mod console_tests;
mod iterator;

use std::borrow::Cow;

use ansi_term::Style;
use itertools::Itertools;
use unicode_segmentation::UnicodeSegmentation;
use unicode_width::UnicodeWidthStr;

pub use iterator::{AnsiElementIterator, Element};

pub const ANSI_CSI_CLEAR_TO_EOL: &str = "\x1b[0K";
pub const ANSI_CSI_CLEAR_TO_BOL: &str = "\x1b[1K";
pub const ANSI_SGR_RESET: &str = "\x1b[0m";
pub const ANSI_SGR_REVERSE: &str = "\x1b[7m";

// Return the text component of `s`, i.e. with all ANSI codes removed. In this library, the term
// "ANSI codes" means any bytes that belong to CSI, OSC, SGR or escape sequence constructs and are
// not part of the text that will be displayed to the user. For example, "ANSI codes" includes color
// escape sequences, OSC8 sequences that are used for terminal hyperlinks, and also the URI part of
// a terminal hyperlink. See https://en.wikipedia.org/wiki/ANSI_escape_code.
pub fn strip_ansi(s: &str) -> String {
    strip_ansi_from_strings_iterator(ansi_strings_iterator(s))
}

enum ExtractOsc8HyperlinkState {
    ExpectOsc8Url,
    ExpectFirstText,
    ExpectMoreTextOrTerminator,
    SeenOneHyperlink,
    WillNotReturnUrl,
}

/// Strip OSC codes from `s`. If `s` is a single OSC8 hyperlink, with no other text, then return
/// (s_with_all_hyperlinks_removed, Some(url)). If `s` does not meet this description, then return
/// (s_with_all_hyperlinks_removed, None). Any ANSI color sequences in `s` will be retained. See
/// https://gist.github.com/egmontkob/eb114294efbcd5adb1944c9f3cb5feda
pub fn strip_osc(s: &str) -> (String, Option<String>) {
    use ExtractOsc8HyperlinkState::*;

    let mut url = None;
    let mut state = ExpectOsc8Url;
    let mut text = String::with_capacity(s.len());

    for el in AnsiElementIterator::new(s) {
        match el {
            Element::Osc(i, j) => match state {
                ExpectOsc8Url => {
                    url = Some(&s[i..j]);
                    state = ExpectFirstText;
                }
                ExpectMoreTextOrTerminator => state = SeenOneHyperlink,
                _ => state = WillNotReturnUrl,
            },
            Element::Sgr(_, i, j) => text.push_str(&s[i..j]),
            Element::Csi(i, j) => text.push_str(&s[i..j]),
            Element::Esc(_, _) => {}
            Element::Text(i, j) => {
                text.push_str(&s[i..j]);
                match state {
                    ExpectFirstText => state = ExpectMoreTextOrTerminator,
                    ExpectMoreTextOrTerminator => {}
                    _ => state = WillNotReturnUrl,
                }
            }
        }
    }

    match state {
        WillNotReturnUrl => (text, None),
        _ => {
            let url = url.and_then(|s| {
                s.strip_prefix("\x1b]8;;")
                    .and_then(|s| s.strip_suffix("\x1b"))
            });
            if let Some(url) = url {
                (text, Some(url.to_string()))
            } else {
                (text, None)
            }
        }
    }
}

enum OscPartitionState {
    BeforeText(Option<usize>),
    InText,
    AfterText,
}

/// If `s` is of the form
/// '<non-text-ansi-prefix><text-with-non-osc-ansi-codes><non-text-ansi-suffix>' then return
/// `Some((ansi_prefix, text_with_non_osc_ansi_codes, ansi_suffix))`, otherwise return None. Any of
/// the 3 substrings may be empty. If `s` contains no text, then return `Some(("", "", s))`. If `s`
/// contains more than one text section, then return None. The second element of the returned
/// structure (`text_with_non_osc_ansi_codes`) greedily captures non-OSC ANSI content before and
/// after it. This function can be used to extract a hyperlink when the link text itself is colored.
pub fn osc_partition(s: &str) -> Option<(&str, &str, &str)> {
    use OscPartitionState::*;
    let mut state = BeforeText(Some(0));
    let (mut text_start, mut text_end) = (0, 0);
    for el in AnsiElementIterator::new(s) {
        match el {
            Element::Text(i, j) => {
                match state {
                    BeforeText(last_non_osc_start) => {
                        state = InText;
                        text_start = last_non_osc_start.unwrap_or(i);
                    }
                    InText => {}
                    AfterText => return None,
                }
                text_end = j;
            }
            Element::Sgr(_, i, j) => match state {
                BeforeText(None) => {
                    // Start accumulating some non-OSC content to potentially be prepended to the
                    // returned text section.
                    state = BeforeText(Some(i))
                }
                InText => {
                    // Extend the end of the text so that adjacent non-OSC content is appended to
                    // the returned text section.
                    text_end = j;
                }
                _ => {}
            },
            Element::Csi(i, j) => match state {
                BeforeText(None) => state = BeforeText(Some(i)),
                InText => text_end = j,
                _ => {}
            },
            Element::Osc(i, _j) => match state {
                BeforeText(Some(_)) => {
                    // We had accumulated some non-OSC/ESC content to potentially be prepended to
                    // the returned text section, but in fact it must not be, because there is
                    // intervening OSC/ESC content.
                    state = BeforeText(None);
                }
                InText => {
                    // OSC/ESC marks the end of the text section.
                    text_end = i;
                    state = AfterText;
                }
                _ => {}
            },
            Element::Esc(i, _j) => match state {
                BeforeText(Some(_)) => {
                    // We had accumulated some non-OSC/ESC content to potentially be prepended to
                    // the returned text section, but in fact it must not be, because there is
                    // intervening OSC/ESC content.
                    state = BeforeText(None);
                }
                InText => {
                    // OSC/ESC marks the end of the text section.
                    text_end = i;
                    state = AfterText;
                }
                _ => {}
            },
        }
    }
    Some((&s[..text_start], &s[text_start..text_end], &s[text_end..]))
}

pub fn measure_text_width(s: &str) -> usize {
    // TODO: how should e.g. '\n' be handled?
    strip_ansi(s).width()
}

/// Truncate string such that `tail` is present as a suffix, preceded by as much of `s` as can be
/// displayed in the requested width.
// Return string constructed as follows:
// 1. `display_width` characters are available. If the string fits, return it.
//
// 2. Contribute graphemes and ANSI escape sequences from `tail` until either (1) `tail` is
//    exhausted, or (2) the display width of the result would exceed `display_width`.
//
// 3. If tail was exhausted, then contribute graphemes and ANSI escape sequences from `s` until the
//    display_width of the result would exceed `display_width`.
pub fn truncate_str<'a, 'b>(s: &'a str, display_width: usize, tail: &'b str) -> Cow<'a, str> {
    let items = ansi_strings_iterator(s).collect::<Vec<(&str, bool)>>();
    let width = strip_ansi_from_strings_iterator(items.iter().copied()).width();
    if width <= display_width {
        return Cow::from(s);
    }
    let result_tail = if !tail.is_empty() {
        truncate_str(tail, display_width, "").to_string()
    } else {
        String::new()
    };
    let mut used = measure_text_width(&result_tail);
    let mut result = String::new();
    for (t, is_ansi) in items {
        if !is_ansi {
            for g in t.graphemes(true) {
                let w = g.width();
                if used + w > display_width {
                    break;
                }
                result.push_str(g);
                used += w;
            }
        } else {
            result.push_str(t);
        }
    }

    Cow::from(format!("{}{}", result, result_tail))
}

pub fn parse_style_sections(s: &str) -> Vec<(ansi_term::Style, &str)> {
    let mut sections = Vec::new();
    let mut curr_style = Style::default();
    for element in AnsiElementIterator::new(s) {
        match element {
            Element::Text(start, end) => sections.push((curr_style, &s[start..end])),
            Element::Sgr(style, _, _) => curr_style = style,
            _ => {}
        }
    }
    sections
}

// Return the first CSI element, if any, as an `ansi_term::Style`.
pub fn parse_first_style(s: &str) -> Option<ansi_term::Style> {
    AnsiElementIterator::new(s).find_map(|el| match el {
        Element::Sgr(style, _, _) => Some(style),
        _ => None,
    })
}

pub fn string_starts_with_ansi_style_sequence(s: &str) -> bool {
    AnsiElementIterator::new(s)
        .next()
        .map(|el| matches!(el, Element::Sgr(_, _, _)))
        .unwrap_or(false)
}

/// Return string formed from a byte slice starting at byte position `start`, where the index
/// counts bytes in non-ANSI-escape-sequence content only. All ANSI escape sequences in the
/// original string are preserved.
pub fn ansi_preserving_slice(s: &str, start: usize) -> String {
    AnsiElementIterator::new(s)
        .scan(0, |index, element| {
            // `index` is the index in non-ANSI-escape-sequence content.
            Some(match element {
                Element::Sgr(_, a, b) => &s[a..b],
                Element::Csi(a, b) => &s[a..b],
                Element::Esc(a, b) => &s[a..b],
                Element::Osc(a, b) => &s[a..b],
                Element::Text(a, b) => {
                    let i = *index;
                    *index += b - a;
                    if *index <= start {
                        // This text segment ends before start, so contributes no bytes.
                        ""
                    } else if i > start {
                        // This section starts after `start`, so contributes all its bytes.
                        &s[a..b]
                    } else {
                        // This section contributes those bytes that are >= start
                        &s[(a + start - i)..b]
                    }
                }
            })
        })
        .join("")
}

/// Return the byte index in `s` of the i-th text byte in `s`. I.e. `i` counts
/// bytes in non-ANSI-escape-sequence content only.
pub fn ansi_preserving_index(s: &str, i: usize) -> Option<usize> {
    let mut index = 0;
    for element in AnsiElementIterator::new(s) {
        if let Element::Text(a, b) = element {
            index += b - a;
            if index > i {
                return Some(b - (index - i));
            }
        }
    }
    None
}

fn ansi_strings_iterator(s: &str) -> impl Iterator<Item = (&str, bool)> {
    AnsiElementIterator::new(s).map(move |el| match el {
        Element::Sgr(_, i, j) => (&s[i..j], true),
        Element::Csi(i, j) => (&s[i..j], true),
        Element::Esc(i, j) => (&s[i..j], true),
        Element::Osc(i, j) => (&s[i..j], true),
        Element::Text(i, j) => (&s[i..j], false),
    })
}

fn strip_ansi_from_strings_iterator<'a>(strings: impl Iterator<Item = (&'a str, bool)>) -> String {
    strings
        .filter_map(|(el, is_ansi)| if !is_ansi { Some(el) } else { None })
        .join("")
}

#[cfg(test)]
mod tests {
    // Note that src/ansi/console_tests.rs contains additional test coverage for this module.
    use super::*;

    const HTTP_URL: &str = "http://example.com";
    const HTTPS_URL: &str = "https://example.com/whatever?this=that&x=y";
    const FILE_URL: &str = "file:///Users/dan/src/delta/src/ansi/mod.rs";
    const COLORED_NON_ASCII_TEXT: &str = "\x1b[31mバー\x1b[0m";
    const COLORED_HYPERLINK: &str = "\x1b[38;5;4m\x1b]8;;file:///Users/dan/src/delta/src/ansi/mod.rs\x1b\\src/ansi/mod.rs\x1b]8;;\x1b\\\x1b[0m\n";
    const COLORED_HYPERLINK_WITH_COLORED_FIRST_CHAR_OF_TEXT: &str = "\x1b[38;5;4m\x1b]8;;file:///Users/dan/src/delta/src/ansi/mod.rs\x1b\\\x1b[38;5;4msrc[0m/ansi/mod.rs\x1b]8;;\x1b\\\x1b[0m\n";
    const MULTICOLORED_TEXT: &str =
        "\x1b[30mfoo\x1b[0m\x1b[31mbar\x1b[0m\x1b[32mbaz\x1b[0m\x1b[33mqux\x1b[0m";

    fn format_osc8_hyperlink(url: &str, text: &str) -> String {
        format!(
            "{osc}8;;{url}{st}{text}{osc}8;;{st}",
            url = url,
            text = text,
            osc = "\x1b]",
            st = "\x1b\\"
        )
    }

    #[test]
    fn test_strip_ansi() {
        for s in &["src/ansi/mod.rs", "バー", "src/ansi/modバー.rs"] {
            assert_eq!(strip_ansi(s), *s);
        }
        assert_eq!(strip_ansi("\x1b[31mバー\x1b[0m"), "バー");
    }

    #[test]
    fn test_strip_osc() {
        assert_eq!(
            strip_osc(&format_osc8_hyperlink(HTTP_URL, "This is a link")),
            ("This is a link".to_string(), Some(HTTP_URL.to_string()))
        );
        assert_eq!(
            strip_osc(&format_osc8_hyperlink(HTTPS_URL, "This is a link")),
            ("This is a link".to_string(), Some(HTTPS_URL.to_string()))
        );
        assert_eq!(
            strip_osc(COLORED_HYPERLINK.strip_suffix("\n").unwrap()),
            (
                "\x1b[38;5;4msrc/ansi/mod.rs\x1b[0m".into(),
                Some(FILE_URL.into())
            )
        );
        assert_eq!(
            strip_osc(&format_osc8_hyperlink(FILE_URL, MULTICOLORED_TEXT)),
            (MULTICOLORED_TEXT.to_string(), Some(FILE_URL.to_string()))
        );
        assert_eq!(
            strip_osc(&format!(
                "{}{}",
                format_osc8_hyperlink(HTTP_URL, "This is a link"),
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            ("This is a linkThis is a link".to_string(), None)
        );
        assert_eq!(
            strip_osc(&format!(
                "{}{}",
                COLORED_HYPERLINK.strip_suffix("\n").unwrap(),
                COLORED_HYPERLINK.strip_suffix("\n").unwrap()
            )),
            (
                "\x1b[38;5;4msrc/ansi/mod.rs\x1b[0m\x1b[38;5;4msrc/ansi/mod.rs\x1b[0m".to_string(),
                None
            )
        )
    }

    #[test]
    fn test_strip_osc_invalid_input() {
        assert_eq!(strip_osc(""), ("".to_string(), None));
        assert_eq!(strip_osc("a"), ("a".to_string(), None));
        assert_eq!(
            strip_osc(&format!(
                "{}X",
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            ("This is a linkX".to_string(), None)
        );
        assert_eq!(
            strip_osc(&format!(
                "{} ",
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            ("This is a link ".to_string(), None)
        );
        assert_eq!(
            strip_osc(&format!(
                "X{}",
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            ("XThis is a link".to_string(), None)
        );
        assert_eq!(
            strip_osc(&format!(
                " {}",
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            (" This is a link".to_string(), None)
        );
        assert_eq!(
            strip_osc(&format!(
                "{}{}",
                format_osc8_hyperlink(HTTP_URL, "This is a link"),
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            ("This is a linkThis is a link".to_string(), None)
        );
        assert_eq!(
            strip_osc(&format!(
                "{}XXX{}",
                format_osc8_hyperlink(HTTP_URL, "This is a link"),
                format_osc8_hyperlink(HTTP_URL, "This is a link")
            )),
            ("This is a linkXXXThis is a link".to_string(), None)
        );
    }

    #[test]
    fn test_osc_partition() {
        for (input, expected) in [
            ("", Some(("", "", ""))),
            ("a", Some(("", "a", ""))),
            ("ab", Some(("", "ab", ""))),
            ("a\nb\n", Some(("", "a\nb\n", ""))),
            ("バー", Some(("", "バー", ""))),
            (
                COLORED_NON_ASCII_TEXT,
                Some(("", COLORED_NON_ASCII_TEXT, "")),
            ),
            (
                &format!("{}{}", COLORED_NON_ASCII_TEXT, COLORED_NON_ASCII_TEXT),
                Some((
                    "",
                    &format!("{}{}", COLORED_NON_ASCII_TEXT, COLORED_NON_ASCII_TEXT),
                    "",
                )),
            ),
            (
                &format_osc8_hyperlink(HTTP_URL, "This is a link"),
                Some((
                    &format!("\x1b]8;;{}\x1b\\", HTTP_URL),
                    "This is a link",
                    "\x1b]8;;\x1b\\",
                )),
            ),
            (
                COLORED_HYPERLINK.strip_suffix("\n").unwrap(),
                Some((
                    "\x1b[38;5;4m\x1b]8;;file:///Users/dan/src/delta/src/ansi/mod.rs\x1b\\",
                    "src/ansi/mod.rs",
                    "\x1b]8;;\x1b\\\x1b[0m",
                )),
            ),
            (COLORED_HYPERLINK, None), // it has a trailing newline
            ("\x1b[38;5;4m\x1b[0m", Some(("", "", "\x1b[38;5;4m\x1b[0m"))),
            (
                "\x1b[38;5;4m____\x1b[0m\x1b[38;5;4m____\x1b[0m",
                Some(("", "\x1b[38;5;4m____\x1b[0m\x1b[38;5;4m____\x1b[0m", "")),
            ),
            (
                COLORED_HYPERLINK_WITH_COLORED_FIRST_CHAR_OF_TEXT
                    .strip_suffix("\n")
                    .unwrap(),
                Some((
                    "\x1b[38;5;4m\x1b]8;;file:///Users/dan/src/delta/src/ansi/mod.rs\x1b\\",
                    "\x1b[38;5;4msrc[0m/ansi/mod.rs",
                    "\x1b]8;;\x1b\\\x1b[0m",
                )),
            ),
            (
                &format!(
                    "{}{}",
                    format_osc8_hyperlink(HTTP_URL, "This is a link"),
                    format_osc8_hyperlink(HTTP_URL, "This is a link")
                ),
                None,
            ),
            (
                &format!(
                    "{}{}",
                    COLORED_HYPERLINK.strip_suffix("\n").unwrap(),
                    COLORED_HYPERLINK.strip_suffix("\n").unwrap()
                ),
                None,
            ),
            (
                &format!(
                    "text before {} text after",
                    format_osc8_hyperlink(HTTP_URL, "This is a link")
                ),
                None,
            ),
        ] {
            assert_eq!(osc_partition(input), expected)
        }
    }

    #[test]
    fn test_measure_text_width() {
        assert_eq!(measure_text_width("src/ansi/mod.rs"), 15);
        assert_eq!(measure_text_width("バー"), 4);
        assert_eq!(measure_text_width("src/ansi/modバー.rs"), 19);
        assert_eq!(measure_text_width("\x1b[31mバー\x1b[0m"), 4);
        assert_eq!(measure_text_width("a\nb\n"), 2);
    }

    #[test]
    fn test_strip_ansi_osc_hyperlink() {
        assert_eq!(
            strip_ansi(&format_osc8_hyperlink(HTTP_URL, "This is a link")),
            "This is a link",
        );
        assert_eq!(strip_ansi(COLORED_HYPERLINK), "src/ansi/mod.rs\n");
    }

    #[test]
    fn test_measure_text_width_osc_hyperlink() {
        assert_eq!(
            measure_text_width(COLORED_HYPERLINK),
            measure_text_width("src/ansi/mod.rs")
        );
    }

    #[test]
    fn test_measure_text_width_osc_hyperlink_non_ascii() {
        assert_eq!(measure_text_width("\x1b[38;5;4m\x1b]8;;file:///Users/dan/src/delta/src/ansi/mod.rs\x1b\\src/ansi/modバー.rs\x1b]8;;\x1b\\\x1b[0m"),
                   measure_text_width("src/ansi/modバー.rs"));
    }

    #[test]
    fn test_parse_first_style() {
        let minus_line_from_unconfigured_git = "\x1b[31m-____\x1b[m\n";
        let style = parse_first_style(minus_line_from_unconfigured_git);
        let expected_style = ansi_term::Style {
            foreground: Some(ansi_term::Color::Red),
            ..ansi_term::Style::default()
        };
        assert_eq!(Some(expected_style), style);
    }

    #[test]
    fn test_string_starts_with_ansi_escape_sequence() {
        assert!(!string_starts_with_ansi_style_sequence(""));
        assert!(!string_starts_with_ansi_style_sequence("-"));
        assert!(string_starts_with_ansi_style_sequence(
            "\x1b[31m-XXX\x1b[m\n"
        ));
        assert!(string_starts_with_ansi_style_sequence("\x1b[32m+XXX"));
    }

    #[test]
    fn test_ansi_preserving_slice_and_index() {
        assert_eq!(ansi_preserving_slice("", 0), "");
        assert_eq!(ansi_preserving_index("", 0), None);

        assert_eq!(ansi_preserving_slice("0", 0), "0");
        assert_eq!(ansi_preserving_index("0", 0), Some(0));

        assert_eq!(ansi_preserving_slice("0", 1), "");
        assert_eq!(ansi_preserving_index("0", 1), None);

        let raw_string = "\x1b[1;35m0123456789\x1b[0m";
        assert_eq!(
            ansi_preserving_slice(raw_string, 1),
            "\x1b[1;35m123456789\x1b[0m"
        );
        assert_eq!(ansi_preserving_slice(raw_string, 7), "\x1b[1;35m789\x1b[0m");
        assert_eq!(ansi_preserving_index(raw_string, 0), Some(7));
        assert_eq!(ansi_preserving_index(raw_string, 1), Some(8));
        assert_eq!(ansi_preserving_index(raw_string, 7), Some(14));

        let raw_string = "\x1b[1;36m0\x1b[m\x1b[1;36m123456789\x1b[m\n";
        assert_eq!(
            ansi_preserving_slice(raw_string, 1),
            "\x1b[1;36m\x1b[m\x1b[1;36m123456789\x1b[m\n"
        );
        assert_eq!(ansi_preserving_index(raw_string, 0), Some(7));
        assert_eq!(ansi_preserving_index(raw_string, 1), Some(18));
        assert_eq!(ansi_preserving_index(raw_string, 7), Some(24));

        let raw_string = "\x1b[1;36m012345\x1b[m\x1b[1;36m6789\x1b[m\n";
        assert_eq!(
            ansi_preserving_slice(raw_string, 3),
            "\x1b[1;36m345\x1b[m\x1b[1;36m6789\x1b[m\n"
        );
        assert_eq!(ansi_preserving_index(raw_string, 0), Some(7));
        assert_eq!(ansi_preserving_index(raw_string, 1), Some(8));
        assert_eq!(ansi_preserving_index(raw_string, 7), Some(24));
    }

    #[test]
    fn test_truncate_str() {
        assert_eq!(truncate_str("1", 1, ""), "1");
        assert_eq!(truncate_str("12", 1, ""), "1");
        assert_eq!(truncate_str("123", 2, "s"), "1s");
        assert_eq!(truncate_str("123", 2, "→"), "1→");
        assert_eq!(truncate_str("12ݶ", 1, "ݶ"), "ݶ");
    }
}
