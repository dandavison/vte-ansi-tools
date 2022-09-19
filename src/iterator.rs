use core::str::Bytes;
use vte::Params;

pub struct AnsiElementIterator<'a> {
    // The input bytes
    bytes: Bytes<'a>,

    // The state machine
    machine: vte::Parser,

    // Becomes non-None when the parser finishes parsing an ANSI sequence.
    // This is never Element::Text.
    element: Option<Element>,

    // Number of text bytes seen since the last element was emitted.
    text_length: usize,

    // Byte offset of start of current element.
    start: usize,

    // Byte offset of most rightward byte processed so far
    pos: usize,
}

#[derive(Default)]
struct Performer {
    // Becomes non-None when the parser finishes parsing an ANSI sequence.
    // This is never Element::Text.
    element: Option<Element>,

    // Number of text bytes seen since the last element was emitted.
    text_length: usize,
}

#[derive(Debug)]
pub enum Element {
    // TODO: capture SGR Params. Delta captures these as an ansi_term::Style struct.
    // https://github.com/dandavison/delta/blob/1193d54d5c90ab3a45048de3fd1e95c7c2580014/src/ansi/iterator.rs#L136-L137
    // However, the ansi_term crate is unmaintained.
    Sgr(usize, usize),
    Csi(usize, usize),
    Esc(usize, usize),
    Osc(usize, usize),
    Text(usize, usize),
}

impl Element {
    fn set_range(&mut self, start: usize, end: usize) {
        let (from, to) = match self {
            Element::Sgr(from, to) => (from, to),
            Element::Csi(from, to) => (from, to),
            Element::Esc(from, to) => (from, to),
            Element::Osc(from, to) => (from, to),
            Element::Text(from, to) => (from, to),
        };

        *from = start;
        *to = end;
    }
}

impl<'a> AnsiElementIterator<'a> {
    pub fn new(s: &'a str) -> Self {
        Self {
            machine: vte::Parser::new(),
            bytes: s.bytes(),
            element: None,
            text_length: 0,
            start: 0,
            pos: 0,
        }
    }

    fn advance_vte(&mut self, byte: u8) {
        let mut performer = Performer::default();
        self.machine.advance(&mut performer, byte);
        self.element = performer.element;
        self.text_length += performer.text_length;
        self.pos += 1;
    }
}

impl<'a> Iterator for AnsiElementIterator<'a> {
    type Item = Element;

    fn next(&mut self) -> Option<Element> {
        // If the last element emitted was text, then there may be a non-text element waiting
        // to be emitted. In that case we do not consume a new byte.
        while self.element.is_none() {
            match self.bytes.next() {
                Some(b) => self.advance_vte(b),
                None => break,
            }
        }

        if let Some(mut element) = self.element.take() {
            // There is a non-text element waiting to be emitted, but it may have preceding
            // text, which must be emitted first.
            if self.text_length > 0 {
                let start = self.start;
                self.start += self.text_length;
                self.text_length = 0;
                self.element = Some(element);
                return Some(Element::Text(start, self.start));
            }

            let start = self.start;
            self.start = self.pos;
            element.set_range(start, self.pos);

            return Some(element);
        }

        if self.text_length > 0 {
            self.text_length = 0;
            return Some(Element::Text(self.start, self.pos));
        }

        None
    }
}

// Based on https://github.com/alacritty/vte/blob/v0.9.0/examples/parselog.rs
impl vte::Perform for Performer {
    fn csi_dispatch(&mut self, params: &Params, intermediates: &[u8], ignore: bool, c: char) {
        if ignore || intermediates.len() > 1 {
            return;
        }

        let is_sgr = c == 'm' && intermediates.first().is_none();
        let element = if is_sgr {
            if params.is_empty() {
                // Attr::Reset
                // Probably doesn't need to be handled: https://github.com/dandavison/delta/pull/431#discussion_r536883568
                None
            } else {
                Some(Element::Sgr(0, 0))
            }
        } else {
            Some(Element::Csi(0, 0))
        };

        self.element = element;
    }

    fn print(&mut self, c: char) {
        self.text_length += c.len_utf8();
    }

    fn execute(&mut self, byte: u8) {
        // E.g. '\n'
        if byte < 128 {
            self.text_length += 1;
        }
    }

    fn hook(&mut self, _params: &Params, _intermediates: &[u8], _ignore: bool, _c: char) {}

    fn put(&mut self, _byte: u8) {}

    fn unhook(&mut self) {}

    fn osc_dispatch(&mut self, _params: &[&[u8]], _bell_terminated: bool) {
        self.element = Some(Element::Osc(0, 0));
    }

    fn esc_dispatch(&mut self, _intermediates: &[u8], _ignore: bool, _byte: u8) {
        self.element = Some(Element::Esc(0, 0));
    }
}
