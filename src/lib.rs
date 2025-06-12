// SPDX-FileCopyrightText: 2025 Madeline Baggins <declanbaggins@gmail.com>
//
// SPDX-License-Identifier: MIT

use std::{
    borrow::Cow, collections::HashMap, num::{IntErrorKind, ParseIntError}, path::{Path, PathBuf}, str::FromStr
};

#[derive(Clone)]
pub struct Parser<'a> {
    tail: &'a str,
    pub position: Position<'a>,
}

#[derive(Debug, Clone)]
pub struct Position<'a> {
    pub path: &'a Path,
    pub src: &'a str,
    pub line: usize,
    pub char: usize,
}

impl<'a> Position<'a> {
    pub fn error(&self, message: String) -> Error<'a> {
        Error {
            message,
            position: self.clone(),
        }
    }
}

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;

#[derive(Debug)]
pub struct Error<'a> {
    pub message: String,
    pub position: Position<'a>,
}

impl std::fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const RED: &str = "\x1b[1;31m";
        const DEFAULT: &str = "\x1b[1;39m";
        writeln!(
            f,
            "{RED}Error in '{}':{DEFAULT}",
            self.position.path.display()
        )?;
        for (line_num, line) in self.position.src.split('\n').enumerate() {
            writeln!(f, "{line}")?;
            if line_num == self.position.line {
                let offset = std::iter::repeat_n(' ', self.position.char).collect::<String>();
                writeln!(f, "{offset}^")?;
                let offset_len = self.position.char.saturating_sub(self.message.len());
                let offset = std::iter::repeat_n(' ', offset_len).collect::<String>();
                writeln!(f, "{offset}{RED}{}{DEFAULT}", self.message)?;
            }
        }
        Ok(())
    }
}

impl<'a> Parser<'a> {
    pub fn new(path: &'a Path, src: &'a str) -> Self {
        Self {
            tail: src,
            position: Position {
                src,
                path,
                line: 0,
                char: 0,
            },
        }
    }
    pub fn parse<T: Parse<'a>>(&mut self) -> T {
        T::parse(self)
    }
    fn take_whitespace(&mut self) {
        let len = self
            .tail
            .find(|c: char| !c.is_whitespace())
            .unwrap_or(self.tail.len());
        self.take(len);
    }
    fn take_char(&mut self) -> Option<char> {
        let char = self.tail.chars().next()?;
        match char {
            '\n' => {
                self.position.line += 1;
                self.position.char = 0;
            }
            _ => self.position.char += 1,
        }
        (_, self.tail) = self.tail.split_at(char.len_utf8());
        Some(char)
    }
    fn take(&mut self, n: usize) -> &'a str {
        let head;
        (head, self.tail) = self.tail.split_at(n);
        for c in head.chars() {
            match c {
                '\n' => {
                    self.position.line += 1;
                    self.position.char = 0;
                }
                _ => self.position.char += 1,
            }
        }
        head
    }
}

pub trait Parse<'a> {
    fn parse(parser: &mut Parser<'a>) -> Self;
}

#[derive(Debug)]
pub enum Content<'a> {
    Element(Element<'a>),
    Text(String),
}

impl<'a> Parse<'a> for Option<Result<'a, Content<'a>>> {
    fn parse(parser: &mut Parser<'a>) -> Self {
        // Clear any whitespace
        parser.take_whitespace();
        // If the document has finished parsing
        if parser.tail.is_empty() {
            return None;
        };
        // Check if we start with an element
        match parser.parse::<Option<Result<Element>>>() {
            Some(Ok(element)) => return Some(Ok(Content::Element(element))),
            Some(Err(err)) => return Some(Err(err)),
            None => {}
        }
        // Otherwise, get the text
        let len = parser.tail.find('<').unwrap_or(parser.tail.len());
        let text = parser.take(len);
        Some(Ok(Content::Text(text.into())))
    }
}

#[derive(Debug)]
pub struct Element<'a> {
    pub name: &'a str,
    pub attributes: HashMap<&'a str, Attribute<'a>>,
    pub contents: Vec<Content<'a>>,
    pub position: Position<'a>,
}

impl<'a> Element<'a> {
    pub fn attribute<'b, T: Query<'a, 'b>>(&'b self, name: &str) -> Result<'a, T> {
        T::get(name, self)
    }

    pub fn children<'b, 'c, T: FromElement<'a, 'b>>(
        &'b self,
        name: &'c str,
    ) -> impl Iterator<Item = Result<'a, T>> + use<'a, 'b, 'c, T> {
        use Content;
        self.contents
            .iter()
            .filter_map(move |item| match item {
                Content::Element(e) if e.name == name => Some(e),
                _ => None,
            })
            .map(|t| T::from_element(t))
    }
    pub fn child<'b, 'c, T: FromElement<'a, 'b>>(&'b self, name: &'c str) -> Result<'a, T> {
        use Content;
        let mut candidates = self.contents.iter().filter_map(move |item| match item {
            Content::Element(e) if e.name == name => Some(e),
            _ => None,
        });
        let Some(result) = candidates.next() else {
            return Err(self.position.error(format!("expected '{name}' element")));
        };
        if let Some(duplicate) = candidates.next() {
            return Err(duplicate
                .position
                .error(format!("duplicate '{name}' element")));
        }
        T::from_element(result)
    }
    pub fn optional_child<'b, 'c, T: FromElement<'a, 'b>>(
        &'b self,
        name: &'c str,
    ) -> Result<'a, Option<T>> {
        use Content;
        let mut candidates = self.contents.iter().filter_map(move |item| match item {
            Content::Element(e) if e.name == name => Some(e),
            _ => None,
        });
        let Some(result) = candidates.next() else {
            return Ok(None);
        };
        if let Some(duplicate) = candidates.next() {
            return Err(duplicate
                .position
                .error(format!("duplicate '{name}' element")));
        }
        Some(T::from_element(result)).transpose()
    }
}

impl<'a> Parse<'a> for Option<Result<'a, Element<'a>>> {
    fn parse(parser: &mut Parser<'a>) -> Self {
        // Find the opening tag if there is one
        let open_tag = match parser.parse::<Option<Result<OpenTag>>>()? {
            Ok(open_tag) => open_tag,
            Err(err) => return Some(Err(err)),
        };
        // If the tag was self closing, return the entity
        let mut contents = vec![];
        if open_tag.self_closing {
            return Some(Ok(Element {
                name: open_tag.name,
                position: open_tag.position,
                attributes: open_tag.attributes,
                contents,
            }));
        }
        // Parse all the content
        let close_tag = loop {
            // Remove any whitespace
            parser.take_whitespace();
            // Check if there's a closing tag
            if let Some(close_tag) = parser.parse::<Option<Result<CloseTag>>>() {
                break close_tag;
            }
            // Otherwise, try to get content
            match parser.parse::<Option<Result<Content>>>() {
                Some(Err(err)) => return Some(Err(err)),
                Some(Ok(content)) => contents.push(content),
                None => return Some(Err(parser.position.error("missing closing tag".into()))),
            }
        };
        // Ensure we didn't error getting the close tag
        let close_tag = match close_tag {
            Ok(close_tag) => close_tag,
            Err(err) => return Some(Err(err)),
        };
        // Ensure the close and open tags match
        if open_tag.name != close_tag.name {
            return Some(Err(parser.position.error("mismatched closing tag".into())));
        }
        Some(Ok(Element {
            name: open_tag.name,
            attributes: open_tag.attributes,
            contents,
            position: open_tag.position,
        }))
    }
}

/// The name of an element.
/// - Must start with a letter or underscore.
/// - Cannot start with the letters "xml" in any case.
/// - Consists only of letters, digits, hyphens,
///   underscores, and periods.
struct Name<'a>(&'a str);

impl<'a> Parse<'a> for Option<Name<'a>> {
    fn parse(parser: &mut Parser<'a>) -> Self {
        // Ensure tail starts with a letter or underscore
        if !parser
            .tail
            .starts_with(|c: char| c.is_alphabetic() || c == '_')
        {
            return None;
        }
        // Ensure tail doesn't start with 'xml' in any case
        if parser
            .tail
            .get(0..3)
            .is_some_and(|f| f.to_lowercase() == "xml")
        {
            return None;
        }
        // Find the head of the tail that only consists of
        // digits, hyphens, underscores, and periods.
        let len = parser
            .tail
            .find(|c: char| !c.is_ascii_alphanumeric() && !['.', '_', '-'].contains(&c))
            .unwrap_or(parser.tail.len());
        let name = parser.tail.get(..len).unwrap();
        (!name.is_empty()).then_some(Name(parser.take(len)))
    }
}

struct OpenTag<'a> {
    name: &'a str,
    attributes: HashMap<&'a str, Attribute<'a>>,
    self_closing: bool,
    position: Position<'a>,
}

impl<'a> Parse<'a> for Option<Result<'a, OpenTag<'a>>> {
    fn parse(parser: &mut Parser<'a>) -> Self {
        // Ensure we're parsing an open tag
        if !parser.tail.starts_with('<') {
            return None;
        }
        // Skip over the opening chevron
        parser.take(1);
        // Get the element's name
        let Some(Name(name)) = parser.parse::<Option<Name>>() else {
            return Some(Err(parser.position.error("expected element name".into())));
        };
        // Skip any whitespace
        parser.take_whitespace();
        // Parse any attributes
        let mut attributes = HashMap::new();
        while let Some(attribute) = parser.parse::<Option<Result<Attribute>>>() {
            match attribute {
                Ok(attribute) => {
                    if let Some(old) = attributes.insert(attribute.name, attribute) {
                        let duplicate = attributes.get(old.name).unwrap();
                        return Some(Err(duplicate
                            .position
                            .error(format!("found duplicate '{}' attribute", old.name))));
                    }
                }
                Err(e) => return Some(Err(e)),
            }
            parser.take_whitespace();
        }
        // Ensure the opening tag ends with '/>' or '>'.
        let self_closing = parser.tail.starts_with("/>");
        if !self_closing && !parser.tail.starts_with(">") {
            return Some(Err(parser.position.error("expected '>' or '/>'".into())));
        }
        // Skip the ending bit
        if self_closing {
            parser.take("/>".len());
        } else {
            parser.take(">".len());
        }
        // Build the opening tag
        Some(Ok(OpenTag {
            name,
            attributes,
            self_closing,
            position: parser.position.clone(),
        }))
    }
}

#[derive(Debug)]
pub struct Attribute<'a> {
    pub name: &'a str,
    pub value: Option<String>,
    pub position: Position<'a>,
}

impl<'a> Parse<'a> for Option<Result<'a, Attribute<'a>>> {
    fn parse(parser: &mut Parser<'a>) -> Self {
        // Clone the parser in case we need to restore it
        let backup = parser.clone();
        // Get the name of the attribute
        let Some(Name(name)) = parser.parse::<Option<Name>>() else {
            *parser = backup;
            return None;
        };
        // If there's no value to the attribute, finish
        // parsing.
        if !parser.tail.starts_with('=') {
            return Some(Ok(Attribute {
                name,
                value: None,
                position: parser.position.clone(),
            }));
        }
        // Skip the '='
        parser.take(1);
        // Parse the value of the attribute
        let Some(AttributeValue(value)) = parser.parse::<Option<AttributeValue>>() else {
            return Some(Err(parser
                .position
                .error("expected attribute value".into())));
        };
        Some(Ok(Attribute {
            name,
            value: Some(value),
            position: parser.position.clone(),
        }))
    }
}

struct AttributeValue(String);

impl Parse<'_> for Option<AttributeValue> {
    fn parse(parser: &mut Parser) -> Self {
        // Ensure the parser starts with a single or double
        // quote.
        let quote = match parser.tail.chars().next()? {
            c @ ('"' | '\'') => c,
            _ => return None,
        };
        // Create a working copy of the parser
        let mut working = parser.clone();
        working.take(1);
        // Build out the string
        // TODO: Add support for character entities
        let mut value = String::new();
        loop {
            let next = working.take_char()?;
            match next {
                '\\' => match working.take_char()? {
                    c @ ('\\' | '\'' | '"') => value.push(c),
                    _ => return None,
                },
                c if c == quote => break,
                c => value.push(c),
            }
        }
        // Save the working copy of the parser
        *parser = working;
        Some(AttributeValue(value))
    }
}

struct CloseTag<'a> {
    name: &'a str,
}

impl<'a> Parse<'a> for Option<Result<'a, CloseTag<'a>>> {
    fn parse(parser: &mut Parser<'a>) -> Self {
        // Ensure we're at the start of a closing tag
        if !parser.tail.starts_with("</") {
            return None;
        }
        parser.take("</".len());
        // Get the name of the closing tag
        let Some(Name(name)) = parser.parse::<Option<Name>>() else {
            return Some(Err(parser.position.error("expected element name".into())));
        };
        // Ensure we end with a '>'.
        if !parser.tail.starts_with('>') {
            return Some(Err(parser.position.error("expected '>'".into())));
        }
        // Skip the '>'.
        parser.take(">".len());
        Some(Ok(CloseTag { name }))
    }
}

pub trait FromValue<'a, 'b>: Sized {
    fn from_value(value: &'b str, position: &'b Position<'a>) -> Result<'a, Self>;
}

impl<'a, 'b> FromValue<'a, 'b> for Cow<'b, str> {
    fn from_value(value: &'b str, _position: &'b Position<'a>) -> Result<'a, Self> {
        Ok(Cow::Borrowed(value))
    }
}

impl<'a, 'b> FromValue<'a, 'b> for &'b str {
    fn from_value(value: &'b str, _position: &'b Position<'a>) -> Result<'a, Self> {
        Ok(value)
    }
}

impl<'a, 'b> FromValue<'a, 'b> for &'b Path {
    fn from_value(value: &'b str, _position: &'b Position<'a>) -> Result<'a, Self> {
        Ok(value.as_ref())
    }
}

impl<'a, 'b> FromValue<'a, 'b> for String {
    fn from_value(value: &'b str, _position: &'b Position<'a>) -> Result<'a, Self> {
        Ok(value.into())
    }
}

impl<'a, 'b> FromValue<'a, 'b> for PathBuf {
    fn from_value(value: &'b str, _position: &'b Position<'a>) -> Result<'a, Self> {
        Ok(PathBuf::from(value))
    }
}

pub trait FromNumeric: FromStr<Err = ParseIntError> {}

impl FromNumeric for u8 {}

impl FromNumeric for u16 {}

impl FromNumeric for u32 {}

impl FromNumeric for u64 {}

impl FromNumeric for u128 {}

impl FromNumeric for usize {}

impl FromNumeric for i8 {}

impl FromNumeric for i16 {}

impl FromNumeric for i32 {}

impl FromNumeric for i64 {}

impl FromNumeric for i128 {}

impl FromNumeric for isize {}

impl<'a, 'b, T> FromValue<'a, 'b> for T
where
    T: FromNumeric,
{
    fn from_value(value: &'b str, position: &'b Position<'a>) -> Result<'a, Self> {
        value.parse::<T>().map_err(|e| {
            let msg = match e.kind() {
                IntErrorKind::Empty => "failed to parse integer from empty string",
                IntErrorKind::InvalidDigit => "value contains invalid digit",
                IntErrorKind::PosOverflow => "value too large for this attribute",
                IntErrorKind::NegOverflow => "value too small for this attribute",
                IntErrorKind::Zero => "value cannot be zero for this attribute",
                _ => "unknown integer parse error",
            }
            .into();
            position.error(msg)
        })
    }
}

pub trait FromAttribute<'a, 'b>: Sized {
    fn from_attribute(attribute: &'b Attribute<'a>) -> Result<'a, Self>;
}

impl<'a, 'b, T: FromValue<'a, 'b>> FromAttribute<'a, 'b> for T {
    fn from_attribute(attribute: &'b Attribute<'a>) -> Result<'a, Self> {
        let Some(value) = attribute.value.as_ref() else {
            let name = attribute.name;
            return Err(attribute
                .position
                .error(format!("expected non-empty value for '{name}'")));
        };
        T::from_value(value, &attribute.position)
    }
}

pub trait Query<'a, 'b>: Sized {
    fn get(name: &str, element: &'b Element<'a>) -> Result<'a, Self>;
}

impl<'a, 'b, T: FromAttribute<'a, 'b>> Query<'a, 'b> for T {
    fn get(name: &str, element: &'b Element<'a>) -> Result<'a, Self> {
        let Some(attribute) = element.attributes.get(name) else {
            let msg = format!("expected '{name}' attribute");
            return Err(element.position.error(msg));
        };
        T::from_attribute(attribute)
    }
}

impl<'a, 'b, T: FromAttribute<'a, 'b>> Query<'a, 'b> for Option<T> {
    fn get(name: &str, element: &'b Element<'a>) -> Result<'a, Self> {
        element
            .attributes
            .get(name)
            .map(|a| T::from_attribute(a))
            .transpose()
    }
}

impl<'a, 'b> Query<'a, 'b> for bool {
    fn get(name: &str, element: &'b Element<'a>) -> Result<'a, Self> {
        Ok(element.attributes.contains_key(name))
    }
}

pub trait FromElement<'a, 'b>: Sized {
    fn from_element(element: &'b Element<'a>) -> Result<'a, Self>;
}

impl<'a, 'b> FromElement<'a, 'b> for &'b Element<'a> {
    fn from_element(element: &'b Element<'a>) -> Result<'a, Self> {
        Ok(element)
    }
}

impl<'a, 'b, T> FromElement<'a, 'b> for T
where
    T: FromValue<'a, 'b>,
{
    fn from_element(element: &'b Element<'a>) -> Result<'a, Self> {
        match element.contents.as_slice() {
            [Content::Text(value)] => T::from_value(value, &element.position),
            _ => Err(element
                .position
                .error("expected element to contain a single value".into())),
        }
    }
}
