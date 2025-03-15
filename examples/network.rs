use maddi_xml::{Content, Element, FromElement, FromValue, Parser, Result};
use std::{net::Ipv4Addr, path::Path};

/// An example custom type. Here we're adding
/// support for id addresses.
struct IP(Ipv4Addr);

impl<'a, 'b> FromValue<'a, 'b> for IP {
    fn from_value(value: &'b str, position: &'b maddi_xml::Position<'a>) -> Result<'a, Self> {
        let Ok(ip) = value.parse::<Ipv4Addr>() else {
            return Err(position.error("expected an ip address".into()));
        };
        Ok(IP(ip))
    }
}

/// This struct represents the whole configuration file.
#[derive(Debug)]
struct Config {
    servers: Vec<Server>,
}

impl<'a, 'b> FromElement<'a, 'b> for Config {
    fn from_element(element: &'b Element<'a>) -> Result<'a, Self> {
        Ok(Config {
            servers: element.children("server").collect::<Result<_>>()?,
        })
    }
}

/// This represents a theoretical server that we want to
/// list information about in our config.
#[derive(Debug)]
struct Server {
    name: String,
    ip: Ipv4Addr,
    aliases: Vec<Alias>,
}

impl<'a, 'b> FromElement<'a, 'b> for Server {
    fn from_element(element: &'b Element<'a>) -> Result<'a, Self> {
        Ok(Server {
            name: element.attribute("name")?,
            ip: element.attribute::<IP>("ip")?.0,
            aliases: element.children("alias").collect::<Result<Vec<_>>>()?,
        })
    }
}

/// As alias that the server can be referred to by.
#[derive(Debug)]
struct Alias(String);

impl<'a, 'b> FromElement<'a, 'b> for Alias {
    fn from_element(element: &'b Element<'a>) -> Result<'a, Self> {
        match element.contents.as_slice() {
            [] => Err(element.position.error("alias cannot be empty".into())),
            [Content::Text(alias)] => Ok(Alias(alias.clone())),
            _ => Err(element
                .position
                .error("expected a single alias name".into())),
        }
    }
}

fn main() {
    // The configuration we're going to parse
    let config = r#"
        <config>
            <server name="localhost" ip="127.0.0.1">
                <alias>local</alias>
                <alias>me</alias>
            </server>
            <server name="example" ip="10.0.0.101">
                <alias>example.com</alias>
            </server>
        </config>
    "#;
    // The parser state machine we'll use to do the work
    let mut parser = Parser::new(Path::new("example.xml"), config);
    // Parsing a piece of content from the top of the file.
    // Content is either a piece of non-xml text or an xml element.
    match parser.parse::<Option<Result<Content>>>() {
        Some(Ok(content)) => println!("{content:?}"),
        Some(Err(e)) => println!("{e}"),
        None => {
            let error = parser
                .position
                .error("Could not find root config node".into());
            println!("{error}");
        }
    }
}
