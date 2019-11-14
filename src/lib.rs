//! This crate provides a simple generic implementation of the [oEmbed
//! specification][1] version 1.0.
//!
//! No HTTP client mechanism is included. Users of this library must
//! provide an implementation of the `FetchUrl` trait, which
//! `oembed::fetch` will use to retrieve server responses.
//!
//! # Examples
//!
//! ```
//! use oembed::FetchUrl;
//!
//! struct DummyFetchUrl {}
//!
//! impl FetchUrl for DummyFetchUrl {
//!     type Error = std::io::Error;
//!
//!     fn fetch_url(&self, _url: &str) -> Result<Vec<u8>, Self::Error> {
//!         Ok("{
//!             \"version\": \"1.0\",
//!             \"type\": \"photo\",
//!             \"width\": 240,
//!             \"height\": 160,
//!             \"title\": \"ZB8T0193\",
//!             \"url\": \"http://farm4.static.flickr.com/3123/2341623661_7c99f48bbf_m.jpg\",
//!             \"author_name\": \"Bees\",
//!             \"author_url\": \"http://www.flickr.com/photos/bees/\",
//!             \"provider_name\": \"Flickr\",
//!             \"provider_url\": \"http://www.flickr.com/\"
//!         }".as_bytes().to_owned())
//!     }
//! }
//!
//! let fetch_url = DummyFetchUrl {};
//! let endpoints = oembed::Schema::load();
//!
//! let some_url = "http://www.flickr.com/photos/bees/2341623661/";
//!
//! let response = oembed::fetch(fetch_url, &endpoints, some_url)
//!     .expect("Missing provider")
//!     .expect("Failed to fetch server response");
//!
//! assert_eq!("ZB8T0193", response.title.unwrap());
//! ```
//!
//! [1]: https://oembed.com/

#[macro_use]
extern crate serde;
extern crate serde_json;

use std::sync::Arc;

#[derive(Deserialize, Debug)]
pub struct Provider {
    pub provider_name : String,
    pub provider_url  : String,
    pub endpoints     : Vec<Arc<Endpoint>>
}

/// Maps one or more URL schemes to an API endpoint.
#[derive(Deserialize, Debug)]
pub struct Endpoint {
    pub url       : String,
    pub schemes   : Option<Vec<String>>,
    pub formats   : Option<Vec<String>>,
    pub discovery : Option<bool>
}

/// Type-specific oEmbed response data.
///
/// See section 2.3.4 of the [oEmbed specification][1].
///
/// [1]: https://oembed.com/
#[derive(Deserialize, Debug)]
#[serde(tag = "type", rename_all(deserialize = "lowercase"))]
pub enum ResponseType {
    Photo {url:  String, width: Option<i32>, height: Option<i32>},
    Video {html: String, width: Option<i32>, height: Option<i32>},
    Rich  {html: String, width: Option<i32>, height: Option<i32>},
    Link
}

/// Server response to an oEmbed request.
///
/// See section 2.3.4 of the [oEmbed specification][1].
///
/// [1]: https://oembed.com/
#[derive(Deserialize, Debug)]
pub struct Response {
    #[serde(flatten, rename(deserialize = "type"))]
    pub response_type    : ResponseType,
    pub version          : String,
    pub title            : Option<String>,
    pub author_name      : Option<String>,
    pub author_url       : Option<String>,
    pub provider_name    : Option<String>,
    pub provider_url     : Option<String>,
    pub cache_age        : Option<String>,
    pub thumbnail_url    : Option<String>,
    pub thumbnail_width  : Option<i32>,
    pub thumbnail_height : Option<i32>,
}

/// Schema containing known oEmbed providers and their endpoints.
///
/// The number of endpoints is currently quite small (~400
/// endpoints). For this reason, they are stored in a standard `Vec`
/// and looked up with a linear scan of the list.
pub struct Schema {
    endpoints: Vec<(Arc<Endpoint>, Arc<Provider>)>
}

impl Schema {
    /// Load providers from the included schema file.
    ///
    /// # Note
    ///
    /// Schema data is loaded from
    /// `src/resources/providers.json`. This file is included at build
    /// time, so your copy may either currently or eventually be out
    /// of date.
    pub fn load() -> Self {
        let json = include_str!("resources/providers.json");

        let providers: Vec<Arc<Provider>> = serde_json::from_str(&json)
            .expect("Failed to load providers.json -- this should never happen");

        let mut endpoints = vec![];

        for provider in providers.iter() {
            for endpoint in provider.endpoints.iter() {
                endpoints.push((endpoint.clone(), provider.clone()));
            }
        }

        Self { endpoints }
    }

    /// Find an endpoint with a scheme that matches `url`.
    pub fn find_endpoint(&self, url: &str) -> Option<(Arc<Endpoint>, Arc<Provider>)> {
        self.endpoints
            .iter()
            .filter(|(endpoint, _provider)| endpoint.has_matching_scheme(url))
            .map(|(endpoint, provider)| (endpoint.clone(), provider.clone()))
            .next()
    }
}

/// Retrieval of resources by their URL.
///
/// An implementation of this trait is required to use `fetch`.
pub trait FetchUrl {
    type Error: std::error::Error;

    /// Retrieve the body of a resource located at `url`.
    fn fetch_url(&self, url: &str) -> Result<Vec<u8>, Self::Error>;
}

/// Fetch an oEmbed response for `url`.
///
/// Returns `None` if no endpoint with a scheme matching `url` is
/// found.
pub fn fetch<FetchUrlImpl>(
    fetch_url : FetchUrlImpl,
    schema    : &Schema,
    url       : &str
) -> Option<Result<Response, String>> where
    FetchUrlImpl: FetchUrl
{
    schema
        .find_endpoint(url)
        .map(|(endpoint, _provider)| fetch_from(fetch_url, &endpoint, url))
}

/// Fetch an oEmbed response for `url` from the specified `endpoint`.
pub fn fetch_from<FetchUrlImpl>(
    fetch_url : FetchUrlImpl,
    endpoint  : &Endpoint,
    url       : &str
) -> Result<Response, String> where
    FetchUrlImpl: FetchUrl
{
    let request_url = format!("{}?format=json&url={}", endpoint.url, url);

    fetch_url.fetch_url(&request_url)
        .map_err(|e| format!("{:?}", e))
        .and_then(parse_response)
}

impl Endpoint {
    fn has_matching_scheme(&self, url: &str) -> bool {
        match self.schemes {
            Some(ref schemes) =>
                schemes.iter()
                .filter(|scheme| url_matches_scheme(url, scheme))
                .next()
                .is_some(),

            None => false
        }
    }
}

fn url_matches_scheme(url: &str, scheme: &str) -> bool {
    let mut url_chars = url.chars().peekable();
    let mut scheme_chars = scheme.chars().peekable();

    let mut current_scheme_char = scheme_chars.next();

    while let Some(url_char) = url_chars.next() {
        match current_scheme_char {
            Some('*') if scheme_chars.peek() == url_chars.peek() => (),
            Some('*') => continue,

            Some(scheme_char) if scheme_char == url_char => (),

            Some(_) | None => return false
        }

        current_scheme_char = scheme_chars.next();
    }

    true
}

fn parse_response(data: Vec<u8>) -> Result<Response, String> {
    std::str::from_utf8(&data)
        .map_err(|e| format!("{:?}", e))
        .and_then(|data| serde_json::from_str(data).map_err(|e| format!("{:?}", e)))
}

#[cfg(test)]
mod tests {
    #[test]
    fn url_matches_scheme() {
        assert_eq!(
            super::url_matches_scheme("spotify:abc", "spotify:*"),
            true
        );

        assert_eq!(
            super::url_matches_scheme(
                "https://youtu.be/v/5mMOsl8qpfc",
                "https://youtu.be/*"
            ),
            true
        );

        assert_eq!(
            super::url_matches_scheme(
                "https://www.youtube.com/watch?v=5mMOsl8qpfc",
                "https://www.youtube.com/watch*"
            ),
            true
        );
    }
}
