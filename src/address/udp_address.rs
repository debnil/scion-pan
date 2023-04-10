//! UDP address.
//!
//! Address for a SCION/UDP end point.

#![allow(dead_code)]

use crate::address::isdas::IA;

use anyhow::Error as AnyError;
use std::fmt;
use std::net::IpAddr;

/// Address for a SCION/UDP end point.
#[derive(Debug, PartialEq)]
pub struct UDPAddr {
    ia: IA,
    ip: IpAddr,
    port: u16,
}

impl UDPAddr {
    pub fn network() -> String {
        "scion+udp".to_string()
    }

    /// Parses an address string.
    ///
    /// Supported formats are based on RFC 3986:
    /// https://scion.docs.anapaya.net/en/latest/uri.html#scion-udp
    ///
    /// Examples:
    /// - [isd-as,ipv4]:port (e.g., [1-ff00:0:110,192.0.2.1]:80)
    /// - [isd-as,ipv6%zone]:port (e.g., [1-ff00:0:110,2001:DB8::1%zone]:80)
    pub fn parse(string: &str) -> Result<Self, AnyError> {
        // Split string into host and port.
        let split: Vec<&str> = string.split("]:").collect();

        if split.len() != 2 {
            return Err(AnyError::msg(
                "invalid scion+udp format: expected [isd-as,ip]:port".to_string(),
            ));
        }

        if !split[0].starts_with('[') {
            return Err(AnyError::msg(
                "invalid scion+udp format: expected [isd-as,ip]:port".to_string(),
            ));
        }

        // Remove leading '['.
        let mut host = split[0];
        host = &host[1..host.len()];

        let parts: Vec<&str> = host.split(',').collect();
        if parts.len() != 2 {
            return Err(AnyError::msg(format!(
                "invalid address: host parts invalid: expected 2, actual {}",
                parts.len()
            )));
        }

        let ia: IA = IA::parse(parts[0])?;
        let ip = parts[1].parse::<IpAddr>()?;
        let port = split[1].parse::<u16>()?;

        let udp = Self { ia, ip, port };

        Ok(udp)
    }
}

impl fmt::Display for UDPAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ip = match self.ip {
            IpAddr::V4(_) => format!("[{}]", self.ip),
            IpAddr::V6(_) => format!("{}", self.ip),
        };

        write!(f, "{},{}:{}", self.ia, ip, self.port)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_udp_parse() {
        // Error strings.
        assert!(UDPAddr::parse("foo").is_err());
        assert!(UDPAddr::parse("5-").is_err());
        assert!(UDPAddr::parse("2-ff00:0:300,[").is_err());
        assert!(UDPAddr::parse("5-ff00:0:300,[]").is_err());
        assert!(UDPAddr::parse("5-ff00:0:300,[127.0.0.1]").is_err());
        assert!(UDPAddr::parse("40-ff00:0:300,[]:19").is_err());
        assert!(UDPAddr::parse("1-ff00:0:300,[]:13,[f").is_err());
        assert!(UDPAddr::parse("5-ff00:0:300,[hostthatdoesnotexistforsure]:12").is_err());
        assert!(UDPAddr::parse("1-ff00:0:300]:14,[1.2.3.4]").is_err());
        assert!(UDPAddr::parse("1-ff00:0:300,[1.2.3.4]:70000").is_err());
        assert!(UDPAddr::parse("1-ff00:0:300,[1.2.3.4]]").is_err());
        assert!(UDPAddr::parse("1-ff00:0:300,::1:60000").is_err());
        assert!(UDPAddr::parse("[1-ff00:0:110,1.2.3.4]:70:300").is_err());
        assert!(UDPAddr::parse("[1-ff00:0:110,1.2.3.4,80]:80").is_err());
        assert!(UDPAddr::parse("[1-ff00:0:110,1.2.3.4]").is_err());
        assert!(UDPAddr::parse("[1-ff00:0:110,::1%some-zone]").is_err());
        assert!(UDPAddr::parse("").is_err());

        assert_eq!(
            UDPAddr {
                ia: IA::parse("1-ff00:0:110").unwrap(),
                ip: "2001:DB8::1".parse::<IpAddr>().unwrap(),
                port: 80,
            },
            UDPAddr::parse("[1-ff00:0:110,2001:DB8::1]:80").unwrap()
        );

        assert_eq!(
            UDPAddr {
                ia: IA::parse("1-ff00:0:110").unwrap(),
                ip: "2001:DB8::1".parse::<IpAddr>().unwrap(),
                port: 80,
            },
            UDPAddr::parse("[1-ff00:0:110,2001:DB8::1]:80").unwrap()
        );

        assert_eq!(
            UDPAddr {
                ia: IA::parse("1-64496").unwrap(),
                ip: "2001:DB8::1".parse::<IpAddr>().unwrap(),
                port: 80,
            },
            UDPAddr::parse("[1-64496,2001:DB8::1]:80").unwrap()
        );

        assert_eq!(
            UDPAddr {
                ia: IA::parse("1-64496").unwrap(),
                ip: "2001:DB8::1".parse::<IpAddr>().unwrap(),
                port: 60000,
            },
            UDPAddr::parse("[1-64496,2001:DB8::1]:60000").unwrap()
        );
    }
}
