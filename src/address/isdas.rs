//! Isolation Domain (ISD) and Autonomous System (AS) identifiers.

use anyhow::{Error as AnyError};
use radix_fmt::radix;
use std::fmt;

const ISD_BITS: i32 = 16;
const ISD_MAX: ISD = ISD(((1 << ISD_BITS) as u32 - 1) as u16);

const AS_BITS: i32 = 48;
const AS_MAX: AS = AS((1 << AS_BITS) - 1);

const AS_BGP_BITS: i32 = 32;
const AS_BGP_MAX: AS = AS((1 << AS_BGP_BITS) - 1);

const AS_PART_BITS: i32 = 16;
const AS_PART_BASE: u32 = 16;
const AS_PART_MASK: u64 = (1 << AS_PART_BITS) - 1;
const AS_PARTS: i32 = AS_BITS / AS_PART_BITS;

/// ISD is the ISolation Domain identifier.
/// Formatting and allocations are defined at: https://github.com/scionproto/scion/wiki/ISD-and-AS-numbering#isd-numbers
#[derive(Debug, PartialEq)]
pub struct ISD(u16);

impl ISD {
    pub fn parse(string: &str) -> Result<Self, AnyError> {
        match string.parse::<u16>() {
            Ok(n) => Ok(Self(n)),
            Err(e)=>
            Err(AnyError::msg(format!("could not parse ISD: {}", string))),
        }
    }
}

impl fmt::Display for ISD {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// AS is the Autonomous System identifier.
/// Formatting and allocations are defined at: https://github.com/scionproto/scion/wiki/ISD-and-AS-numbering#as-numbers
#[derive(Debug, PartialEq, PartialOrd)]
pub struct AS(u64);

impl AS {
    // Parses an AS from a decimal (32-bit BGP AS) or
    // ipv6-style hex (with SCION-only AS numbers) string.
    pub fn parse(string: &str) -> Result<Self, AnyError> {
        let res: Vec<&str> = string.split(":").collect();

        // If the input does not have a colon, it should
        // be a BGP AS. Parse it as a 32-bit decimal number.
        if res.len() == 1 {
            return match string.parse::<u32>() {
                Ok(n) => Ok(Self(n.into())), 
                Err(e) => Err(AnyError::msg(format!("could not parse BGP AS: {}", res[0])))
            };
        }

        // AS_PARTS is currently 48/16 = 3, so should not panic.
        if res.len() != AS_PARTS.try_into().unwrap() {
            return Err(AnyError::msg(format!("wrong number of colon-separated strings in AS: expected {}, got {}", AS_PARTS, res.len())));
        }

        let mut parsed: u64 = 0;
        for r in res {
            parsed <<= AS_PART_BITS;
            let v: u64 = match u64::from_str_radix(r, AS_PART_BASE) {
                Ok(n) => {
                    if n > AS_PART_MASK {
                        return Err(AnyError::msg(format!("AS part value too long: max {}, got {}", AS_PART_MASK, n)));
                    }

                    n
                },
                Err(_) => {
                    return Err(AnyError::msg(format!("could not parse AS part: {}", r)));
                }
            };
            parsed |= v;
        }

        // Should be unreachable.
        // Left to protect against possible refactor issues.
        if parsed > AS_MAX.0 {
            return Err(AnyError::msg(format!("AS out of range: max {}, value {}", AS_MAX.0, {parsed})));
        }

        Ok(AS(parsed))
    }
}

impl fmt::Display for AS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let as_val = self.0;
        if as_val > AS_MAX.0 {
            return write!(f, "{} [Illegal AS: larger than {}]", as_val, AS_MAX.0);
        }

        // Format BGP ASes as decimal
        if as_val <= AS_BGP_MAX.0 {
            return write!(f, "{}", as_val);
        }

        // Format all other ASes as colon-separated hex.
        let mut i = 0;
        while i < AS_PARTS {
            if i > 0 {
                write!(f, ":");
            }

            let shift = AS_PART_BITS * (AS_PARTS - i - 1);
            write!(f, "{}", radix((as_val >> shift) & AS_PART_MASK, AS_PART_BASE as u8));

            i +=1;
        };

        Ok(())
    }
}

/// IA represents the ISD (ISolation Domain) and AS (Autonomous System) of a given SCION AS.
/// The highest 16 bits form the ISD number, and the lower 48 bits form the AS number.
#[derive(Debug, PartialEq)]
pub struct IA(u64);

impl IA {
    pub fn from(isd_val: ISD, as_val: AS) -> Result<Self, AnyError> {
        if as_val > AS_MAX {
            return Err(AnyError::msg(format!("AS out of range: max {}, value {}", AS_MAX.0, as_val.0)));
        }

        let mut ia_val: u64 = (isd_val.0 as u64) << AS_BITS;
        ia_val |= as_val.0 & AS_MAX.0;

        Ok(IA(ia_val))
    }

    pub fn parse(ia: &str) -> Result<Self, AnyError> {
        let parts: Vec<&str> = ia.split("-").collect();
        if parts.len() != 2 {
            return Err(AnyError::msg(format!("invalid ISD-AS: {}", ia)));
        }

        let isd = ISD::parse(parts[0])?;
        let as_ = AS::parse(parts[1])?; 
        
        Self::from(isd, as_)
    }

    pub fn to_isd(&self) -> ISD {
        // The cast will truncate the upper bits
        ISD((self.0 >> AS_BITS) as u16)
    }

    pub fn to_as(&self) -> AS {
        AS(self.0 & AS_MAX.0)
    }
}

impl fmt::Display for IA {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.to_isd(), self.to_as())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_isd_parse() {
        assert_eq!(ISD(0), ISD::parse("0").unwrap());
        assert_eq!(ISD(1), ISD::parse("1").unwrap());
        assert_eq!(ISD_MAX, ISD::parse("65535").unwrap());

        assert_eq!("could not parse ISD: ", format!("{}", ISD::parse("").unwrap_err().root_cause()));
        assert_eq!("could not parse ISD: a", format!("{}", ISD::parse("a").unwrap_err().root_cause()));
        assert_eq!("could not parse ISD: 65536", format!("{}", ISD::parse("65536").unwrap_err().root_cause()));
    }

    #[test]
    fn test_as_parse_bgp() {
        assert_eq!(AS(0), AS::parse("0").unwrap());
        assert_eq!(AS(1), AS::parse("1").unwrap());
        assert_eq!(AS_BGP_MAX, AS::parse("4294967295").unwrap());

        assert_eq!("could not parse BGP AS: ", format!("{}", AS::parse("").unwrap_err().root_cause()));
        assert_eq!("could not parse BGP AS: 0x0", format!("{}", AS::parse("0x0").unwrap_err().root_cause()));
        assert_eq!("could not parse BGP AS: ff", format!("{}", AS::parse("ff").unwrap_err().root_cause()));
        assert_eq!("could not parse BGP AS: 4294967296", format!("{}", AS::parse("4294967296").unwrap_err().root_cause()));
    }

    #[test]
    fn test_as_parse_scion() {
        assert_eq!(AS(0), AS::parse("0:0:0").unwrap());
        assert_eq!(AS(1), AS::parse("0:0:1").unwrap());
        assert_eq!(AS(0x000100000000), AS::parse("1:0:0").unwrap());
        assert_eq!(AS_MAX, AS::parse("ffff:ffff:ffff").unwrap());

        // Incorrectly formatted (wrong number of colons).
        assert_eq!("wrong number of colon-separated strings in AS: expected 3, got 2", format!("{}", AS::parse(":").unwrap_err().root_cause()));
        assert_eq!("wrong number of colon-separated strings in AS: expected 3, got 4", format!("{}", AS::parse("0:0:0:").unwrap_err().root_cause()));
        assert_eq!("wrong number of colon-separated strings in AS: expected 3, got 4", format!("{}", AS::parse(":0:0:0").unwrap_err().root_cause()));
        assert_eq!("wrong number of colon-separated strings in AS: expected 3, got 2", format!("{}", AS::parse("0:0").unwrap_err().root_cause()));
        
        // Incorrectly formatted, too-long parts.
        assert_eq!("AS part value too long: max 65535, got 65536", format!("{}", AS::parse("10000:0:0").unwrap_err().root_cause()));
        assert_eq!("AS part value too long: max 65535, got 65536", format!("{}", AS::parse("0:10000:0").unwrap_err().root_cause()));
        assert_eq!("AS part value too long: max 65535, got 65536", format!("{}", AS::parse("0:0:10000").unwrap_err().root_cause()));

        assert_eq!("could not parse AS part: 0x0", format!("{}", AS::parse("0:0x0:0").unwrap_err().root_cause()));
    }

    #[test]
    fn test_ia_parse_from() {
        // Success cases also test from.
        assert_eq!(IA::parse("0-0").unwrap(), IA::from(ISD(0), AS(0)).unwrap());
        assert_eq!(IA::parse("1-1").unwrap(), IA::from(ISD(1), AS(1)).unwrap());
        assert_eq!(IA::parse("65535-1").unwrap(), IA::from(ISD_MAX, AS(1)).unwrap());
        assert_eq!(IA::parse("1-4294967295").unwrap(), IA::from(ISD(1), AS_BGP_MAX).unwrap());
        assert_eq!(IA::parse("1-1:0:0").unwrap(), IA::from(ISD(1), AS(0x000100000000)).unwrap());
        assert_eq!(IA::parse("1-1:fcd1:1").unwrap(), IA::from(ISD(1), AS(0x0001fcd10001)).unwrap());
        assert_eq!(IA::parse("65535-ffff:ffff:ffff").unwrap(), IA::from(ISD_MAX, AS_MAX).unwrap());

        assert_eq!("invalid ISD-AS: ", format!("{}", IA::parse("").unwrap_err().root_cause()));
        assert_eq!("invalid ISD-AS: a", format!("{}", IA::parse("a").unwrap_err().root_cause()));
        assert_eq!("could not parse ISD: 1a", format!("{}", IA::parse("1a-2b").unwrap_err().root_cause()));
        assert_eq!("could not parse ISD: ", format!("{}", IA::parse("-").unwrap_err().root_cause()));
        assert_eq!("could not parse BGP AS: ", format!("{}", IA::parse("1-").unwrap_err().root_cause()));
        assert_eq!("could not parse ISD: ", format!("{}", IA::parse("-1").unwrap_err().root_cause()));
        assert_eq!("invalid ISD-AS: -1-", format!("{}", IA::parse("-1-").unwrap_err().root_cause()));
        assert_eq!("invalid ISD-AS: 1--1", format!("{}", IA::parse("1--1").unwrap_err().root_cause()));

        assert_eq!("could not parse ISD: 65536", format!("{}", IA::parse("65536-1").unwrap_err().root_cause()));
        assert_eq!("could not parse BGP AS: 4294967296", format!("{}", IA::parse("1-4294967296").unwrap_err().root_cause()));
        assert_eq!("AS part value too long: max 65535, got 65536", format!("{}", IA::parse("1-ffff:ffff:10000").unwrap_err().root_cause()));
    }

    #[test]
    fn test_ia_string() {
        assert_eq!("0-0", format!("{}", IA::from(ISD(0),AS(0)).unwrap()));
        assert_eq!("1-1", format!("{}", IA::from(ISD(1),AS(1)).unwrap()));
        assert_eq!("65535-1", format!("{}", IA::from(ISD(65535),AS(1)).unwrap()));
        assert_eq!("1-4294967295", format!("{}", IA::from(ISD(1), AS_BGP_MAX).unwrap()));
        assert_eq!("1-1:0:0", format!("{}", IA::from(ISD(1), AS(AS_BGP_MAX.0 + 1)).unwrap()));
        assert_eq!("65535-ffff:ffff:ffff", format!("{}", IA::from(ISD(65535), AS_MAX).unwrap()));
    }

    #[test]
    fn test_as_string() {
        assert_eq!("0", format!("{}", AS(0)));
        assert_eq!("1", format!("{}", AS(1)));
        assert_eq!("999", format!("{}", AS(999)));
        assert_eq!("4294967295", format!("{}", AS_BGP_MAX));
        assert_eq!("1:0:0", format!("{}", AS(AS_BGP_MAX.0 + 1)));
        assert_eq!("1:fcd1:1", format!("{}", AS(0x0001fcd10001)));
        assert_eq!("ffff:ffff:ffff", format!("{}", AS_MAX));
        assert_eq!("281474976710656 [Illegal AS: larger than 281474976710655]", format!("{}", AS(AS_MAX.0 + 1)));
    }
}