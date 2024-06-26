use std::cmp::Ordering;
use std::iter::{self, from_fn};

/// Sort a list of strings in a "human-friendly way". See examples...
///
/// Known limitation: function does not work as expected if the string contains integers bigger
/// than the maximum value of usize (it won't panic, but the final ordering might not be correct).
///
/// # Examples
///
/// ```ignore
///  let mut unsorted =
///      ["helloh", "hello2", "hello", "hello11", "hello1", "hello100", "42", "hello1000"];
///  let sorted =
///      ["42", "hello", "hello1", "hello2", "hello11", "hello100", "hello1000", "helloh"];

///  natural_sort(&mut unsorted);
///  assert_eq!(sorted, unsorted);
/// ```
pub fn natural_sort<T: AsRef<str>>(strings: &mut [T]) {
    strings.sort_by(|s1, s2| {
        // I'm pretty sure this is a total order relation ;)
        let mut it1 = s1.as_ref().chars().peekable();
        let mut it2 = s2.as_ref().chars().peekable();
        loop {
            match (it1.next(), it2.next()) {
                (Some(c1 @ '0'..='9'), Some(c2 @ '0'..='9')) => {
                    let num1: usize = iter::once(c1)
                        .chain(from_fn(|| it1.by_ref().next_if(|c| c.is_ascii_digit())))
                        .collect::<String>()
                        .parse()
                        .unwrap_or(42);
                    let num2: usize = iter::once(c2)
                        .chain(from_fn(|| it2.by_ref().next_if(|c| c.is_ascii_digit())))
                        .collect::<String>()
                        .parse()
                        .unwrap_or(42);
                    if num1 != num2 {
                        return num1.cmp(&num2);
                    }
                }
                (Some('0'..='9'), Some(_)) => return Ordering::Less,
                (Some(_), Some('0'..='9')) => return Ordering::Greater,
                (Some(c1), Some(c2)) => {
                    if c1 != c2 {
                        return c1.cmp(&c2);
                    }
                }
                (None, Some(_)) => return Ordering::Less,
                (Some(_), None) => return Ordering::Greater,
                (None, None) => return Ordering::Equal,
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_nat_sort_1() {
        let mut unsorted =
            ["helloh", "hello2", "hello", "hello11", "hello1", "hello100", "42", "hello1000"];
        let sorted =
            ["42", "hello", "hello1", "hello2", "hello11", "hello100", "hello1000", "helloh"];

        natural_sort(&mut unsorted);
        assert_eq!(sorted, unsorted);
    }
}
