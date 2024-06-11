use std::fmt;

pub(crate) fn separated_display<T, S>(vec: &[T], sep: S, f: &mut fmt::Formatter<'_>) -> fmt::Result
where
    T: fmt::Display,
    S: fmt::Display,
{
    let mut first = true;
    for elem in vec {
        if first {
            first = false;
        } else {
            write!(f, "{}", sep)?;
        }
        write!(f, "{}", elem)?;
    }
    Ok(())
}

pub(crate) fn maybe_quoted(s: &str) -> String {
    if s.is_empty() {
        panic!("Empty string for function or predicate identifier");
    }
    let mut first = true;

    let needs_quotes = !s.chars().all(|c| {
        if first {
            first = false;
            c.is_alphabetic()
        } else {
            c == '_' || c.is_alphanumeric()
        }
    });

    if needs_quotes {
        format!("\"{}\"", s)
    } else {
        s.to_string()
    }
}

pub(crate) fn write_maybe_quoted(s: &str, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if s.is_empty() {
        panic!("Empty string for function or predicate identifier");
    }
    let mut first = true;

    let needs_quotes = !s.chars().all(|c| {
        if first {
            first = false;
            c.is_alphabetic()
        } else {
            c == '_' || c.is_alphanumeric()
        }
    });

    if needs_quotes {
        write!(f, "\"{}\"", s)
    } else {
        write!(f, "{}", s)
    }
}
