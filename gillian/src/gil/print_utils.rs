use std::fmt;

pub(crate) fn comma_separated_display<T>(vec: &[T], f: &mut fmt::Formatter<'_>) -> fmt::Result
where
    T: fmt::Display,
{
    let mut sep = "";
    for elem in vec {
        f.write_str(sep)?;
        write!(f, "{}", elem)?;
        sep = ", ";
    }
    Ok(())
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
