use std::fmt;

pub fn comma_separated_display(
    vec: &Vec<impl fmt::Display>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let mut sep = "";
    for elem in vec {
        f.write_str(sep)?;
        write!(f, "{}", elem)?;
        sep = ", ";
    }
    Ok(())
}
