#[derive(Debug)]
pub struct Position {
    pub line: i32,
    pub column: i32,
}

impl Default for Position {
    fn default() -> Self {
        Position {
            line: -1,
            column: -1,
        }
    }
}

#[derive(Debug)]
pub struct Location {
    pub start: Position,
    pub end: Position,
    pub source: String,
}

impl Default for Location {
    fn default() -> Self {
        Location {
            start: Position::default(),
            end: Position::default(),
            source: "(none)".to_string(),
        }
    }
}