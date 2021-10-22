use rustc_middle::mir::{BasicBlock, Local};

const BB_LABEL: &str = "bb";
const RET_VAR: &str = "ret";
const TEMP_PREFIX: &str = "mirgiltemp___";

pub fn bb_label(bb: &BasicBlock) -> String {
    format!("{}{}", BB_LABEL, bb.as_u32())
}

pub fn ret_var() -> String {
    String::from(RET_VAR)
}

pub fn temp_name_from_local(local: &Local) -> String {
    format!("{}{}", TEMP_PREFIX, local.as_u32())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bb_label_test() {
        let bb = BasicBlock::from(0u32);
        assert_eq!(bb_label(&bb), String::from("bb0"));
        let bb = BasicBlock::from(100u32);
        assert_eq!(bb_label(&bb), String::from("bb100"));
    }
}
