use rustc_middle::mir::{BasicBlock, Local};

pub const SWITCH_LABEL: &str = "sw";

const BB_LABEL: &str = "bb";
const RET_VAR: &str = "ret";
const RET_LABEL: &str = "rlab";
const MIR_TEMP_PREFIX: &str = "m_";
const GIL_TEMP_PREFIX: &str = "g_";
const GIL_UNUSED_VAR: &str = "u";

pub fn bb_label(bb: BasicBlock) -> String {
    format!("{}{}", BB_LABEL, bb.as_usize())
}

pub fn ret_label() -> String {
    String::from(RET_LABEL)
}

pub fn ret_var() -> String {
    String::from(RET_VAR)
}

pub fn temp_name_from_local(local: Local) -> String {
    format!("{}{}", MIR_TEMP_PREFIX, local.as_usize())
}

pub fn gil_temp_from_id(id: usize) -> String {
    format!("{}{}", GIL_TEMP_PREFIX, id)
}

pub fn unused_var() -> String {
    String::from(GIL_UNUSED_VAR)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bb_label_test() {
        let bb = BasicBlock::from(0usize);
        assert_eq!(bb_label(bb), String::from("bb0"));
        let bb = BasicBlock::from(100usize);
        assert_eq!(bb_label(bb), String::from("bb100"));
    }
}
