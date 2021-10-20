use rustc_middle::mir::BasicBlock;

const BB_LABEL: &str = "bb";
const RET_VAR: &str = "ret";

pub fn bb_label(bb: &BasicBlock) -> String {
    format!("{}{}", BB_LABEL, bb.as_u32())
}

pub fn ret_var() -> String {
    String::from(RET_VAR)
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
