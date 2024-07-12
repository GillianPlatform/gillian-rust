
#[ensures((^str)@.len() >= len@ && (^str)@.len() >= (*str)@.len())]
#[ensures((^str)@.len() == len@ || (^str)@.len() == (*str)@.len())]
#[ensures(len@ <= (*str)@.len() ==> (^str)@.len() == (*str)@.len())]
#[ensures(len@ > (*str)@.len() ==> (^str)@.len() == len@)]
#[ensures(forall<i: _> 0 <= i && i < (*str)@.len() ==> (^str)@[i] == (*str)@[i])]
#[ensures(forall<i: _> (*str)@.len() <= i && i < len@ ==> (^str)@[i] == pad)]

    #[invariant(old_str@.len() <= str@.len())]
    #[invariant(old_str@.len() < len@ ==> str@.len() <= len@)]
    #[invariant(str@.len() > len@ ==> str@.len() == old_str@.len())]
    #[invariant(forall<i: _> 0 <= i && i < old_str@.len() ==> str@[i] == old_str@[i])]
    #[invariant(forall<i: _> old_str@.len() <= i && i < str@.len() ==> str@[i] == pad)]