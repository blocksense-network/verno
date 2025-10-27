use fv_std::{decreases, invariant};

#['ensures((cond & (result == 17)) | ((!cond) & (result == 2)))]
fn branch_example(cond: bool) -> u32 {
    let mut x = 0u32;

    if cond {
        x = 10;
    }

    if cond {
        x = x + 3;
        x = x + 4;
    } else {
        x = x + 2;
    }

    assert((!cond) | (x == 17));
    assert(cond | (x == 2));

    if x == 0 {
        assert(false);
    } else if x == 1 {
        assert(false);
    } else if x == 2 {
        assert(!cond);
    } else {
        assert(x == 17);
    }

    x
}

#['requires(limit <= 50)]
#['ensures(result == limit * 2)]
unconstrained fn loop_example(limit: u32) -> u32 {
    let mut i = 0u32;
    let mut acc = 0u32;

    while i < limit {
        invariant(limit <= 50);
        invariant(i <= limit);
        invariant(acc == i * 2);
        decreases(limit - i);

        acc += 2;
        i += 1;
    }

    acc
}

#['ensures(result == 119)]
unconstrained fn main() -> pub u32 {
    let true_branch = branch_example(true);
    let false_branch = branch_example(false);
    let doubled = loop_example(50);

    true_branch + false_branch + doubled
}
