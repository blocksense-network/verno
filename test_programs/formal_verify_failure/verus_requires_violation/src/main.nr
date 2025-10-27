#['requires(flag)]
fn requires_true(flag: bool) {
    assert(flag);
}

fn main() -> pub u32 {
    requires_true(false);
    0
}
