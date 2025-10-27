fn impossible_assert() {
    assert(false);
}

fn main() -> pub u32 {
    impossible_assert();
    1
}
