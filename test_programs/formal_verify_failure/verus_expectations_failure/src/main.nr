// Ported from Verus `examples/assertions.rs` - requires violation
#['requires(condition)]
fn has_expectations(condition: bool) {
    assert(condition);
}

fn main() -> pub u32 {
    has_expectations(false);
    0
}
