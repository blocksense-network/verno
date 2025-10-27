// Ported from Verus `examples/assertions.rs` - positive path for requires clauses
#['requires(condition)]
fn has_expectations(condition: bool) {
    assert(condition);
}

#['ensures(result == 0)]
fn main() -> pub u32 {
    has_expectations(true);
    0
}
