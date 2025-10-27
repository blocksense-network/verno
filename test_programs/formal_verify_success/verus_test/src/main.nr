// Ported from Verus `examples/test.rs`
#['requires(a < 100)]
#['ensures(result == a + 1)]
fn foo(a: u32) -> u32 {
    a + 1
}

#['ensures(result == 2)]
fn main() -> pub u32 {
    let c = 1;
    let mut b = 3;
    b = 4;
    b = foo(c);
    b
}
