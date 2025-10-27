#['requires(a < 100)]
#['ensures(result == a + 1)]
fn foo(a: u32) -> u32 {
    a + 1
}

#['requires(start < 100)]
#['ensures(result == start + 1)]
fn call_foo(start: u32) -> u32 {
    foo(start)
}

#['ensures(result == 11)]
fn main() -> pub u32 {
    call_foo(10)
}
