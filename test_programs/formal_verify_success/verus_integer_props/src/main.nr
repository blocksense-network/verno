// Ported from Verus `examples/integers.rs`
#['requires(u < 200)]
#['requires(n < 1_000)]
#['ensures(result == 0)]
fn integer_comparisons(u: u8, n: u32) -> u32 {
    let double_u = (u as u32) + (u as u32);
    assert(double_u >= (u as u32));
    assert((u as u32) % 10 < 10);

    let half_n = n / 2;
    assert(half_n <= n);

    let half_u = (u as u32) / 2;
    assert(half_u <= (u as u32));

    let add_one = (u as u32) + 1;
    assert(add_one == (u as u32) + 1);

    0
}

#['ensures(result == 0)]
fn main() -> pub u32 {
    integer_comparisons(24, 200);
    integer_comparisons(5, 10);
    0
}
