use fv_std::assume;

fn print_two_digit_number(i: i32) {
    let _ = i;
}

#['ensures(result == 8 * x1)]
fn octuple(x1: i32) -> i32 {
    assume(-16 <= x1);
    assume(x1 < 16);
    let x2 = x1 + x1;
    assume(-32 <= x2);
    assume(x2 < 32);
    let x4 = x2 + x2;
    assume(-64 <= x4);
    assume(x4 < 64);
    let result = x4 + x4;
    assume(-128 <= result);
    assume(result <= 127);
    result
}

#['ensures(result == 0)]
fn main() -> pub u32 {
    let input: i32 = 10;
    assert(-16 <= input);
    assert(input < 16);
    let n = octuple(input);
    assert(n == 80);
    assert(-99 <= n);
    assert(n < 100);
    print_two_digit_number(n);
    0
}
