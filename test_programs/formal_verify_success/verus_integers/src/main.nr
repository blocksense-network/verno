#['requires(start < limit)]
#['ensures(result == limit - start)]
fn difference(start: u32, limit: u32) -> u32 {
    let diff = limit - start;
    assert(diff + start == limit);
    diff
}

#['requires(value < 200)]
#['ensures(result == value + 1)]
fn add_one(value: u32) -> u32 {
    value + 1
}

#['requires(factor <= 1000)]
#['ensures(result == factor * 2)]
fn double(factor: u32) -> u32 {
    let doubled = factor * 2;
    assert(doubled >= factor);
    doubled
}

#['requires(number < 1000)]
#['ensures((result < 10) & (result == number % 10))]
fn last_digit(number: u32) -> u32 {
    let remainder = number % 10;
    assert(remainder < 10);
    remainder
}

#['ensures(result == 63)]
fn main() -> pub u32 {
    let diff = difference(5, 20);
    let next = add_one(24);
    let doubled = double(10);
    let digit = last_digit(123);

    diff + next + doubled + digit
}
