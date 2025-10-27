// Ported from Verus `examples/guide/getting_started.rs`
#['ensures(result <= x)]
#['ensures(result <= y)]
#['ensures((x <= y) ==> (result == x))]
#['ensures((y < x) ==> (result == y))]
fn min_int(x: i32, y: i32) -> i32 {
    if x <= y {
        x
    } else {
        y
    }
}

#['ensures(result == 0)]
fn main() -> pub i32 {
    let first = min_int(10, 20);
    assert(first == 10);

    let second = min_int(-10, -20);
    assert(second == -20);

    let swapped = min_int(20, 10);
    let mirrored = min_int(10, 20);
    assert(swapped == mirrored);

    let equal_pair = min_int(5, 5);
    assert(equal_pair == 5);

    0
}
