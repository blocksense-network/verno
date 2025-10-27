// Ported from Verus `examples/assorted_demo.rs`
use fv_std::{decreases, invariant};

#['ensures(result)]
fn integers_are_not_equal() -> bool {
    let x = 3;
    let y = 4;
    let unequal = x != y;
    assert(unequal);
    unequal
}

struct Train {
    cars: u32,
}

#['ensures(result)]
fn identical_trains_match() -> bool {
    let first = Train { cars: 10 };
    let second = Train { cars: 10 };
    let equal_car_count = first.cars == second.cars;
    assert(equal_car_count);
    equal_car_count
}

#['requires((a > 0) & (b > 0))]
#['requires(a <= 1_000)]
#['requires(b <= 1_000)]
#['ensures(result >= 1)]
#['ensures(a % result == 0)]
#['ensures(b % result == 0)]
#['ensures(result <= a)]
#['ensures(result <= b)]
unconstrained fn gcd_scan(a: u32, b: u32) -> u32 {
    let bound = if a <= b { a } else { b };
    assert(bound <= a);
    assert(bound <= b);
    assert(bound >= 1);

    let mut candidate = bound;
    let mut result = 1u32;
    while candidate > 0 {
        invariant(candidate <= bound);
        invariant(result >= 1);
        invariant(result <= bound);
        invariant(a % result == 0);
        invariant(b % result == 0);
        decreases(candidate);

        if (a % candidate == 0) & (b % candidate == 0) {
            result = candidate;
            break;
        }

        candidate -= 1;
    }

    result
}

#['ensures(result == 0)]
unconstrained fn main() -> pub u32 {
    let neq = integers_are_not_equal();
    let trains_equal = identical_trains_match();
    let gcd_value = gcd_scan(42, 182);

    assert(neq);
    assert(trains_equal);
    assert(42 % gcd_value == 0);
    assert(182 % gcd_value == 0);
    assert(gcd_value <= 42);
    assert(gcd_value >= 1);

    0
}
