use fv_std::{decreases, invariant};

#['ensures(result == input)]
#['requires(input <= 32)]
unconstrained fn exec_basic_recursive_expr(input: u32) -> u32 {
    let mut countdown = input;
    let mut acc = 0u32;
    while countdown > 0 {
        invariant(countdown <= input);
        invariant(acc + countdown == input);
        decreases(countdown);
        countdown -= 1;
        acc += 1;
    }
    assert(acc == input);
    acc
}

#['requires(counter <= 32)]
unconstrained fn exec_basic_recursive_stmt(counter: u32) {
    let mut countdown = counter;
    while countdown > 0 {
        invariant(countdown <= counter);
        decreases(countdown);
        countdown -= 1;
    }
}

#['ensures(result == 10)]
unconstrained fn exec_basic_while_loop() -> u32 {
    let mut i = 0u32;
    while i < 10 {
        invariant(i <= 10);
        decreases(10 - i);
        i += 1;
    }
    i
}

#['ensures(result == 50)]
unconstrained fn exec_nested_while_loop() -> u32 {
    let mut outer = 0u32;
    let mut inner = 0u32;
    while outer < 10 {
        invariant(outer <= 10);
        invariant(inner <= 5);
        decreases(10 - outer);

        while inner < 5 {
            invariant(inner <= 5);
            decreases(5 - inner);
            inner += 1;
        }
        outer += 1;
    }
    outer * 5
}

#['ensures(result == 30)]
unconstrained fn exec_for_loop() -> u32 {
    let mut iter = 0u32;
    let mut acc = 0u32;
    while iter < 10 {
        invariant(iter <= 10);
        invariant(acc == iter * 3);
        decreases(10 - iter);
        acc += 3;
        iter += 1;
    }
    acc
}

#['ensures(result == 30)]
unconstrained fn exec_for_loop_2() -> u32 {
    let end = 10u32;
    let mut iter = 0u32;
    let mut acc = 0u32;
    while iter < end {
        invariant(iter <= end);
        invariant(end == 10u32);
        invariant(acc == iter * 3);
        decreases(end - iter);
        acc += 3;
        iter += 1;
    }
    acc
}

#['ensures(result == 130)]
unconstrained fn main() -> pub u32 {
    exec_basic_recursive_stmt(5);
    exec_basic_recursive_expr(10)
        + exec_basic_while_loop()
        + exec_nested_while_loop()
        + exec_for_loop()
        + exec_for_loop_2()
}
