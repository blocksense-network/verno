// Ported from Verus `examples/basic_failure.rs`
#['ensures(result == 1)]
fn fail_post_expr() -> u32 {
    0
}

#['ensures(*state == 1)]
fn fail_post_stmt(state: &mut u32) {
    *state = 0;
}

fn main() -> pub u32 {
    let mut value = 5;
    fail_post_stmt(&mut value);
    fail_post_expr();
    0
}
