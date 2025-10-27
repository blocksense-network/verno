// Ported from Verus `examples/guide/equality.rs`
fn equal1(x: u8, y: u8) {
    let eq1 = x == y;
    let eq2 = y == x;
    assert((!eq1) | eq2);
}

fn equal3(x: u8, y: u8) {
    assert({
        let eq1 = x == y;
        let eq2 = y == x;
        (!eq1) | eq2
    });
}

fn main() -> pub u8 {
    equal1(3, 3);
    equal1(3, 4);
    equal3(5, 5);
    0
}
