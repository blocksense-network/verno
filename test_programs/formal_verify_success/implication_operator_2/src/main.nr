// This test shows that the implication operator p -> q is
// equivalent to !p V q.
// Inside of a function's body the implication operator is
// not supported
#['requires(y ==> x > 5)]
fn main(x: u32, y: bool) {
    assert(!y | (x > 5));
}
