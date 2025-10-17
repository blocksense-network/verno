use std::hint::black_box;

#['ensures(result == 6)]
unconstrained fn main() -> pub Field {
  black_box(5) + 1
}
