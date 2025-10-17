use fv_std::{decreases, invariant};

#['requires(n <= 5)]
#['ensures(result == n * 2)]
unconstrained fn main(n: u32) -> pub u32 {
  let mut i = 0u32;
  let mut acc = 0u32;

  while i < n {
    invariant(n <= 5);
    invariant(i <= n);
    invariant(acc == i * 2);
    decreases(n - i);

    i += 1;
    acc += 2;
  }

  acc
}
