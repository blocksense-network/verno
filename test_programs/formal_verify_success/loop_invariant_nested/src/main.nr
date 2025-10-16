use fv_std::invariant;

#['requires(bound <= 6)]
#['ensures(result == bound)]
unconstrained fn main(bound: u32) -> pub u32 {
  let mut outer = 0u32;
  let mut total_processed = 0u32;

  for i in 0..bound {
    invariant(outer == i);
    invariant(total_processed == i);
    invariant(outer <= bound);

    let inner_bound = bound - i;
    let mut inner = 0u32;

    for j in 0..inner_bound {
      invariant(inner == j);
      invariant(inner <= inner_bound);
      invariant(inner_bound <= bound);

      inner += 1;
    }

    total_processed += 1;
    outer += 1;
  }

  total_processed
}
