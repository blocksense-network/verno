use fv_std::invariant;

#['ensures(result == bound)]
unconstrained fn main(bound: u32) -> pub u32 {
  let mut acc = 0u32;

  for i in 0..bound {
    invariant(acc == i);
    invariant(acc <= bound);

    acc += 1;
  }

  acc
}
