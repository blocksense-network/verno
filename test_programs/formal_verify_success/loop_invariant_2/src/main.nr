use fv_std::invariant;
use fv_std::U32_MAX;

#['requires(n <= U32_MAX / 2)]
#['ensures(result == n * 2)]
unconstrained fn main(n: u32) -> pub u32 {
  let mut acc = 0;
 
   for i in 0..n {
    invariant(n <= U32_MAX / 2);
    invariant(acc == i*2);
    invariant(i <= n);
 
    acc += 2;
  }
 
  acc
}
