#['requires(x <= 10)]
fn main(x: u64) {
  let y = 0;
  assert(x <= 10);
  assert(x * x <= 100);
}
