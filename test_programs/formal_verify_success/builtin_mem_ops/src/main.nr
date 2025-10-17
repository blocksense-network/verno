use std::mem::{checked_transmute, zeroed};

#['ensures(result == 8)]
fn main() -> pub Field {
  let arr: [Field; 3] = zeroed();
  let initial_sum = arr[0] + arr[1] + arr[2];

  let mut pair: [Field; 2] = zeroed();
  pair[0] = 4;
  let copy: Field = checked_transmute(pair[0]);

  initial_sum + pair[0] + copy
}
