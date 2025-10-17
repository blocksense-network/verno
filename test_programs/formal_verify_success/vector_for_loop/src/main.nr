fn main(elements: [Field; 10]) -> pub Field {
  let mut acc = 0;
  for x in elements {
    acc += x;
  }
  acc
}
