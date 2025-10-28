#['ensures(result == x * x)]
fn square(x: Field) -> Field {
    x * x
}

#['ensures(result == x + 1)]
fn increment(x: Field) -> Field {
    x + 1
}
