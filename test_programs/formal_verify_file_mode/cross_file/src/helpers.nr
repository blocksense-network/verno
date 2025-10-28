// Intentionally left without specs so we can observe verification coverage.
#['ensures(result == x + x)]
pub fn double(x: Field) -> Field {
    x + x
}
