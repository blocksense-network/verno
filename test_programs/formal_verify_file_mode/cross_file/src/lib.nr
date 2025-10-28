mod helpers;

use helpers::double;

#['ensures(result == x + x)]
fn apply_double(x: Field) -> Field {
    double(x)
}
