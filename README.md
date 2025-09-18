# Verno

A tool for formally verifying your Noir projects.

## Formal Verification in Noir

Formal verification mathematically ensures that your code is correct for all possible inputs. Unlike traditional testing, which checks a limited set of scenarios, formal verification can eliminate entire categories of bugs by proving that your code behaves as expected under all conditions.

Noir's design, which avoids features like pointers, global mutable state, and complex memory management, makes it particularly well-suited for formal verification. This is especially important for the high-stakes world of crypto-economic protocols and smart contracts, where a single bug can have devastating consequences.

To bring formal verification to Noir, we built Verno on top of the [Verus](https://github.com/verus-lang/verus) verification framework. Verus integrates the powerful Z3 SMT solver, allowing for precise logical reasoning. By compiling Noir to Verus, we've created a proof-of-concept formal verification system that you can use today.

### Installation

#### Prerequisites

Before you begin, you need to have the Rust programming language and its package manager, Cargo, installed on your system.

We recommend using [rustup](https://rustup.rs/) to install and manage your Rust versions. This project includes a `rust-toolchain.toml` file, and `rustup` will automatically download and use the correct Rust toolchain for you.

#### 1. Clone the Repository

First, clone the Verno repository from GitHub:

```bash
git clone https://github.com/blocksense-network/verno.git
cd verno
```

#### 2. Set up the Environment

You have two options for setting up the development environment: using Nix or by running the provided shell scripts.

##### Option A: With Nix

If you have the [Nix package manager](https://nixos.org/download.html) installed, you can easily set up a development environment by running:

```bash
nix develop
```

This command will create a shell with all the necessary dependencies for Verno.

##### Option B: Without Nix

If you don't have Nix, you can set up the environment by running the following shell scripts from the root of the repository:

```bash
./get_verus_std.sh
./venir_build.sh
```

These scripts will download and build the required dependencies. Please follow any instructions printed by the scripts.

#### 3. Build and Test

Once your environment is set up, you can build Verno using Cargo:

```bash
cargo build
```

To ensure everything is working correctly, run the test suite:

```bash
cargo test
```

If all tests pass, you have successfully installed Verno!

### Example usage

1. Create a new project using `nargo` or `verno`:

    You can create a new Noir project using `nargo`:
    ```bash
    nargo new my_program
    ```

    Alternatively, if you have `nargo` in your path or have set up the `NARGO_PATH` environment variable, you can use `verno` to proxy the command:
    ```bash
    verno new my_program
    ```

2. Navigate to the folder:

    ```bash
    cd my_program
    ```

3. Update `src/main.nr` with your favorite text editor to:

    ```rust
    #['requires(x < 100 & 0 < y & y < 100)]
    #['ensures(result >= 5 + x)]
    fn main(x: u32, y: u32) -> pub u32 {
      x + y * 5
    }
    ```

4. Finally, verify the program:

    ```bash
    verno formal-verify
    ```

### Leveraging Formal Verification

Consider the following code:
```rust
fn main(x: i32, y:i32, arr: [u32; 5]) -> pub u32 {
  let z = arithmetic_magic(x, y);
  arr[z]
}

fn arithmetic_magic(x: i32, y: i32) -> i32 {
  (x / 2) + (y / 2)
}
```
Attempting to formally verify this code will produce an error because the value of `z` could fall outside the valid index range for `arr`.

We can fix this by adding a check to ensure `z` is within the array bounds:
```rust
fn main(x: i32, y:i32, arr: [u32; 5]) -> pub u32 {
  let z = arithmetic_magic(x, y);
  if (z >= 0) & (z < 5) {
    arr[z]
  } else {
    0
  }
}

fn arithmetic_magic(x: i32, y: i32) -> i32 {
  (x / 2) + (y / 2)
}
```
This version successfully verifies.

## Conclusion

Verno empowers developers to write safer, more reliable Noir programs.

Built with love by the blocksense.network team.
