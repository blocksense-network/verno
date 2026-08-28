# Limitations

Verno does not yet cover all of Noir. This page lists what it does not cover, and it is
kept in agreement with the code: every entry below corresponds to a specific place in the
translator that refuses to continue, and each of those places names its construct in the
message it prints.

When Verno meets one of these, it stops with:

```
The application panicked (crashed).
Message:  not yet implemented: UNSUPPORTED: <the construct>
```

The `UNSUPPORTED:` prefix is what the regression harness (`scripts/run-corpus.py`) matches
on. It classifies such a run as **unsupported** rather than as a failed proof, so hitting a
limitation does not move the proved/not-proved counts a version bump is judged against.

*Verified against Noir `v1.0.0-beta.26`.*

## Unsupported constructs

| Construct | Example | What happens |
|---|---|---|
| **Lambdas and function values** | `let f = \|x\| x / 2;` | `UNSUPPORTED: function types (lambdas, function values)` |
| **Vectors** (`Vector`, formerly `Slice`) | see the note below | `UNSUPPORTED: vector types (Vec<T> / slices)`, `vector literals` |
| **Strings** | `let s = "hello";` | `UNSUPPORTED: string literals` / `string types` |
| **Format strings** | `f"{x}"` | `UNSUPPORTED: format-string literals` / `format-string types` |
| **`match` expressions and enums** | `match c { ... }` | `UNSUPPORTED: match expressions and enums` |
| **Unary negation of a non-constant value** | `-x` where `x` is a variable | `UNSUPPORTED: unary negation of a non-constant value` |
| **Inclusive `for` ranges with non-constant bounds** | `for i in 0..=n` where `n` is a parameter | `UNSUPPORTED: an inclusive for range ... whose bounds are not compile-time constants` |
| **Standard-library functions needing runtime helpers** beyond the verification shim | `x.lt(y)` | usually a panic inside the translator |

Three entries deserve a note.

**Vectors.** Verno has never translated the compiler's variable-length collection type, and
still does not. What changed is how you would reach it from Noir source: the old
`std::collections::vec::Vec` was removed from the standard library (`Could not resolve
'Vec' in path`), `[T; N]::as_slice` was removed, and what used to be `Type::Slice` in the
compiler is now `Type::Vector`. No program written against current Noir was found that
reaches Verno's vector paths at all, so the refusals below are reachable in principle — they
are still in the translator, and named — but were not exercised against
`v1.0.0-beta.26`. Treat this row as "unsupported, and currently also unreachable".

**Negation.** `-5` written as a literal is folded by the Noir compiler into a negative
integer literal and is fully supported; it is only negation applied to a *value* at run
time that is not.

**Inclusive ranges.** `for i in a..=b` stopped being rewritten into an exclusive range and
now reaches the monomorphised AST as written, since Noir `v1.0.0-beta.19`
(noir-lang/noir#10567). When both bounds
are compile-time constants, Verno unrolls the loop and handles the inclusive bound exactly,
so `for i in 0..=4` works. When they are not, the loop is lowered to a synthetic `while`
whose exit condition, decreases measure and invariant are all written for Noir's *exclusive*
range semantics. Rather than approximate them — which would produce a *passing* proof of a
loop the program does not contain — Verno refuses. Nothing about this is fundamental; it is
three expressions in `vir_backend::vir_gen::expr_to_vir::expr` that need an inclusive
variant.

## Recently checked, and now supported

These were re-checked against `v1.0.0-beta.26` because Noir changed them, and they work:

- **Compound assignment** (`x += y`, `x *= y`). Noir stopped desugaring these in the parser
  in `v1.0.0-beta.20` (noir-lang/noir#12123) and now does it during elaboration. Verno sees
  the desugared form and is unaffected. (The same change silently broke the CodeTracer
  tracer fork, so it was worth confirming rather than assuming.)
- **Repeated array literals** (`[expr; N]`). Since `v1.0.0-beta.19` (noir-lang/noir#11279)
  the monomorphiser no longer expands these into `N` copies; they arrive as a single
  `Repeated` literal. Verno materialises them, so both the loop-unrolling constant
  interpreter and VIR generation behave as they did before.
- **Mutable references** as function parameters. Use `fv_std::old()` in a specification to
  refer to the incoming value (see the ghost-functions guide).
- **Unconstrained functions**, provided their bodies carry the right
  `#['requires]`/`#['ensures]` contracts and loop annotations (`invariant`, `decreases`).
  See *Unconstrained Noir Support*.

## Things Noir itself rejects first

These never reach Verno, so they are not Verno limitations:

- **`enum` and `match`** are behind Noir's unstable `enums` feature and are rejected by the
  compiler unless `-Zenums` is passed. Were the feature enabled, Verno would report
  `UNSUPPORTED: match expressions and enums`.
- **`while` loops in constrained code**: Noir requires a statically known iteration count in
  constrained functions. Verno does support `while` in *unconstrained* functions.

## Not yet re-measured

- **`Option<T>`** was previously listed as unsupported, with an example that verified
  *incorrectly* rather than crashing. Against `v1.0.0-beta.26` an `Option<u32>` program now
  completes the whole Noir → VIR pipeline and reaches the solver, so the old "unsupported"
  claim no longer describes what happens. Whether the resulting proof is *correct* has not
  been established — that needs a run with a working solver — so `Option<T>` should be
  treated as unverified rather than as either supported or unsupported.

## Diagnostics that are bugs, not limitations

A panic reading `internal error: entered unreachable code` is **not** a limitation. It means
an invariant Verno relies on did not hold, and it should be reported. The regression harness
deliberately does not fold these into the `unsupported` bucket, so that they cannot hide.
