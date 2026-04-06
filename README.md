# TCSlib

A Lean 4 library for Theoretical Computer Science.

Official website at <https://shilun-allan-li.github.io/tcslib/>.

# What's TCSlib?

TCSlib formalizes results in Theoretical Computer Science using [Lean 4](https://lean-lang.org) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). Every theorem is machine-checked.

## Areas covered

- **Boolean Function Analysis** — Fourier analysis over the Boolean hypercube, hypercontractivity, Arrow's theorem, and more.
- **Error-Correcting Codes** — Singleton, Hamming, Gilbert–Varshamov, and Johnson bounds; linear codes; list decoding; quantum codes.

# Using TCSlib in your project

To add TCSlib as a dependency, add the following to your `lakefile.lean`:

```lean
require TCSlib from git "https://github.com/Shilun-Allan-Li/tcslib" @ "main"
```

Then run `lake update` to fetch the dependency.

# Building locally

Install Lean following the [setup instructions](https://leanprover-community.github.io/get_started.html), then run:

```
lake exe cache get
lake build
```

# Contributing and discussion

Contributions are welcome — please open an issue or pull request on [GitHub](https://github.com/Shilun-Allan-Li/tcslib).
