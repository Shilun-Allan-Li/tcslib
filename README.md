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

## Matching PDF proofs to TCSlib

The repository includes an auditable Codex workflow for comparing a local PDF or
validated Markdown reference with TCSlib proofs:

```bash
# Free local extraction only
python3 scripts/proofmatch.py extract notes.pdf --local-only --max-cost 1.00

# Estimate before paid agent stages
python3 scripts/proofmatch.py estimate notes.pdf

# Full extraction, selective visual repair, search, and comparison
python3 scripts/proofmatch.py run notes.pdf --max-cost 1.00

# Start downstream matching from existing validated Markdown
python3 scripts/proofmatch.py match notes.md --max-cost 1.00
```

The workflow stores both `notes.raw.md` and `notes.md`. It writes no blueprint
proof-source metadata until the user explicitly approves a generated review with
`python3 scripts/proofmatch.py review RUN_ID`.

Then run `lake update` to fetch the dependency.

# Building locally

Install Lean following the [setup instructions](https://leanprover-community.github.io/get_started.html), then run:

```
lake exe cache get
lake build
```

# Contributing and discussion

Contributions are welcome — please open an issue or pull request on [GitHub](https://github.com/Shilun-Allan-Li/tcslib).
