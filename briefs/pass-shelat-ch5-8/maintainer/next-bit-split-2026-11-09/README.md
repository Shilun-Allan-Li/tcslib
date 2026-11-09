# Finite and ensemble next-bit results

Seyoon merged the PRG contract move #264 at `850d97de5dff2594d8cdf75f3d7705df4df27108`. Its Lean and checker
inputs match the verified head `eb67b18405a968b75155429bb9a7c884874795b5`.

The next-bit split at `6776475858254d11adadf57776cae215c2c6cd79` puts the fixed-parameter experiment, hybrids,
and both advantage bounds in `Pseudorandom.NextBit.Concrete`. The polynomial-time
machines and both ensemble implications are in `Pseudorandom.NextBit`. The
legacy `Asymptotic.NextBit` import re-exports both layers. [PR #265](https://github.com/Shilun-Allan-Li/tcslib/pull/265)

- The ordinary replay passes all 61 affected modules, including the library
  root and campaign Checks. It verifies 1,027 retained local objects and 3,810
  external objects. The finite import closure has eight TCSlib modules, all
  in finite probability, statistical distance, or concrete generators.
- The old and new standalone imports print the same six declaration types.
  The census maps all 51 original declarations to their new owners. Their
  types, definition values, and axiom dependencies agree after normalizing
  generated binder scopes and relocated private names. Three ensemble proof
  terms change to use the new equations.
- The existing `List.ofFn` equations for prefix and completion are public.
  The new `nextBitPred_eq` and `nextBitDist_eq` readers sit beside their definitions.
  The ensemble proofs also use the existing `nextBitProb_eq`.
- The baseline seal verifies 1,215 requests. The finite and ensemble seals
  verify 39 and 1,222 respectively, including all seven finite definitions at
  the ensemble boundary. Each whole-file seal passes. The control passes
  unsealed, fails at `rfl` when sealed, and passes through the reader under
  the same mask. The source scan finds zero explicit unfolds of the
  newly foreign definitions.
- The prior cleanup ledger has zero observations or provider references at
  the old next-bit owner. Style checks add zero findings. The first development
  run identified the two finite probability imports needed by the split, and
  its log is archived beside the passing run.

`next-bit-checks.zip` has SHA-256 `d1ec25d22f2ef745a611b5a9ecda1c08409e4531f6d67363ae0c8031e43798a7`.

**Clear to merge — both layers, the compatibility import, and the affected checks pass.**
