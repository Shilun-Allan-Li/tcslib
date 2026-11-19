/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Primality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reader bridge for `PRIMES` and `PRIMESBin` (bounded, to be deleted)

**Recorded bounded Rule-10 exception** (plan decision log, 2026-11-18, ruling EF-H1-R2 (B);
duplication ledger DL-69). The languages `Randomized.PRIMES`
(`Complexity/Randomized/PrimalityMath.lean`) and `Randomized.PRIMESBin`
(`Complexity/Randomized/Primality.lean`) publish no membership reader, and those files belong to
the Complexity (Arora–Barak) owners. This file states exactly the two missing readers, with the
content the owner files would publish, proved by `Iff.rfl`; it is the only place of
`Cryptography/Candidates/` that sees through these two definitions.

**This file is to be deleted** when the Complexity owner PR adding `Randomized.mem_PRIMES` and
`Randomized.mem_PRIMESBin` merges: its consumers (the `PRIMESBin` bridge of `PrimesInP.lean`,
`ArithmeticFP.ofPrimesInP` and `arithmeticFP_iff_primesInP`) are then re-pointed one-for-one
to the owner readers. The readers live in their own namespace so that the owner names never
clash with them in between.

| Reader | Definition | Owner file |
|---|---|---|
| `PrimesBridge.mem_PRIMES` | `Randomized.PRIMES` | `Complexity/Randomized/PrimalityMath.lean` |
| `PrimesBridge.mem_PRIMESBin` | `Randomized.PRIMESBin` | `Complexity/Randomized/Primality.lean` |

## Main definitions

None: this file only states readers.

## Main results

The two readers above (no new mathematics).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§7.2.2, p. 128: the language `PRIMES`.)
-/

namespace TCSlib.Cryptography.Candidates.PrimesBridge

open Complexity.LogProg (bitsVal)

/-- Reader for `Randomized.PRIMES` (missing in `PrimalityMath.lean`):
`N ∈ PRIMES ↔ N.Prime`. -/
theorem mem_PRIMES (N : ℕ) : N ∈ Randomized.PRIMES ↔ N.Prime := Iff.rfl

/-- Reader for `Randomized.PRIMESBin` (missing in `Primality.lean`):
`x ∈ PRIMESBin ↔ bitsVal x ∈ PRIMES`. -/
theorem mem_PRIMESBin (x : List Bool) :
    x ∈ Randomized.PRIMESBin ↔ bitsVal x ∈ Randomized.PRIMES := Iff.rfl

end TCSlib.Cryptography.Candidates.PrimesBridge
