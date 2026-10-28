/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Complexity.Randomized.Primitives
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity — randomized and non-uniform polynomial-time machines

The computational-model layer of the Pass–shelat campaign ([PS10, §2.1]; plan
`PassShelatChapter2-4Plan.md`, foundation decisions D3, D4, D9, D11): probabilistic
polynomial-time machines with explicit coin and advice polynomials, their closure calculus,
and the repetition lemma that every repeated-adversary argument of chapters 2–4 rests on.

**Integration note.** `Complexity.NUPPT` (in `PPT`) is a model type in the sense of
`policy.md` §1; the integrator registers it in `TCSlib/ComputationalModels.lean` (entry
"`Complexity.NUPPT` — non-uniform probabilistic polynomial-time machines [PS10, Definitions
23.4 and 26.8], `Complexity/Randomized/PPT.lean`") and imports this facade from `TCSlib.lean`.

## Contents

* `PolyExpr` — syntactic polynomials `Complexity.PolyExpr` for every length and budget
  (evaluation, substitution, monotonicity, the normal-form majorant `C (n+1)^c`).
* `PPT` — the structure `Complexity.NUPPT` (PPT [PS10, Definition 23.4] with worst-case
  time [PS10, Definition 23.5], computing with probability one [PS10, Definition 24.6],
  non-uniform PPT in the advice form [PS10, Definition 26.8]); `output`, `runAt`, `runLit`,
  `Uniform`, `ofPolyTime`, and the subtype `Complexity.PPT`.
* `NonUniform` — the two formulations of Definition 26.8, the literal activation and
  uniformity lemmas, the PPT subtype API, and the optional bridge to
  `Turing.FinTM.DecidesWithAdviceInTime`.
* `Primitives` — the two new machines (coin splitting `pairSplitAt`, unary multiplication
  `unaryMul`), the unary evaluator `polyTimeComputable_unaryPoly`, and the typed coin cuts
  `pairTakePoly`/`pairDropPoly`.
* `Closure` — the closure catalogue of non-uniform PPTs (pre/post-composition, parameter
  changes, hard-wired advice, coins as data, sequential composition).
* `Repetition` — the repetition lemma `polyTimeComputable_iterateFind` (the single admissible
  admission, D11), iteration and emission variants, majority, xor, equality and block map.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/
