/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.RealPhases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The padded repeated-prover construction contract

The construction contract packages only direct equations and move-count readers for an
original protocol and an abstract padded repetition. Zero-knowledge proofs supply their
relation and message bound separately. This keeps both statistical and computational
composition proofs independent of the owned construction definitions.

## Main definitions

* `PaddedProverSpec π ρ x q p`: the repeated prover's equations and position readers at `x`.

## Main results

* `PaddedProverSpec.real_phase`: the real portion is an original wrapped-verifier execution.
* `PaddedProverSpec.padded_phase`: the complete phase appends the real messages and fillers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- For original protocol `π`, repeated protocol `ρ`, common input `x`, phase count `q` and
real prover-message count `p`, `PaddedProverSpec π ρ x q p` asserts the displayed prover coin,
round, mover, reply, index and history-count equations, with `k = π.rounds.eval |x|`.
The contract is independent of any witness relation or message bound.
[PS10, Theorem 175.1, the padded repeated-prover construction]. -/
structure PaddedProverSpec (π ρ : Protocol) (x : List Bool) (q p : ℕ) : Prop where
  /-- The prover coin length is `ρ.P.coinLen |x| = q * π.P.coinLen |x|`. -/
  prover_coinLen : ρ.P.coinLen x.length = q * π.P.coinLen x.length
  /-- The total move count is `ρ.rounds.eval |x| = 2 * π.rounds.eval |x| * q`. -/
  rounds_eval : ρ.rounds.eval x.length = 2 * π.rounds.eval x.length * q
  /-- The first-mover flag is `ρ.verifierFirst = π.verifierFirst`. -/
  first : ρ.verifierFirst = π.verifierFirst
  /-- For `y,r,hist`, `ρ.P.next x y r hist` uses index
  `idx = if π.verifierFirst then 2|hist|-1 else 2|hist|`; it runs `π.P.next` on coin block
  `idx/(2k)` and the history after `(idx/(2k))*k` slots when `idx%(2k)<k`, and returns `[]`
  otherwise, where `k = π.rounds.eval |x|`. -/
  next (y r : List Bool) (hist : List (List Bool)) :
    ρ.P.next x y r hist =
      let idx := if π.verifierFirst then 2 * hist.length - 1 else 2 * hist.length
      if idx % (2 * π.rounds.eval x.length) < π.rounds.eval x.length then
        π.P.next x y (coinBlock (π.P.coinLen x.length)
          (idx / (2 * π.rounds.eval x.length)) r)
          (hist.drop (idx / (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
      else []
  /-- For `V,y,z,rP,rV,n`, at an active prover move, the index recovered from the source
  prover's received-history length is `n`, for every natural move index. -/
  prover_index (V : Strategy) (y z rP rV : List Bool) (n : ℕ)
      (hm : moverIsV π.verifierFirst n = false) :
    (if π.verifierFirst then
      2 * (exec ρ.P V π.verifierFirst x y z rP rV n).1.length - 1
    else 2 * (exec ρ.P V π.verifierFirst x y z rP rV n).1.length) = n
  /-- For `V,y,z,rP,rV,j`, both received histories after `2*k*j` moves have length `j*k`,
  for every natural `j`, with `k = π.rounds.eval |x|`. -/
  boundary (V : Strategy) (y z rP rV : List Bool) (j : ℕ) :
    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).1.length =
        j * π.rounds.eval x.length ∧
    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2.length =
        j * π.rounds.eval x.length
  /-- For `V,y,z,rP,rV`, the original verifier receives exactly `p` messages in `k` moves:
  `(exec π.P V π.verifierFirst x y z rP rV k).2.length = p`. -/
  original_count (V : Strategy) (y z rP rV : List Bool) :
    (exec π.P V π.verifierFirst x y z rP rV (π.rounds.eval x.length)).2.length = p
  /-- The number of real prover messages satisfies `p ≤ π.rounds.eval |x|`. -/
  real_le : p ≤ π.rounds.eval x.length
  /-- For `j,t`, the mover pattern satisfies `moverIsV π.verifierFirst (2*k*j+t) =
  moverIsV π.verifierFirst t`, with `k = π.rounds.eval |x|`. -/
  period (j t : ℕ) :
    moverIsV π.verifierFirst (2 * π.rounds.eval x.length * j + t) =
      moverIsV π.verifierFirst t

namespace PaddedProverSpec

/-- For a construction specification `h`, verifier `V`, inputs `y,z`, tapes `rP,rV`, phase
`j<q` and `t≤k`, the two source histories after `2*k*j+t` equal their phase-start histories
followed by the original `π.P` execution on coin block `j` against `phaseVerifier V`.
The wrapped auxiliary word is `phaseAux z rV j` of the earlier verifier history.
[PS10, Theorem 175.1; Gol01, §4.3.4, real-phase endpoint]. -/
theorem real_phase {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rP rV : List Bool)
    (j : ℕ) (hj : j < q) {t : ℕ} (ht : t ≤ π.rounds.eval x.length) :
    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j + t)).1 =
      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).1 ++
        (exec π.P (phaseVerifier V) π.verifierFirst x y
          (phaseAux z rV j
            (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
          (coinBlock (π.P.coinLen x.length) j rP) [] t).1 ∧
    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j + t)).2 =
      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2 ++
        (exec π.P (phaseVerifier V) π.verifierFirst x y
          (phaseAux z rV j
            (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
          (coinBlock (π.P.coinLen x.length) j rP) [] t).2 :=
  exec_real_phase ρ.P π.P V π.verifierFirst x y z rP rV (π.rounds.eval x.length) q j hj
    (h.next y rP) (fun n _ hm => h.prover_index V y z rP rV n hm)
    (h.boundary V y z rP rV j).1 (fun u _ => h.period j u) ht

/-- For a construction specification `h`, verifier `V`, inputs `y,z`, tapes `rP,rV` and
phase `j<q`, the source verifier history after the complete padded phase is its earlier
history followed by the wrapped original real-phase messages and `k-p` empty fillers.
The verifier's filler replies are unrestricted. [PS10, Theorem 175.1; Gol01, §4.3.4]. -/
theorem padded_phase {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rP rV : List Bool)
    (j : ℕ) (hj : j < q) :
    (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * (j + 1))).2 =
      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2 ++
        ((exec π.P (phaseVerifier V) π.verifierFirst x y
          (phaseAux z rV j
            (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
          (coinBlock (π.P.coinLen x.length) j rP) [] (π.rounds.eval x.length)).2 ++
            List.replicate (π.rounds.eval x.length - p) []) :=
  exec_padded_real_phase ρ.P π.P V π.verifierFirst x y z rP rV (π.rounds.eval x.length)
    q j p hj (h.next y rP) (fun n _ hm => h.prover_index V y z rP rV n hm)
    (h.boundary V y z rP rV j).1 (h.boundary V y z rP rV j).2
    (h.boundary V y z rP rV (j + 1)).2
    (h.original_count (phaseVerifier V) y
      (phaseAux z rV j
        (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2)
      (coinBlock (π.P.coinLen x.length) j rP) [])
    (fun u _ => h.period j u)

end PaddedProverSpec

end TCSlib.Cryptography.SequentialZK
