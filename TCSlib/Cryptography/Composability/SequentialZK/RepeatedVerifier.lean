/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Phases
import TCSlib.Cryptography.Composability.SequentialZK.VerifierPrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract padded verifiers and their real phases

## Main definitions

* `Composability.PaddedVerifierSpec`: the published equations and position readers needed
  to compare an abstract repeated verifier with its original verifier.

## Main results

* `Composability.PaddedVerifierSpec.phase_exec`: each real phase against any prover is
  an original-verifier execution with the earlier received history hardwired.
* `Composability.PaddedVerifierSpec.phase_take`: each final aggregate phase history is
  that original verifier history.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition).
-/

namespace TCSlib.Cryptography.Composability

/-- For original protocol `π`, abstract repeated protocol `ρ`, common input `x`, phase count
`q`, real prover-message count `p`, and terminal reply function `terminal z r hist`,
`PaddedVerifierSpec π ρ x q p terminal` collects the coin, move, reply, verdict, and history
length equations displayed below. Here a real phase has `π.rounds.eval |x|` moves and is
padded to twice that length. [PS10, Theorem 175.1].
Its first three fields state `ρ.V.coinLen x.length = q * π.V.coinLen x.length`, `ρ.rounds.eval
x.length = 2 * π.rounds.eval x.length * q` and `ρ.verifierFirst = π.verifierFirst`. -/
structure PaddedVerifierSpec (π ρ : Protocol) (x : List Bool) (q p : ℕ)
    (terminal : List Bool → List Bool → List (List Bool) → List Bool) : Prop where
  /-- The verifier coin length is `ρ.V.coinLen |x| = q * π.V.coinLen |x|`. -/
  coinLen_eq : ρ.V.coinLen x.length = q * π.V.coinLen x.length
  /-- The repeated move count is `ρ.rounds.eval |x| = 2 * π.rounds.eval |x| * q`. -/
  rounds_eq : ρ.rounds.eval x.length = 2 * π.rounds.eval x.length * q
  /-- The first-mover flag is `ρ.verifierFirst = π.verifierFirst`. -/
  first_eq : ρ.verifierFirst = π.verifierFirst
  /-- For `z`, `r`, `hist`, `ρ.V.next x z r hist` is `terminal z r hist` at history length
  `q*k`; otherwise its real-phase reply is `π.V.next` on block `idx/(2*k)` and the suffix
  after `(idx/(2*k))*k` received slots, and its filler reply is `[]`, with `k=π.rounds |x|`
  and `idx=if π.verifierFirst then 2*|hist| else 2*|hist|-1`. -/
  next_eq (z r : List Bool) (hist : List (List Bool)) :
    ρ.V.next x z r hist =
      if hist.length = q * π.rounds.eval x.length then terminal z r hist
      else
        let idx := if π.verifierFirst then 2 * hist.length else 2 * hist.length - 1
        if idx % (2 * π.rounds.eval x.length) < π.rounds.eval x.length then
          π.V.next x z (coinBlock (π.V.coinLen x.length)
            (idx / (2 * π.rounds.eval x.length)) r)
            (hist.drop (idx / (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
        else []
  /-- For `z`, `r`, `hist`, `terminal z r hist = [true]` exactly when each phase `j<q`
  satisfies `π.V.next x z (coinBlock c j r) ((hist.drop (j*k)).take p)=[true]`;
  the other terminal output is `[false]`, with `k=π.rounds |x|`, `c=π.V.coinLen |x|`. -/
  terminal_eq (z r : List Bool) (hist : List (List Bool)) :
    terminal z r hist =
      if (List.range q).all (fun j => decide
        (π.V.next x z (coinBlock (π.V.coinLen x.length) j r)
          ((hist.drop (j * π.rounds.eval x.length)).take p) = [true]))
      then [true] else [false]
  /-- For `P`, `y`, `z`, `rP`, `rV`, and a verifier move `t`, the index computed from its
  source received-history length is `t`: `if π.verifierFirst then 2*|hist| else 2*|hist|-1=t`.
  Here `hist=(exec P ρ.V π.verifierFirst x y z rP rV t).2`. -/
  index_eq (P : Strategy) (y z rP rV : List Bool) (t : ℕ)
      (hm : moverIsV π.verifierFirst t = true) :
    (if π.verifierFirst then 2 * (exec P ρ.V π.verifierFirst x y z rP rV t).2.length
      else 2 * (exec P ρ.V π.verifierFirst x y z rP rV t).2.length - 1) = t
  /-- For `P`, `y`, `z`, `rP`, `rV`, `j≤q`, both histories after `2*k*j` moves have
  length `j*k`, where `k=π.rounds.eval |x|`. -/
  boundary_lengths (P : Strategy) (y z rP rV : List Bool) (j : ℕ) (hj : j ≤ q) :
    (exec P ρ.V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).1.length =
        j * π.rounds.eval x.length ∧
      (exec P ρ.V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2.length =
        j * π.rounds.eval x.length
  /-- For `P`, `y`, `z`, `rP`, `rV`, the original verifier receives `p` messages:
  `(exec P π.V π.verifierFirst x y z rP rV (π.rounds.eval |x|)).2.length=p`. -/
  local_length (P : Strategy) (y z rP rV : List Bool) :
    (exec P π.V π.verifierFirst x y z rP rV (π.rounds.eval x.length)).2.length = p
  /-- For `j`, `t`, `moverIsV π.verifierFirst (2*k*j+t)=moverIsV π.verifierFirst t`,
  where `k=π.rounds.eval |x|`. -/
  period (j t : ℕ) :
    moverIsV π.verifierFirst (2 * π.rounds.eval x.length * j + t) =
      moverIsV π.verifierFirst t

/-- For a padded-verifier specification `d`, prover `P`, inputs `y`, `z`, tapes `rP`, `rV`,
phase `j<q`, and local move count `t≤k`, both source histories after `2*k*j+t` equal their
histories after `2*k*j` followed by the corresponding original-verifier histories against
`prefixProver P y rP priorP` on verifier block `j`. Here `k=π.rounds.eval |x|` and `priorP`
is the source prover-received history after `2*k*j`. [PS10, Theorem 175.1].

**Proof sketch.** Apply the generic fixed-prefix phase theorem. At a verifier move of the
real phase, its recovered index is `2*k*j+t`; this excludes the terminal-history branch.
Its quotient and residue modulo `2*k` are `j` and `t`, so the padded reply is the original
verifier's reply on coin block `j`. The boundary reader identifies the dropped prefix
length as `j*k`. The generic theorem supplies both transcript decompositions, including
zero-round phases through its empty local execution. -/
theorem PaddedVerifierSpec.phase_exec {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy)
    (y z rP rV : List Bool) (j : ℕ) (hj : j < q) {t : ℕ}
    (ht : t ≤ π.rounds.eval x.length) :
    (exec P ρ.V π.verifierFirst x y z rP rV
      (2 * π.rounds.eval x.length * j + t)).1 =
        (exec P ρ.V π.verifierFirst x y z rP rV
          (2 * π.rounds.eval x.length * j)).1 ++
          (exec (prefixProver P y rP (exec P ρ.V π.verifierFirst x y z rP rV
            (2 * π.rounds.eval x.length * j)).1) π.V π.verifierFirst x [] z []
              (coinBlock (π.V.coinLen x.length) j rV) t).1 ∧
      (exec P ρ.V π.verifierFirst x y z rP rV
        (2 * π.rounds.eval x.length * j + t)).2 =
        (exec P ρ.V π.verifierFirst x y z rP rV
          (2 * π.rounds.eval x.length * j)).2 ++
          (exec (prefixProver P y rP (exec P ρ.V π.verifierFirst x y z rP rV
            (2 * π.rounds.eval x.length * j)).1) π.V π.verifierFirst x [] z []
              (coinBlock (π.V.coinLen x.length) j rV) t).2 := by
  let k := π.rounds.eval x.length
  have hb := (d.boundary_lengths P y z rP rV j hj.le).2
  apply exec_phase P ρ.V π.V π.verifierFirst x y z rP rV
    (coinBlock (π.V.coinLen x.length) j rV) (2 * k * j) k
    (fun t _ => d.period j t) ?_ ht
  intro t ht hm
  have hmv : moverIsV π.verifierFirst (2 * k * j + t) = true := by
    rw [d.period j t]
    exact hm
  have hi := d.index_eq P y z rP rV (2 * k * j + t) hmv
  -- The terminal branch cannot occur at a real move of phase j.
  have hlen : 2 * (exec P ρ.V π.verifierFirst x y z rP rV
      (2 * k * j + t)).2.length ≤ 2 * k * j + t + 1 := by
    by_cases hv : π.verifierFirst = true
    · rw [if_pos hv] at hi
      omega
    · rw [if_neg hv] at hi
      omega
  have hne : (exec P ρ.V π.verifierFirst x y z rP rV
      (2 * k * j + t)).2.length ≠ q * k := by
    intro heq
    rw [heq] at hlen
    have hjk := Nat.mul_le_mul_right k hj
    nlinarith
  have hmod : (2 * k * j + t) % (2 * k) = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (2 * k * j + t) / (2 * k) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  -- Read the real reply and the fixed old verifier-history length.
  rw [d.next_eq, if_neg hne]
  dsimp only
  rw [hi, hmod, if_pos ht, hdiv, hb]

/-- For specification `d`, prover `P`, inputs `y`, `z`, tapes `rP`, `rV`, and `j<q`,
the final verifier history restricted to `(drop (j*k)).take p` is the original verifier's
history against the prefix-hardwired prover on block `j`, where `k=π.rounds.eval |x|`.
[PS10, Theorem 175.1, the phase test in the aggregate verdict].

**Proof sketch.** A zero-round phase has empty histories on both sides. Otherwise the
real-phase coupling identifies its ending history with the old `j*k` messages followed
by the original verifier's `p` received messages. This ending history is a prefix of the
final transcript. Take that prefix, then drop its old messages, to recover the original
verifier history used by the aggregate phase test. -/
theorem PaddedVerifierSpec.phase_take {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    {terminal : List Bool → List Bool → List (List Bool) → List Bool}
    (d : PaddedVerifierSpec π ρ x q p terminal) (P : Strategy)
    (y z rP rV : List Bool) (j : ℕ) (hj : j < q) :
    ((exec P ρ.V π.verifierFirst x y z rP rV
      (2 * π.rounds.eval x.length * q)).2.drop (j * π.rounds.eval x.length)).take p =
      (exec (prefixProver P y rP (exec P ρ.V π.verifierFirst x y z rP rV
        (2 * π.rounds.eval x.length * j)).1) π.V π.verifierFirst x [] z []
          (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
  by_cases hk0 : π.rounds.eval x.length = 0
  · simp only [hk0, Nat.mul_zero, Nat.zero_mul, exec_zero, List.drop_nil, List.take_nil]
  · let k := π.rounds.eval x.length
    have hb := (d.boundary_lengths P y z rP rV j hj.le).2
    have hphase := (d.phase_exec P y z rP rV j hj (t := k) le_rfl).2
    have hl : (exec P ρ.V π.verifierFirst x y z rP rV (2 * k * j + k)).2.length =
        j * k + p := by
      rw [hphase, List.length_append, hb, d.local_length]
    have hjk := Nat.mul_le_mul_right k hj
    have hle : 2 * k * j + k ≤ 2 * k * q := by nlinarith
    have hp := exec_snd_take P ρ.V π.verifierFirst x y z rP rV
      (2 * k * j + k) (2 * k * q - (2 * k * j + k))
    rw [Nat.add_sub_of_le hle, hl] at hp
    rw [List.take_drop, hp, hphase, ← hb, List.drop_left]

end TCSlib.Cryptography.Composability
