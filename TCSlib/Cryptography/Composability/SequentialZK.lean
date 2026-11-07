/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition of zero-knowledge proofs (statement phase)

[PS10, Theorem 175.1]: if `(P, V)` is a perfect or computational zero-knowledge proof for `L`
and `Q` is a polynomial, the protocol `(P_Q, V_Q)` that runs `(P, V)` on the common input `x`
`Q(|x|)` times in sequence, each time with fresh coins, is again a perfect or computational
zero-knowledge interactive proof.

**The construction** (`Protocol.seqRep`), on the interaction model of
`ZeroKnowledge/Interaction.lean` (D8): with `k = rounds(|x|)` moves of `π`, phase `j` occupies
the `2k` moves `2kj, …, 2kj + 2k − 1`.
- The first `k` moves of a phase are `π`'s; in the last `k` (**fillers**) the honest parties
  send `[]`. A phase thus has an even number of moves, so every phase starts with the same mover
  as `π` (`moverIsV_two_mul_add`), even when `k` is odd (the graph protocols have three
  messages). Each party moves exactly `k` times per phase.
- A party finds the global move from the number of messages it has received
  (`proverMoveIndex_exec`, `verifierMoveIndex_exec`), hence its phase `j` and position `t`.
  At a position `t < k` it runs `π`'s next-message function on the coin slice `j` of its tape
  (`coinBlock` from `Asymptotic/Adversary.lean`) and on the messages received in phase `j`
  (all of them real, since `t < k`).
- The coins of `P_Q` and `V_Q` are `Q` copies of `π`'s.
- `V_Q`'s verdict, on its complete history (`Q · k` messages), is `[true]` iff every phase's
  verdict, `V.next` on that phase's real messages, is `[true]`; otherwise `[false]`. When
  `π.verifierFirst = false`, `V_Q` makes the last move, and by the convention of D8 that move is
  its verdict (`outV_eq_getLast_of_moverIsV`); the filler position carries it, and nobody
  reads it.

**Deviations** (beyond D8, declared once here).
- **Filler moves**, as above: each phase is padded to `2k` moves; the honest parties' fillers
  are `[]` and are ignored.
- **Strict or truncated simulators** (ruling G02-#4, D8): zero-knowledge composes to
  zero-knowledge; statistical error `δ` composes to `Q · δ`; perfect zero-knowledge with abort
  ([Gol01, Definition 4.3.1], with which the text's expected-polynomial-time simulators are
  handled) composes to statistical zero-knowledge with error `Q(n) · 2^{-n}`, by retrying each phase's
  simulator `n = |x|` times (any `ω(log n)` retries would do; `n` is the simplest).
- **Bounded prover messages** (`Protocol.ProverBounded`). Under D8, `Strategy.Efficient` bounds
  a verifier's work per activation in the total length of its input, not in `|x|`. A cheating
  `V_Q` may then double its message length in every phase. If the honest prover echoes the
  verifier's messages, which is zero-knowledge for one run, the views of `V_Q` grow like
  `2^{Q(|x|)}`, which no strict PPT simulator can output. The composition theorems therefore
  assume that the honest prover's messages on instances with witnesses have at most `B(|x|)`
  bits. The text's machines read only `t(|x|)` bits per message, so the issue does not arise
  there.
- **At least one phase** for soundness: with `Q(n) = 0`, `V_Q` accepts everything, so the
  interactive-proof statement assumes `1 ≤ Q(n)`.

## Main definitions

* `Composability.proverMoveIndex`, `Composability.verifierMoveIndex`,
  `Composability.proverMoves`: positions from message counts.
* `TCSlib.Cryptography.Protocol.seqProver`, `seqVerifier`, `seqRep`: the `Q`-fold sequential
  repetition.

## Main results

* `moverIsV_two_mul_add`, `countP_moverIsV`, `countP_not_moverIsV`, `exec_fst_length`,
  `exec_snd_length`, `proverMoveIndex_exec`, `verifierMoveIndex_exec`: the parties know their
  position.
* `Protocol.seqRep_exec_phase`: phase `j` of an honest execution of `π.seqRep Q` is an execution
  of `π` with the coin slices `j`.
* `ZK.seqRep`, `StatZK.seqRep` (Thm 175.1, stated; `sorry`s under the source's sketch), and
  `PerfectZK.seqRep` (proved from `StatZK.seqRep`).
* `PerfectZKAbort.seqRep`: the aborting case, derived from `PerfectZKAbort.statZK` and
  `StatZK.seqRep`, with error `Q(n) · 2^{-n}`.
* `InteractiveProof.seqRep` (stated; a `sorry` under its sketch): the repetition is an
  interactive proof.
* `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep` (stated; `sorry`s under their
  sketches): sequential repetition multiplies the soundness error, `s ↦ s^Q` (ruling G3-7d, for
  the text's form of Thm 124.1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1 and its proof sketch (book pp. 175–176).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
  Press, 2001, §4.3.4 (sequential composition) and Definition 4.3.1 (perfect zero-knowledge
  with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

namespace Composability

/-! ### Positions -/

/-- The global index of a prover move, from the number `c` of messages it has received: with
the verifier first, the prover moves at the odd positions `2c − 1`; otherwise at `2c`. -/
def proverMoveIndex (vFirst : Bool) (c : ℕ) : ℕ := if vFirst then 2 * c - 1 else 2 * c

/-- The prover move index is `2c-1` when the verifier starts and `2c` otherwise. -/
theorem proverMoveIndex_eq (vFirst : Bool) (c : ℕ) :
    proverMoveIndex vFirst c = if vFirst then 2 * c - 1 else 2 * c := rfl

/-- The global index of a verifier move, from the number `c` of messages it has received. -/
def verifierMoveIndex (vFirst : Bool) (c : ℕ) : ℕ := if vFirst then 2 * c else 2 * c - 1

/-- The verifier move index is `2c` when the verifier starts and `2c-1` otherwise. -/
theorem verifierMoveIndex_eq (vFirst : Bool) (c : ℕ) :
    verifierMoveIndex vFirst c = if vFirst then 2 * c else 2 * c - 1 := rfl

/-- The number of prover moves among the first `k` moves. -/
def proverMoves (vFirst : Bool) (k : ℕ) : ℕ := (List.range k).countP fun t => !moverIsV vFirst t

/-- Prover moves are counted among the positions below the move budget. -/
theorem proverMoves_eq (vFirst : Bool) (k : ℕ) :
    proverMoves vFirst k = (List.range k).countP fun t => !moverIsV vFirst t := rfl

/-- The mover pattern has period `2`. -/
theorem moverIsV_two_mul_add (vFirst : Bool) (m t : ℕ) :
    moverIsV vFirst (2 * m + t) = moverIsV vFirst t := by
  cases vFirst <;> simp [moverIsV_true, moverIsV_false]

/-- The number of verifier moves among the first `g` moves. -/
theorem countP_moverIsV (vFirst : Bool) (g : ℕ) :
    (List.range g).countP (fun t => moverIsV vFirst t) =
      if vFirst then (g + 1) / 2 else g / 2 := by
  induction g with
  | zero => cases vFirst <;> simp
  | succ g ih =>
    rw [List.range_succ, List.countP_append, ih]
    cases vFirst <;> simp [moverIsV_true, moverIsV_false] <;> split_ifs <;> omega

/-- The number of prover moves among the first `g` moves. -/
theorem countP_not_moverIsV (vFirst : Bool) (g : ℕ) :
    (List.range g).countP (fun t => !moverIsV vFirst t) =
      if vFirst then g / 2 else (g + 1) / 2 := by
  induction g with
  | zero => cases vFirst <;> simp
  | succ g ih =>
    rw [List.range_succ, List.countP_append, ih]
    cases vFirst <;> simp [moverIsV_true, moverIsV_false] <;> split_ifs <;> omega

/-- After `g` moves the prover has received one message per verifier move. -/
theorem exec_fst_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (g : ℕ) :
    (exec P V vFirst x zP zV rP rV g).1.length =
      (List.range g).countP (fun t => moverIsV vFirst t) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [exec_succ, List.range_succ, List.countP_append]
    by_cases h : moverIsV vFirst g = true <;> simp [h, ih]

/-- After `g` moves the verifier has received one message per prover move. -/
theorem exec_snd_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (g : ℕ) :
    (exec P V vFirst x zP zV rP rV g).2.length =
      (List.range g).countP (fun t => !moverIsV vFirst t) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [exec_succ, List.range_succ, List.countP_append]
    by_cases h : moverIsV vFirst g = true <;> simp [h, ih]

/-- **The prover knows the global move**: when it moves at move `g`, the number of messages it
has received gives `g` back. -/
theorem proverMoveIndex_exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g : ℕ) (hg : moverIsV vFirst g = false) :
    proverMoveIndex vFirst (exec P V vFirst x zP zV rP rV g).1.length = g := by
  rw [exec_fst_length, countP_moverIsV]
  cases vFirst <;> simp [moverIsV_true, moverIsV_false, proverMoveIndex] at hg ⊢ <;> omega

/-- **The verifier knows the global move**: when it moves at move `g`, the number of messages
it has received gives `g` back. -/
theorem verifierMoveIndex_exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g : ℕ) (hg : moverIsV vFirst g = true) :
    verifierMoveIndex vFirst (exec P V vFirst x zP zV rP rV g).2.length = g := by
  rw [exec_snd_length, countP_not_moverIsV]
  cases vFirst <;> simp [moverIsV_true, moverIsV_false, verifierMoveIndex] at hg ⊢ <;> omega

end Composability

open Composability

namespace Protocol

/-! ### The sequential repetition -/

/-- The prover `P_Q`: at a real position of phase `j`, `π.P` on the coin slice `j` and the
messages received in phase `j`; at a filler position, `[]`. Its coins are `Q` copies of
`π.P`'s. -/
@[simps (config := { isSimp := false }) coins next]
def seqProver (π : Protocol) (Q : PolyExpr) : Strategy where
  next x y r hist :=
    if proverMoveIndex π.verifierFirst hist.length % (2 * π.rounds.eval x.length) <
        π.rounds.eval x.length then
      π.P.next x y
        (coinBlock (π.P.coinLen x.length)
          (proverMoveIndex π.verifierFirst hist.length / (2 * π.rounds.eval x.length)) r)
        (hist.drop (proverMoveIndex π.verifierFirst hist.length /
          (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
    else []
  coins := .mul Q π.P.coins

/-- The verdict of `V_Q` on its complete history: `[true]` iff for every phase `j < Q`, `π.V`
on the coin slice `j` and the real messages of phase `j` outputs `[true]`. -/
def seqVerdict (π : Protocol) (Q : ℕ) (x z r : List Bool) (hist : List (List Bool)) :
    List Bool :=
  if (List.range Q).all (fun j => decide (π.V.next x z (coinBlock (π.V.coinLen x.length) j r)
      ((hist.drop (j * π.rounds.eval x.length)).take
        (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true]))
  then [true] else [false]

/-- The repeated verdict is true exactly when every phase's original verdict is true. -/
theorem seqVerdict_eq (π : Protocol) (Q : ℕ) (x z r : List Bool)
    (hist : List (List Bool)) :
    seqVerdict π Q x z r hist =
      if (List.range Q).all (fun j => decide
        (π.V.next x z (coinBlock (π.V.coinLen x.length) j r)
          ((hist.drop (j * π.rounds.eval x.length)).take
            (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true]))
      then [true] else [false] := rfl

/-- The verifier `V_Q`: on its complete history (`Q · k` messages received) its verdict
(`seqVerdict`); otherwise, at a real position of phase `j`, `π.V` on the coin slice `j` and the
messages received in phase `j`; at a filler position, `[]`. Its coins are `Q` copies of
`π.V`'s. -/
@[simps (config := { isSimp := false }) coins next]
def seqVerifier (π : Protocol) (Q : PolyExpr) : Strategy where
  next x z r hist :=
    if hist.length = Q.eval x.length * π.rounds.eval x.length then
      seqVerdict π (Q.eval x.length) x z r hist
    else if verifierMoveIndex π.verifierFirst hist.length % (2 * π.rounds.eval x.length) <
        π.rounds.eval x.length then
      π.V.next x z
        (coinBlock (π.V.coinLen x.length)
          (verifierMoveIndex π.verifierFirst hist.length / (2 * π.rounds.eval x.length)) r)
        (hist.drop (verifierMoveIndex π.verifierFirst hist.length /
          (2 * π.rounds.eval x.length) * π.rounds.eval x.length))
    else []
  coins := .mul Q π.V.coins

/-- **The `Q`-fold sequential repetition** of `π` [PS10, Theorem 175.1, `(P_Q, V_Q)`]:
`Q(|x|)` phases of `2 · rounds(|x|)` moves, each running `π` on `x` with fresh coins and then
filler moves. -/
@[simps (config := { isSimp := false }) P V rounds verifierFirst]
def seqRep (π : Protocol) (Q : PolyExpr) : Protocol where
  P := π.seqProver Q
  V := π.seqVerifier Q
  rounds := .mul Q (.mul (.const 2) π.rounds)
  verifierFirst := π.verifierFirst

/-- The number of moves of the repetition. -/
theorem seqRep_rounds_eval (π : Protocol) (Q : PolyExpr) (n : ℕ) :
    (π.seqRep Q).rounds.eval n = 2 * π.rounds.eval n * Q.eval n := by
  simp [seqRep, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- **Phase `j` of an honest execution of the repetition is an execution of `π`** with the coin
slices `j`: after the `j` earlier phases and the `k` real moves of phase `j`, the messages each
party received in phase `j` are those it receives in `π` with those coins.

**Proof sketch.** Induction on the position `t ≤ k` in phase `j`, for the move `2kj + t`.
1. At `t = 0` each party has received exactly `jk` messages (`exec_fst_length`,
   `countP_moverIsV` with `2kj` moves), so both dropped lists are empty.
2. At a move `2kj + t` with `t < k`, the mover is `π`'s mover at `t` (`moverIsV_two_mul_add`).
   The mover recovers `2kj + t` from its message count (`proverMoveIndex_exec`,
   `verifierMoveIndex_exec`). So it computes `j` and `t < k`, and it runs `π`'s strategy on the
   slice `j` and on the messages of phase `j`, which equal `π`'s by the induction hypothesis.
   `V_Q` is not at its verdict: it has received fewer than `jk + k ≤ Qk` messages.
3. Appending the same message on both sides preserves the equation (`List.drop_append_of_le`,
   as at least `jk` messages precede it). -/
theorem seqRep_exec_phase (π : Protocol) (Q : PolyExpr) (x y z rP rV : List Bool) {j : ℕ}
    (hj : j < Q.eval x.length) :
    (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
        (2 * π.rounds.eval x.length * j + π.rounds.eval x.length)).1.drop
          (j * π.rounds.eval x.length) =
      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).1 ∧
    (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
        (2 * π.rounds.eval x.length * j + π.rounds.eval x.length)).2.drop
          (j * π.rounds.eval x.length) =
      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
  set k := π.rounds.eval x.length with hk
  set vF := π.verifierFirst with hvF
  set sP := coinBlock (π.P.coinLen x.length) j rP
  set sV := coinBlock (π.V.coinLen x.length) j rV
  have hjk : (j + 1) * k ≤ Q.eval x.length * k := Nat.mul_le_mul_right _ hj
  have hjk' : (j + 1) * k = j * k + k := by ring
  have h2 : 2 * k * j = 2 * (j * k) := by ring
  suffices key : ∀ t, t ≤ k →
      (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).1.drop (j * k) =
        (exec π.P π.V vF x y z sP sV t).1 ∧
      (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).2.drop (j * k) =
        (exec π.P π.V vF x y z sP sV t).2 from key k le_rfl
  intro t
  induction t with
  | zero =>
    intro _
    constructor
    · rw [List.drop_eq_nil_of_le]
      · rfl
      · rw [exec_fst_length, countP_moverIsV]
        cases vF <;> simp <;> omega
    · rw [List.drop_eq_nil_of_le]
      · rfl
      · rw [exec_snd_length, countP_not_moverIsV]
        cases vF <;> simp <;> omega
  | succ t ih =>
    intro ht
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    have htk : t < k := by omega
    have hl₁ : (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).1.length =
        j * k + (exec π.P π.V vF x y z sP sV t).1.length := by
      rw [exec_fst_length, exec_fst_length, countP_moverIsV, countP_moverIsV]
      cases vF <;> simp <;> omega
    have hl₂ : (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).2.length =
        j * k + (exec π.P π.V vF x y z sP sV t).2.length := by
      rw [exec_snd_length, exec_snd_length, countP_not_moverIsV, countP_not_moverIsV]
      cases vF <;> simp <;> omega
    have hle₂ : (exec π.P π.V vF x y z sP sV t).2.length ≤ t := by
      rw [exec_snd_length]
      exact (List.countP_le_length).trans (by simp)
    have hmv : moverIsV vF (2 * k * j + t) = moverIsV vF t := by
      rw [show 2 * k * j + t = 2 * (k * j) + t by ring]
      exact moverIsV_two_mul_add _ _ _
    have hmod : (2 * k * j + t) % (2 * k) = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hdiv : (2 * k * j + t) / (2 * k) = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    rw [show 2 * k * j + (t + 1) = (2 * k * j + t) + 1 by ring, exec_succ, exec_succ]
    simp only [hmv]
    by_cases hV : moverIsV vF t = true
    · simp only [hV, if_true]
      refine ⟨?_, ih₂⟩
      rw [List.drop_append_of_le_length (by omega), ih₁]
      congr 2
      have hidx := verifierMoveIndex_exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV
        (2 * k * j + t) (by rw [hmv]; exact hV)
      have hne : (exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV (2 * k * j + t)).2.length ≠
          Q.eval x.length * k := by omega
      show (π.seqVerifier Q).next x z rV _ = _
      simp only [seqVerifier, ← hk, ← hvF]
      rw [if_neg hne, hidx, hmod, if_pos htk, hdiv, ih₂]
    · simp only [Bool.not_eq_true] at hV
      simp only [hV, Bool.false_eq_true, if_false]
      refine ⟨ih₁, ?_⟩
      rw [List.drop_append_of_le_length (by omega), ih₂]
      congr 2
      have hidx := proverMoveIndex_exec (π.seqRep Q).P (π.seqRep Q).V vF x y z rP rV
        (2 * k * j + t) (by rw [hmv]; exact hV)
      show (π.seqProver Q).next x y rP _ = _
      simp only [seqProver, ← hk, ← hvF]
      rw [hidx, hmod, if_pos htk, hdiv, ih₁]

end Protocol

/-! ### Theorem 175.1 -/

variable {π : Protocol} {R : List Bool → List Bool → Prop}

/-- **Theorem 175.1, computational case** [PS10, Theorem 175.1]: the sequential repetition of a
zero-knowledge protocol with a bounded prover is zero-knowledge.

**Proof sketch** ([Gol01, §4.3.4], with the hybrids made explicit).
1. Given an efficient `V_Q*`, let `V*` be the verifier of one run of `π` whose auxiliary input
   is `⟨z, r, m̄₁, …, m̄_i⟩`: it runs `V_Q*` on the random tape `r`, feeds it the messages
   `m̄₁, …, m̄_i` of the first `i` phases (fillers `[]` included), and plays phase `i + 1` as
   `V_Q*` does. It is efficient, and it reads `i` from its auxiliary input. Let `S` be its
   simulator (`ZK π R`).
2. `S_Q(x, z)`: pick `r`; for `i = 0, …, Q − 1` run `S(x, ⟨z, r, m̄₁, …, m̄_i⟩)` and take the
   prover's messages of its output as `m̄_{i+1}`. Messages longer than `B(|x|)` are truncated;
   real ones never are (`ProverBounded`). Output `V_Q*`'s view `(x, z, r, m̄₁ … m̄_Q)`. The
   auxiliary inputs stay below `|z| + |r| + Q · k · (2B + 2)`, a polynomial `Lz'` in `|x|`, so
   `S_Q` is a strict PPT.
3. Hybrid `H_i`: the first `i` phases real, the rest simulated as in `S_Q`. `H_Q` is the real
   view, and `H_0` is `S_Q`'s output. A distinguisher between `H_i` and `H_{i+1}` gives one
   between the real and the simulated phase `i + 1`, with the first `i` real phases as auxiliary
   input (of length at most `Lz'`). It reads `i` and those phases from the sample, and completes
   phases `i + 2, …` with `S`. So it does not need the possibly inefficient prover.
4. By `ZK π R` at the bound `Lz'` the advantage is at most `Q(|x|) · ε(|x|)`, which is
   negligible. -/
theorem ZK.seqRep {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr) :
    ZK (π.seqRep Q) R := by
  sorry

/-- **Theorem 175.1, statistical case**: statistical error `δ` composes to `Q · δ`, under the
same prover bound.

**Proof sketch.** As for `ZK.seqRep`, with statistical distance instead of a distinguisher.
Each hybrid step changes one phase from real to simulated for a fixed auxiliary input, at
distance at most `δ(|x|)` (`StatZK π R δ` holds for every auxiliary input). The common
post-processing, which completes the later phases and truncates the messages, does not increase
the distance. Summing the `Q(|x|)` steps by the triangle inequality gives `Q(|x|) · δ(|x|)`. -/
theorem StatZK.seqRep {B : PolyExpr} {δ : ℕ → ℝ} (h : StatZK π R δ)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * δ n) := by
  sorry

/-- **Theorem 175.1, perfect case**: the sequential repetition of a perfect zero-knowledge
protocol with a bounded prover is perfect zero-knowledge (`StatZK.seqRep` at `δ = 0`). -/
theorem PerfectZK.seqRep {B : PolyExpr} (h : PerfectZK π R) (hB : π.ProverBounded R B)
    (Q : PolyExpr) : PerfectZK (π.seqRep Q) R := by
  apply perfectZK_iff.mpr
  simpa only [mul_zero] using StatZK.seqRep h.statZK hB Q

/-- **Theorem 175.1, perfect case with aborting simulators** [PS10, Theorem 175.1]
[Gol01, Definition 4.3.1 and §4.3.4]: with the text's expected-polynomial-time simulators
truncated per ruling G02-#4, the repetition is statistical zero-knowledge with error
`Q(n) · 2^{-n}`.

**Proof sketch.** First apply `PerfectZKAbort.statZK`: retry the aborting simulator on `n = |x|`
fresh coin blocks and keep its first non-aborting output. The probability that all trials
abort is at most `2^{-n}`, and on success the output has the real view's law. Then apply
`StatZK.seqRep` [Gol01, §4.3.4], which bounds the statistical distance of the `Q(n)` phases by
the sum of their errors, `Q(n) · 2^{-n}`. -/
theorem PerfectZKAbort.seqRep {B : PolyExpr} (h : PerfectZKAbort π R)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * (1 / 2 : ℝ) ^ n) := by
  simpa only [one_div] using StatZK.seqRep h.statZK hB Q

/-- **The repetition of an interactive proof is an interactive proof** [PS10, Theorem 175.1,
"`(P_Q, V_Q)` is an interactive proof"], when every input length has at least one phase.

**Proof sketch.**
1. *Efficiency:* `V_Q` runs `π.V`'s machine on a coin slice and a suffix of its history, or
   `Q(|x|)` times for its verdict, so it is computed by a uniform machine with coins `Q · coins`.
2. *Completeness:* with the witness `y` of `π`, each phase is an honest execution of `π` with
   independent uniform coin slices (`seqRep_exec_phase`), accepted with probability one, so
   every phase accepts.
3. *Soundness:* for `x ∉ L` and a prover `P'`, phase `0` is an execution of `P'` against `π.V`
   on the coin slice `0`, which is uniform. Here the dropped prefix is empty, so
   `seqRep_exec_phase`'s argument applies with `P'` in place of `π.P`. Phase `0`'s verdict is
   `[false]` with probability `> 1 − ε(|x|)`, and then `V_Q` outputs `[false]`. Phase `0`
   exists since `1 ≤ Q(|x|)`. -/
theorem InteractiveProof.seqRep {L : Language Bool} (h : InteractiveProof π L) (Q : PolyExpr)
    (hQ : ∀ n, 1 ≤ Q.eval n) : InteractiveProof (π.seqRep Q) L := by
  sorry

/-- **Sequential repetition multiplies the soundness error** [PS10, p. 120: the protocol "can be
repeated many times … to drive the probability of error as low as desired"; and p. 127, the
`O(n|E|)` repetitions of the 3-colouring protocol]: if `π` has soundness error `s`, its
`Q`-phase sequential repetition (which accepts iff every phase does) has soundness error
`s(|x|)^{Q(|x|)}`, with perfect completeness kept.

**Proof sketch.**
1. *Efficiency and completeness* as in `InteractiveProof.seqRep`: every phase of the honest
   execution is an honest execution of `π` with independent coin slices
   (`seqRep_exec_phase`), accepted with probability one.
2. *Soundness:* fix `x ∉ L`, a prover `P'` and `z`. Condition on the prover's coins and on the
   transcript of phases `0, …, j − 1`. Phase `j` is then an execution, against `π.V` on a fresh
   uniform coin slice, of the prover strategy that `P'` induces with that prefix hard-wired (the
   verifier reads only phase `j`'s messages). By `π`'s soundness it accepts with probability at
   most `s(|x|)`, whatever the prefix. By induction on `j`, all `Q(|x|)` phases accept with
   probability at most `s(|x|)^{Q(|x|)}`, so `V_Q` outputs `[false]` with probability at least
   `1 − s(|x|)^{Q(|x|)}`. -/
theorem InteractiveProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ} (h : InteractiveProofErr π L s)
    (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    InteractiveProofErr (π.seqRep Q) L (fun n => s n ^ Q.eval n) := by
  sorry

/-- **The efficient-prover form**: the sequential repetition of an interactive proof with an
efficient prover and soundness error `s` is one with soundness error `s^Q`; the repeated prover
is efficient and complete for every witness.

**Proof sketch.** `InteractiveProofErr.seqRep` for the proof system; `P_Q` runs `π.P`'s machine
on its coin slice and a suffix of its history, so a uniform machine computes it; completeness for
every witness phase by phase, as in `InteractiveProof.seqRep`. -/
theorem EfficientProverProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ}
    (h : EfficientProverProofErr π L R s) (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    EfficientProverProofErr (π.seqRep Q) L R (fun n => s n ^ Q.eval n) := by
  sorry

end TCSlib.Cryptography
