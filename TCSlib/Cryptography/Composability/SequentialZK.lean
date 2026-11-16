/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.Composability.SequentialZK.Advice
import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalAdvice
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalHybrid
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalPhaseBound
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalTransfer
import TCSlib.Cryptography.Composability.SequentialZK.Congruence
import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
import TCSlib.Cryptography.Composability.SequentialZK.Efficiency
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
import TCSlib.Cryptography.Composability.SequentialZK.ErrSoundness
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.HybridRecursion
import TCSlib.Cryptography.Composability.SequentialZK.Normalization
import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.Phases
import TCSlib.Cryptography.Composability.SequentialZK.PrefixFolds
import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers
import TCSlib.Cryptography.Composability.SequentialZK.RealPhases
import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds
import TCSlib.Cryptography.Composability.SequentialZK.ReductionAdvantage
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedSoundness
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedVerifier
import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine
import TCSlib.Cryptography.Composability.SequentialZK.Soundness
import TCSlib.Cryptography.Composability.SequentialZK.Statistical
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPostprocess
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalTransfer
import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
import TCSlib.Cryptography.Composability.SequentialZK.VerifierPrefix
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition of zero-knowledge proofs

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
- **Strict-PPT simulators and bounded abort retries** (ruling G02-#4, D8): zero-knowledge
  composes to zero-knowledge, and statistical error `δ` composes to `Q · δ`. The formal
  `PerfectZKAbort` premise is [Gol01, Definition 4.3.1]'s strict-PPT aborting formulation:
  abort probability at most `1/2`, and the exact real-view law conditioned on success.
  `PerfectZKAbort.statZK` runs this simulator on `n = |x|` independent fresh coin blocks,
  keeping the first non-aborting output. All retries abort with probability at most `2^{-n}`,
  giving statistical error `2^{-n}`; composition gives `Q(n) · 2^{-n}`. Each retry is already
  strict PPT. [PS10]'s expected-polynomial-time wording is a separate source convention;
  this bounded-retry argument does not assert that arbitrary expected-time truncation
  preserves an exact conditional output law.
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

## Contents

* `SequentialZK.Advice`: uniform finite selectors.
* `SequentialZK.BoundedMetadata`: finite bounded phase advice.
* `SequentialZK.ComputationalAdvice`: uniform negligible selectors.
* `SequentialZK.ComputationalHybrid`: conditional computational gaps and endpoints.
* `SequentialZK.ComputationalPhaseBound`: a common negligible phase bound.
* `SequentialZK.ComputationalReduction`: efficient advised continuation machines.
* `SequentialZK.ComputationalTransfer`: computational zero-knowledge transfer.
* `SequentialZK.Congruence`: reached-history execution congruence.
* `SequentialZK.ContinuationProbability`: continuation acceptance and drift.
* `SequentialZK.Efficiency`: phase and verdict machines.
* `SequentialZK.EndpointSampling`: coin and view endpoint equivalences.
* `SequentialZK.ErrSoundness`: acceptance bounds from soundness.
* `SequentialZK.ExecutionBounds`: bounded real messages.
* `SequentialZK.HybridRecursion`: conditional finite hybrid bounds.
* `SequentialZK.Normalization`: bounded message slots.
* `SequentialZK.NormalizationMachine`: normalization machines.
* `SequentialZK.NormalizedStep`: one normalized phase comparison.
* `SequentialZK.PaddedProverSpec`: the repeated-prover contract.
* `SequentialZK.PhaseView`: canonical view validation.
* `SequentialZK.Phases`: fixed-prefix phase executions.
* `SequentialZK.PrefixFolds`: typed phase-prefix samplers.
* `SequentialZK.PrefixLaws`: phase-fold recursion equations.
* `SequentialZK.ProofTransfers`: bounded completeness transfer.
* `SequentialZK.RealPhases`: real and filler phase endpoints.
* `SequentialZK.RealPrefixBounds`: bounded actual real prefixes.
* `SequentialZK.ReductionAdvantage`: typed reduction comparisons.
* `SequentialZK.RepeatedSoundness`: the exact power soundness bound.
* `SequentialZK.RepeatedVerifier`: the repeated-verifier contract.
* `SequentialZK.SimulatorMachine`: the uniform normalized simulator.
* `SequentialZK.Soundness`: execution prefixes and adaptive probability.
* `SequentialZK.Statistical`: averaging and finite chains.
* `SequentialZK.StatisticalPostprocess`: statistical mapping and marginalization.
* `SequentialZK.StatisticalPrefix`: normalized prefix comparisons.
* `SequentialZK.StatisticalRecursion`: linear error accumulation.
* `SequentialZK.StatisticalTransfer`: statistical zero-knowledge transfer.
* `SequentialZK.SuffixLaws`: normalized suffix equations.
* `SequentialZK.SuffixMachine`: strict-PPT normalized suffix simulation.
* `SequentialZK.VerifierPrefix`: prefix tape dependence.
* `SequentialZK.WrappedVerifier`: the deterministic phase verifier.

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
* `ZK.seqRep` (Thm 175.1, proved): computational zero knowledge composes sequentially.
* `StatZK.seqRep` (proved): statistical error composes as `Q · δ`;
  `PerfectZK.seqRep` is proved from it at zero error.
* `PerfectZKAbort.seqRep`: the aborting case, derived from `PerfectZKAbort.statZK` and
  `StatZK.seqRep`, with error `Q(n) · 2^{-n}`.
* `InteractiveProof.seqRep` (proved): sequential repetition with at least one phase preserves
  interactive proofs, using the same negligible soundness bound.
* `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep` (proved): sequential
  repetition multiplies the soundness error, `s ↦ s^Q` (ruling G3-7d, for the text's form of
  Thm 124.1).

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

/-- For `P,V,vFirst,x,zP,zV,rP,rV,k,j`, each party has received exactly `j*k` messages
at move `2*k*j`: both components of `exec P V vFirst x zP zV rP rV (2*k*j)` have length
`j*k`. [PS10, Theorem 175.1, padded-phase boundaries].
`(exec P V vFirst x zP zV rP rV (2 * k * j)).1.length = j * k ∧ (exec P V vFirst x zP zV rP rV (2 *
k * j)).2.length = j * k`. -/
theorem exec_boundary_lengths (P V : Strategy) (vFirst : Bool)
    (x zP zV rP rV : List Bool) (k j : ℕ) :
    (exec P V vFirst x zP zV rP rV (2 * k * j)).1.length = j * k ∧
      (exec P V vFirst x zP zV rP rV (2 * k * j)).2.length = j * k := by
  constructor
  · rw [exec_fst_length, countP_moverIsV,
      show 2 * k * j = 2 * (j * k) by ring]
    cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · rw [exec_snd_length, countP_not_moverIsV,
      show 2 * k * j = 2 * (j * k) by ring]
    cases vFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

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

/-- The repeated prover keeps the message bound: `π.ProverBounded R B` implies
`(π.seqRep Q).ProverBounded R B`, since every real reply is an original reply and every
filler reply is empty. [PS10, Theorem 175.1]. -/
theorem ProverBounded.seqRep {π : Protocol} {R : List Bool → List Bool → Prop}
    {B : PolyExpr} (hB : π.ProverBounded R B) (Q : PolyExpr) :
    (π.seqRep Q).ProverBounded R B := by
  rw [proverBounded_iff] at hB ⊢
  intro x y r hist hxy
  rw [seqRep_P, seqProver_next]
  split_ifs
  · exact hB x y _ _ hxy
  · exact Nat.zero_le _

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
      · exact (congrArg Prod.fst (exec_zero π.P π.V vF x y z sP sV)).symm
      · rw [exec_fst_length, countP_moverIsV]
        cases vF <;> simp <;> omega
    · rw [List.drop_eq_nil_of_le]
      · exact (congrArg Prod.snd (exec_zero π.P π.V vF x y z sP sV)).symm
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

/-- Up to `t ≤ π.rounds.eval |x|`, the repeated verifier against any prover `P'` has the
same execution as the original verifier on coin block zero, provided `1 ≤ Q.eval |x|`.

**Proof sketch.** Induct on the real move index. The received history has length at most
that index, so it cannot trigger the repeated verdict. At a verifier move the recovered
index is the move index, its phase is zero, and its residue is the index itself. Thus the
same original verifier reply is appended. Prover moves agree because their histories agree.
-/
theorem seqVerifier_exec_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z rP rV : List Bool) (hQ : 1 ≤ Q.eval x.length) {t : ℕ}
    (ht : t ≤ π.rounds.eval x.length) :
    exec P' (π.seqVerifier Q) π.verifierFirst x y z rP rV t =
      exec P' π.V π.verifierFirst x y z rP (coinBlock (π.V.coinLen x.length) 0 rV) t := by
  -- Induct through the first phase, keeping both received histories synchronized.
  induction t with
  | zero => rw [exec_zero, exec_zero]
  | succ t ih =>
    have htk : t < π.rounds.eval x.length := by omega
    rw [exec_succ, exec_succ, ih (by omega)]
    by_cases hm : moverIsV π.verifierFirst t = true
    · simp only [hm, if_true]
      -- The active move count excludes the aggregate-verdict branch in this prefix.
      have hl := exec_length P' π.V π.verifierFirst x y z rP
        (coinBlock (π.V.coinLen x.length) 0 rV) t
      have hkQ : π.rounds.eval x.length ≤ Q.eval x.length * π.rounds.eval x.length := by
        simpa only [one_mul] using Nat.mul_le_mul_right (π.rounds.eval x.length) hQ
      have hne : (exec P' π.V π.verifierFirst x y z rP
          (coinBlock (π.V.coinLen x.length) 0 rV) t).2.length ≠
            Q.eval x.length * π.rounds.eval x.length := by omega
      have hidx := verifierMoveIndex_exec P' π.V π.verifierFirst x y z rP
        (coinBlock (π.V.coinLen x.length) 0 rV) t hm
      have hn : (π.seqVerifier Q).next x z rV
          (exec P' π.V π.verifierFirst x y z rP
            (coinBlock (π.V.coinLen x.length) 0 rV) t).2 =
          π.V.next x z (coinBlock (π.V.coinLen x.length) 0 rV)
            (exec P' π.V π.verifierFirst x y z rP
              (coinBlock (π.V.coinLen x.length) 0 rV) t).2 := by
        rw [seqVerifier_next, if_neg hne, hidx,
          Nat.mod_eq_of_lt (by omega), if_pos htk, Nat.div_eq_of_lt (by omega),
          Nat.zero_mul, List.drop_zero]
      rw [hn]
    · simp only [hm, Bool.false_eq_true, if_false]

/-- The repeated output is the aggregate verdict on the final received history:
`(π.seqRep Q).outV P' x y z r = π.seqVerdict (Q.eval |x|) x z (List.ofFn r.2) hist`,
where `hist` is the verifier component of the repeated transcript.

**Proof sketch.** There are exactly `Q(|x|) · k` prover moves in the even-length repeated
execution. This is the terminal-history test in the repeated verifier, so its terminal
branch computes the aggregate verdict. -/
theorem seqRep_outV_eq (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (π.seqRep Q).ExecCoins P' x) :
    (π.seqRep Q).outV P' x y z r =
      π.seqVerdict (Q.eval x.length) x z (List.ofFn r.2)
        ((π.seqRep Q).transcriptWith P' x y z r).2 := by
  have hl : ((π.seqRep Q).transcriptWith P' x y z r).2.length =
      Q.eval x.length * π.rounds.eval x.length := by
    rw [transcriptWith_eq, exec_snd_length, countP_not_moverIsV,
      seqRep_rounds_eval, seqRep_verifierFirst]
    rw [show 2 * π.rounds.eval x.length * Q.eval x.length =
      2 * (Q.eval x.length * π.rounds.eval x.length) by ring]
    cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  rw [outV_eq]
  have hn := congrArg (fun V : Strategy => V.next x z (List.ofFn r.2)
    ((π.seqRep Q).transcriptWith P' x y z r).2) (seqRep_V π Q)
  dsimp only at hn
  rw [hn, seqVerifier_next, if_pos hl]

/-- The final repeated history restricted to the real prover slots of phase `j < Q(|x|)`
is the original verifier history on coin slices `j`. [PS10, Theorem 175.1].

**Proof sketch.** The history just after the phase's real moves is a prefix of the final
history. Its length is the `j · k` slots of preceding phases plus the number of real prover
moves. Taking this prefix and dropping the preceding phases recovers the phase reader.
-/
theorem seqRep_exec_phase_take (π : Protocol) (Q : PolyExpr) (x y z rP rV : List Bool)
    {j : ℕ} (hj : j < Q.eval x.length) :
    ((exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (2 * π.rounds.eval x.length * Q.eval x.length)).2.drop
        (j * π.rounds.eval x.length)).take
          (proverMoves π.verifierFirst (π.rounds.eval x.length)) =
      (exec π.P π.V π.verifierFirst x y z (coinBlock (π.P.coinLen x.length) j rP)
        (coinBlock (π.V.coinLen x.length) j rV) (π.rounds.eval x.length)).2 := by
  let k := π.rounds.eval x.length
  have hjk := Nat.mul_le_mul_right k hj
  have hle : 2 * k * j + k ≤ 2 * k * Q.eval x.length := by
    have hscaled := Nat.mul_le_mul_left 2 hjk
    rw [show 2 * ((j + 1) * k) = 2 * k * j + 2 * k by ring,
      show 2 * (Q.eval x.length * k) = 2 * k * Q.eval x.length by ring] at hscaled
    omega
  have hl : (exec (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (2 * k * j + k)).2.length = j * k + proverMoves π.verifierFirst k := by
    rw [exec_snd_length, countP_not_moverIsV, proverMoves_eq, countP_not_moverIsV]
    rw [show 2 * k * j + k = 2 * (j * k) + k by ring]
    cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  have hp := exec_snd_take (π.seqRep Q).P (π.seqRep Q).V π.verifierFirst x y z rP rV
    (2 * k * j + k) (2 * k * Q.eval x.length - (2 * k * j + k))
  rw [Nat.add_sub_of_le hle, hl] at hp
  rw [List.take_drop, hp]
  exact (seqRep_exec_phase π Q x y z rP rV hj).2

/-- Perfect completeness on `x, y, z` is preserved by every number of sequential phases:
if `Pr[π.outV π.P x y z = [true]] = 1`, then
`Pr[(π.seqRep Q).outV (π.seqRep Q).P x y z = [true]] = 1`.
[PS10, Theorem 175.1].

**Proof sketch.** Probability one on the finite coin space means every original coin pair
accepts. For each repeated coin pair and phase, its coin slices have the original lengths.
The phase-history reader therefore identifies its verdict with an accepting original run.
All phase tests are true, so the aggregate output is true, including an empty phase list.
-/
theorem seqRep_complete (π : Protocol) (Q : PolyExpr) (x y z : List Bool)
    (hc : uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
    uprob (fun r : (π.seqRep Q).ExecCoins (π.seqRep Q).P x =>
      (π.seqRep Q).outV (π.seqRep Q).P x y z r = [true]) = 1 := by
  -- Reduce completeness to pointwise acceptance on every repeated coin tape.
  apply HardcoreBit.uprob_eq_one_of_forall
  intro r
  rw [seqRep_outV_eq, seqVerdict_eq]
  have hall : (List.range (Q.eval x.length)).all (fun j => decide
      (π.V.next x z (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2))
        ((((π.seqRep Q).transcriptWith (π.seqRep Q).P x y z r).2.drop
          (j * π.rounds.eval x.length)).take
            (proverMoves π.verifierFirst (π.rounds.eval x.length))) = [true])) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hjQ : j < Q.eval x.length := List.mem_range.mp hj
    apply decide_eq_true
    rw [transcriptWith_eq, seqRep_verifierFirst, seqRep_rounds_eval,
      seqRep_exec_phase_take π Q x y z (List.ofFn r.1) (List.ofFn r.2) hjQ]
    -- Each phase uses original-length tapes, so the base acceptance fact applies.
    have hlP : (List.ofFn r.1).length = Q.eval x.length * π.P.coinLen x.length := by
      rw [List.length_ofFn, Strategy.coinLen_eq, seqRep_P, seqProver_coins,
        PolyExpr.eval_mul, Strategy.coinLen_eq]
    have hlV : (List.ofFn r.2).length = Q.eval x.length * π.V.coinLen x.length := by
      rw [List.length_ofFn, Strategy.coinLen_eq, seqRep_V, seqVerifier_coins,
        PolyExpr.eval_mul, Strategy.coinLen_eq]
    have hbP : (coinBlock (π.P.coinLen x.length) j (List.ofFn r.1)).length =
        π.P.coinLen x.length := length_coinBlock (by
      rw [hlP]; exact Nat.mul_le_mul_right _ hjQ)
    have hbV : (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2)).length =
        π.V.coinLen x.length := length_coinBlock (by
      rw [hlV]; exact Nat.mul_le_mul_right _ hjQ)
    have hrun := HardcoreBit.forall_of_uprob_eq_one hc
      (padFin (π.P.coinLen x.length) (coinBlock (π.P.coinLen x.length) j (List.ofFn r.1)),
       padFin (π.V.coinLen x.length) (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2)))
    rw [outV_eq, transcriptWith_eq, ofFn_padFin_of_length hbP,
      ofFn_padFin_of_length hbV] at hrun
    exact hrun
  rw [hall]
  rfl

/-- If the original verifier rejects phase zero against `P'`, then the repeated verifier
rejects the same repeated tape, when `1 ≤ Q.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** The first real phase agrees with the original verifier on coin block zero.
Its prover-message history is the initial segment of the final history. Rejection therefore
makes the phase-zero test in the aggregate conjunction false, forcing the repeated output
to be `[false]`. -/
theorem seqRep_reject_of_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (π.seqRep Q).ExecCoins P' x) (hQ : 1 ≤ Q.eval x.length)
    (hr : π.V.next x z (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2))
      (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
        (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2))
        (π.rounds.eval x.length)).2 = [false]) :
    (π.seqRep Q).outV P' x y z r = [false] := by
  -- Compare the first real phase with its prefix in the complete transcript.
  let k := π.rounds.eval x.length
  have hkQ : k ≤ Q.eval x.length * k := by
    simpa only [one_mul] using Nat.mul_le_mul_right k hQ
  have hle : k ≤ 2 * k * Q.eval x.length := by
    have hscaled := Nat.mul_le_mul_left 2 hkQ
    rw [show 2 * (Q.eval x.length * k) = 2 * k * Q.eval x.length by ring] at hscaled
    omega
  have hp := exec_snd_take P' (π.seqVerifier Q) π.verifierFirst x y z
    (List.ofFn r.1) (List.ofFn r.2) k (2 * k * Q.eval x.length - k)
  rw [Nat.add_sub_of_le hle,
    seqVerifier_exec_first π Q P' x y z (List.ofFn r.1) (List.ofFn r.2) hQ le_rfl] at hp
  have hl : (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
      (coinBlock (π.V.coinLen x.length) 0 (List.ofFn r.2)) k).2.length =
        proverMoves π.verifierFirst k := by
    rw [exec_snd_length, proverMoves_eq]
  rw [hl] at hp
  rw [seqRep_outV_eq, seqVerdict_eq]
  -- A failed initial phase test makes the aggregate conjunction false.
  have hnot : (List.range (Q.eval x.length)).all (fun j => decide
      (π.V.next x z (coinBlock (π.V.coinLen x.length) j (List.ofFn r.2))
        ((((π.seqRep Q).transcriptWith P' x y z r).2.drop (j * k)).take
          (proverMoves π.verifierFirst k)) = [true])) ≠ true := by
    intro hall
    have hz := List.all_eq_true.mp hall 0 (List.mem_range.mpr hQ)
    simp only [Nat.zero_mul, List.drop_zero] at hz
    rw [transcriptWith_eq, seqRep_verifierFirst, seqRep_rounds_eval] at hz
    have hpV := congrArg (fun V : Strategy =>
      (exec P' V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
        (2 * k * Q.eval x.length)).2.take (proverMoves π.verifierFirst k)) (seqRep_V π Q)
    dsimp only at hpV
    rw [hpV.trans hp, hr] at hz
    contradiction
  rw [if_neg hnot]

/-- The repeated rejection probability dominates the original rejection probability on
phase zero, against the same prover `P'`, when `1 ≤ Q.eval |x|`.
[PS10, Theorem 175.1].

**Proof sketch.** Restrict the repeated verifier's uniform tape to its initial original-length
prefix; this map preserves uniformity and leaves the prover's tape unchanged. Original
rejection on this projection implies repeated rejection by the first-phase reader, so
monotonicity of probability gives the bound. -/
theorem seqRep_sound_first (π : Protocol) (Q : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (hQ : 1 ≤ Q.eval x.length) :
    uprob (fun r : π.ExecCoins P' x => π.outV P' x y z r = [false]) ≤
      uprob (fun r : (π.seqRep Q).ExecCoins P' x =>
        (π.seqRep Q).outV P' x y z r = [false]) := by
  have hlen : (π.seqRep Q).V.coinLen x.length =
      Q.eval x.length * π.V.coinLen x.length := by
    rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  have hcle : π.V.coinLen x.length ≤ (π.seqRep Q).V.coinLen x.length := by
    rw [hlen]
    simpa only [one_mul] using Nat.mul_le_mul_right (π.V.coinLen x.length) hQ
  let f : (π.seqRep Q).ExecCoins P' x → π.ExecCoins P' x :=
    fun r => (r.1, fun i => r.2 (Fin.castLE hcle i))
  have hf : HardcoreBit.PushesUniform f := HardcoreBit.pushesUniform_id.prodMap
    (HardcoreBit.pushesUniform_restrict (Fin.castLE_injective hcle))
  calc
    _ = uprob (fun r : (π.seqRep Q).ExecCoins P' x =>
        π.outV P' x y z (f r) = [false]) := (hf.uprob_eq _).symm
    _ ≤ _ := uprob_mono fun r hr => by
      apply seqRep_reject_of_first π Q P' x y z r hQ
      rw [outV_eq, transcriptWith_eq] at hr
      change π.V.next x z (List.ofFn (fun i => r.2 (Fin.castLE hcle i)))
        (exec P' π.V π.verifierFirst x y z (List.ofFn r.1)
          (List.ofFn (fun i => r.2 (Fin.castLE hcle i)))
          (π.rounds.eval x.length)).2 = [false] at hr
      rw [← take_ofFn_castLE hcle r.2] at hr
      simpa only [coinBlock_eq, Nat.zero_mul, List.drop_zero] using hr

/-- An efficient original prover gives an efficient sequential prover:
`π.P.Efficient → (π.seqProver Q).Efficient`. [PS10, Theorem 175.1]. -/
theorem seqProver_efficient (π : Protocol) (Q : PolyExpr) (hP : π.P.Efficient) :
    (π.seqProver Q).Efficient := by
  apply SeqEfficiency.phase_efficient (π.seqProver Q) π.P π.rounds π.verifierFirst hP
  intro x z r hist
  dsimp only
  rw [seqProver_next, proverMoveIndex_eq]

/-- An efficient original verifier gives an efficient sequential verifier:
`π.V.Efficient → (π.seqVerifier Q).Efficient`. [PS10, Theorem 175.1]. -/
theorem seqVerifier_efficient (π : Protocol) (Q : PolyExpr) (hV : π.V.Efficient) :
    (π.seqVerifier Q).Efficient := by
  classical
  apply SeqEfficiency.verifier_efficient (π.seqVerifier Q) π.V π.rounds Q π.verifierFirst hV
  intro x z r hist
  dsimp only
  rw [seqVerifier_next, verifierMoveIndex_eq, seqVerdict_eq, proverMoves_eq,
    countP_not_moverIsV]
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- The repeated verifier satisfies the padded-verifier equations on `x`, with
`q=Q.eval |x|` and `p=proverMoves π.verifierFirst (π.rounds.eval |x|)`.
[PS10, Theorem 175.1].

**Proof sketch.** Read the coin, round, mover and next-message fields of the construction.
The existing move-index and message-count readers give each remaining contract field.
The aggregate verdict is its published conjunction of phase tests. -/
theorem seqRep_verifierSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
    PaddedVerifierSpec π (π.seqRep Q) x (Q.eval x.length)
      (proverMoves π.verifierFirst (π.rounds.eval x.length))
      (fun z r hist => π.seqVerdict (Q.eval x.length) x z r hist) := by
  -- Expose the construction equations through the abstract verifier contract.
  refine {
    coinLen_eq := ?_
    rounds_eq := seqRep_rounds_eval π Q x.length
    first_eq := seqRep_verifierFirst π Q
    next_eq := ?_
    terminal_eq := ?_
    index_eq := ?_
    boundary_lengths := ?_
    local_length := ?_
    period := ?_
  }
  · rw [Strategy.coinLen_eq, seqRep_V, seqVerifier_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  · intro z r hist
    rw [seqRep_V, seqVerifier_next, verifierMoveIndex_eq]
  · intro z r hist
    exact seqVerdict_eq π (Q.eval x.length) x z r hist
  -- Recover active indices and phase counts through the published execution readers.
  · intro P y z rP rV t hm
    simpa only [verifierMoveIndex_eq] using
      verifierMoveIndex_exec P (π.seqRep Q).V π.verifierFirst x y z rP rV t hm
  · intro P y z rP rV j _
    exact exec_boundary_lengths P (π.seqRep Q).V π.verifierFirst x y z rP rV
      (π.rounds.eval x.length) j
  · intro P y z rP rV
    rw [exec_snd_length, proverMoves_eq]
  · intro j t
    rw [show 2 * π.rounds.eval x.length * j + t =
      2 * (π.rounds.eval x.length * j) + t by ring]
    exact moverIsV_two_mul_add _ _ _

/-- The repeated prover satisfies the padded-prover equations on `x`, with
`q=Q.eval |x|` and `p=if π.verifierFirst then k/2 else (k+1)/2`, for
`k=π.rounds.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** Read the prover's coin and reply equations. Recover actual move indices
using the existing prover index reader and obtain phase-boundary and local counts from
the published execution-length readers. The even phase length preserves the mover pattern.
-/
theorem seqRep_proverSpec (π : Protocol) (Q : PolyExpr) (x : List Bool) :
    SequentialZK.PaddedProverSpec π (π.seqRep Q) x (Q.eval x.length)
      (if π.verifierFirst then π.rounds.eval x.length / 2
        else (π.rounds.eval x.length + 1) / 2) := by
  -- Expose the prover construction and its padded execution fields.
  refine {
    prover_coinLen := ?_
    rounds_eval := seqRep_rounds_eval π Q x.length
    first := seqRep_verifierFirst π Q
    next := ?_
    prover_index := ?_
    boundary := ?_
    original_count := ?_
    real_le := ?_
    period := ?_
  }
  · rw [Strategy.coinLen_eq, seqRep_P, seqProver_coins, PolyExpr.eval_mul,
      Strategy.coinLen_eq]
  · intro y r hist
    rw [seqRep_P, seqProver_next, proverMoveIndex_eq]
  -- The same index, boundary and mover readers discharge the remaining contract.
  · intro V y z rP rV n hm
    simpa only [proverMoveIndex_eq] using
      proverMoveIndex_exec (π.seqRep Q).P V π.verifierFirst x y z rP rV n hm
  · intro V y z rP rV j
    exact exec_boundary_lengths (π.seqRep Q).P V π.verifierFirst x y z rP rV
      (π.rounds.eval x.length) j
  · intro V y z rP rV
    rw [exec_snd_length, countP_not_moverIsV]
  · cases π.verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · intro j t
    rw [show 2 * π.rounds.eval x.length * j + t =
      2 * (π.rounds.eval x.length * j) + t by ring]
    exact moverIsV_two_mul_add _ _ _

end Protocol

/-! ### Theorem 175.1 -/

variable {π : Protocol} {R : List Bool → List Bool → Prop}

/-- **Theorem 175.1, computational case** [PS10, Theorem 175.1]: the sequential repetition of a
zero-knowledge protocol with a bounded prover is zero-knowledge.

**Proof sketch** ([Gol01, §4.3.4], with the hybrids made explicit).
1. Put `n = |x|`, `k = π.rounds.eval n` and `p = proverMoves π.verifierFirst k`. Each padded
   phase contributes `p` real prover messages and `k - p` empty prover fillers to the
   verifier's received history. If `k = 0` or `Q(n) = 0`, sample the cheating verifier's tape
   and output its exact empty-history view directly.
2. Given an efficient `V_Q*`, use one deterministic efficient wrapped verifier `V*` for a
   run of `π`. Its auxiliary input contains the original `z`, the global verifier tape `r`,
   the phase index and the bounded received-prover prefix of earlier padded phases. It runs
   `V_Q*` on `r` with that prefix followed by this phase's real prover messages. Its own tape
   is empty. Only the honest prover's fillers are fixed to `[]`; no restriction is imposed
   on a cheating verifier's filler replies. Let `S` be the simulator supplied by `ZK π R`.
3. `S_Q(x, z)` samples `r` once and calls `S` with fresh coins for each phase. Normalize each
   output before extending the prefix: syntactically parse its view and message-list
   encoding, take at most `p` real prover messages, truncate each to `B(n)` bits, and pad
   missing real messages with `[]`. Use the known phase input/auxiliary data and empty
   wrapper tape as the view fields. A bad/noncanonical encoding or unexpected view fields
   maps to that canonical phase view with `p` empty real messages. Append the `k - p`
   honest-prover fillers, all `[]`, and retain only these `k` prover-message slots.
   Every real phase view is fixed by this normalization: its count is exactly `p`, its
   metadata is the known phase data, and every real prover message is bounded by `hB`.
   No assumption that simulated outputs already have a valid shape is made.
4. On every simulator tape, the accumulated prefix has at most `Q(n) * k` messages of at
   most `B(n)` bits. Its message-list encoding has length at most `Q(n) * k * (2B(n) + 2)`.
   Including the original auxiliary input, verifier tape, phase index and fixed pairing
   overhead gives a polynomial bound in `n + |z|`; for `|z| ≤ Lz(n)` choose a polynomial
   `Lz'` bounding the phase auxiliary inputs. Thus the same `S_Q` is a uniform strict PPT.
   Its final output is the canonical view with fields `(x, z, r)` and the accumulated prefix.
5. In hybrid `H_i`, the first `i` phases are real and the rest use these normalized simulated
   phases. Normalization fixes real phases, so `H_Q` is the real view and `H_0` is `S_Q`.
   Apply the same normalization and simulated-suffix computation on both sides of each
   phase comparison. A nonuniform reduction may fix a maximizing phase and bounded prefix,
   together with `x`, `z` and `r`, as polynomial-length advice; it needs neither the witness
   nor an efficient honest prover, and need not trust metadata in an arbitrary simulator
   output. By `ZK π R` at `Lz'`, summing the `Q(n)` gaps gives `Q(n) * ε(n)`, negligible. -/
theorem ZK.seqRep {B : PolyExpr} (h : ZK π R) (hB : π.ProverBounded R B) (Q : PolyExpr) :
    ZK (π.seqRep Q) R := by
  exact SequentialZK.zk_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)

/-- **Theorem 175.1, statistical case**: statistical error `δ` composes to `Q · δ`, under the
same prover bound.

**Proof sketch.** Use the same phase-shape normalization as `ZK.seqRep`: exactly
`proverMoves π.verifierFirst k` bounded real prover messages, the canonical empty prover
fillers giving `k` received slots per padded phase, and the fixed canonical fallback for a
malformed simulated view. This fixes every real phase view and bounds every simulated
prefix, so it also gives a strict-PPT simulator without an output-shape premise.
For a fixed earlier prefix, change one phase from real to simulated at distance at most
`δ(|x|)` (`StatZK π R δ` holds for every auxiliary input). The common normalization and
simulated-suffix computation do not increase statistical distance. Average over prefixes
and sum the `Q(|x|)` gaps by the triangle inequality, giving exactly `Q(|x|) · δ(|x|)`.
The empty-history construction handles `k = 0` or `Q(|x|) = 0` directly. The padded-prover
contract and split/block coin equivalences identify the two endpoint laws exactly. -/
theorem StatZK.seqRep {B : PolyExpr} {δ : ℕ → ℝ} (h : StatZK π R δ)
    (hB : π.ProverBounded R B) (Q : PolyExpr) :
    StatZK (π.seqRep Q) R (fun n => Q.eval n * δ n) := by
  exact SequentialZK.statZK_of_padded_spec h hB Q (fun x => π.seqRep_proverSpec Q x)

/-- **Theorem 175.1, perfect case**: the sequential repetition of a perfect zero-knowledge
protocol with a bounded prover is perfect zero-knowledge (`StatZK.seqRep` at `δ = 0`). -/
theorem PerfectZK.seqRep {B : PolyExpr} (h : PerfectZK π R) (hB : π.ProverBounded R B)
    (Q : PolyExpr) : PerfectZK (π.seqRep Q) R := by
  apply perfectZK_iff.mpr
  simpa only [mul_zero] using StatZK.seqRep h.statZK hB Q

/-- **Theorem 175.1, strict-PPT aborting case** [PS10, Theorem 175.1]
[Gol01, Definition 4.3.1 and §4.3.4]: the formal `PerfectZKAbort` premise gives statistical
zero-knowledge of the repetition with error `Q(n) · 2^{-n}`.

**Proof sketch.** The premise supplies a strict-PPT simulator that aborts with probability at
most `1/2` and, conditioned on success, has exactly the real view's law. First apply the proved
`PerfectZKAbort.statZK` bridge: run `n = |x|` independent retries on fresh coin blocks and keep
the first non-aborting output. The probability that all retries abort is at most `2^{-n}`;
conditioned on a retry succeeding, its output has the real view's law. This yields statistical
error `2^{-n}`. Then `StatZK.seqRep` [Gol01, §4.3.4] bounds the distance of the `Q(n)` phases by
the sum of their errors, `Q(n) · 2^{-n}`.

**Source distinction.** [PS10] uses expected-polynomial-time wording. This result instead uses
boundedly many executions of the strict-PPT aborting simulator in its formal premise; it does
not infer an exact conditional law by truncating an arbitrary expected-time simulator. -/
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
  constructor
  · rw [Protocol.seqRep_V]
    exact π.seqVerifier_efficient Q h.efficientV
  · exact SequentialZK.PaddedProverSpec.complete (fun x => π.seqRep_proverSpec Q x)
      (fun x y z hc => π.seqRep_complete Q x y z hc) h.complete
  · obtain ⟨ε, hε, hs⟩ := h.sound
    refine ⟨ε, hε, fun x hx P' z => ?_⟩
    exact (hs x hx P' z).trans_le (π.seqRep_sound_first Q P' x [] z (hQ x.length))

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
  constructor
  · rw [Protocol.seqRep_V]
    exact π.seqVerifier_efficient Q h.efficientV
  · exact SequentialZK.PaddedProverSpec.complete (fun x => π.seqRep_proverSpec Q x)
      (fun x y z hc => π.seqRep_complete Q x y z hc) h.complete
  · intro x hx P' z
    exact (π.seqRep_verifierSpec Q x).sound h hx P' z

/-- **The efficient-prover form**: the sequential repetition of an interactive proof with an
efficient prover and soundness error `s` is one with soundness error `s^Q`; the repeated prover
is efficient and complete for every witness.

**Proof sketch.** `InteractiveProofErr.seqRep` for the proof system; `P_Q` runs `π.P`'s machine
on its coin slice and a suffix of its history, so a uniform machine computes it; completeness for
every witness phase by phase, as in `InteractiveProof.seqRep`. -/
theorem EfficientProverProofErr.seqRep {L : Language Bool} {s : ℕ → ℝ}
    (h : EfficientProverProofErr π L R s) (Q : PolyExpr) (hQ : ∀ n, 1 ≤ Q.eval n) :
    EfficientProverProofErr (π.seqRep Q) L R (fun n => s n ^ Q.eval n) := by
  refine {
    toInteractiveProofErr := h.toInteractiveProofErr.seqRep Q hQ
    efficientP := ?_
    boundedP := ?_
    completeWitness := ?_
  }
  · rw [Protocol.seqRep_P]
    exact π.seqProver_efficient Q h.efficientP
  · obtain ⟨B, hB⟩ := h.boundedP
    exact ⟨B, hB.seqRep Q⟩
  · intro x y hxy z
    exact π.seqRep_complete Q x y z (h.completeWitness x y hxy z)

end TCSlib.Cryptography
