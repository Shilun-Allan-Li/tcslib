/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.TuringMachine.StateRenaming
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finite.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A BPP-hard language of timed probabilistic acceptance

[AB09, §7.5.3, p. 138]: the language `L` of tuples `⟨M, x, 1^t⟩` such that the probabilistic
machine `M` outputs `1` on `x` within `t` steps with probability at least `2/3` is `BPP`-hard:
every `L' ∈ BPP` Karp-reduces to it by `x ↦ ⟨M, x, 1^{T(|x|)}⟩` for a fixed bounded-error
machine `M` of `L'`.

## Main definitions

* `Turing.CodePTM` — the code normal form of a PTM: `k` work tapes, states `Fin (n + 1)`.
* `Turing.PTMCode` — a representation scheme for coded PTMs: total decoding, codes recovered
  under `true`-padding.
* `Turing.FinNDTM.acceptWithinProb` — `Pr[M(x) = 1 within t steps]` over `t` coins.
* `Randomized.ProbAccept` — the language `{⟨M, x, 1^t⟩ : Pr[M(x) = 1 within t steps] ≥ 2/3}`.
* `Randomized.BPPHard` — every language of `BPP` Karp-reduces to `L`.

## Main results

* `Turing.PTMCode.nonempty` — a lawful scheme exists.
* `Turing.FinNDTM.exists_codePTM` — every PTM has a coded copy with the same runs.
* `Randomized.probAccept_bppHard` — [AB09, §7.5.3, p. 138]: `ProbAccept c` is `BPP`-hard.

## Divergences

* The repository's nondeterministic codes (`Turing.CodeNDTM`, `Turing.NDMachineCode`,
  `Turing.EffectiveNDMachineCode` in `TuringMachine/NDCodes.lean`) are fixed at two work tapes,
  while a `BPTIME` machine is a `FinNDTM` with any number `k` of tapes. The only `k → 2`
  converter, `Turing.FinNDTM.exists_codeNDTM_accepts_linear`
  (`Diagonalization/NTimeHierarchy.lean`), is not proved, preserves acceptance only, and
  changes the coin distribution, so it cannot carry acceptance probabilities. We therefore add
  the normal form `CodePTM` (any `k`, `Fin` states) and the abstract scheme `PTMCode` with the
  laws of `Turing.NDMachineCode`: `decode` is total by type and `decode (encode M ++ 1^m) = M`.
* The repository has no effective PTM scheme. Language and hardness are stated for every
  lawful scheme; `PTMCode.nonempty` exhibits one by a non-effective countability argument,
  which suffices since hardness only writes a fixed code (as for `Complexity.TMSAT_NPHard`).
* The tuple is right-nested `Turing.pairEncode`, `1^t` is `List.replicate t true`, and
  "outputs `1` within `t` steps" means the run on the coin word has halted with output exactly
  `[true]`, the output convention of `Turing.FinNDTM.BPDecidesInTime`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing

/-- A probabilistic machine in *code normal form*: `k` work tapes, binary alphabet, states
`Fin (numStates + 1)`. -/
structure CodePTM where
  /-- the number of work tapes -/
  k : ℕ
  /-- one less than the number of states -/
  numStates : ℕ
  /-- the underlying binary-choice machine -/
  tm : NDTM k Bool (Fin (numStates + 1))

/-- The bundled machine of a coded PTM. -/
def CodePTM.toFinNDTM (M : CodePTM) : FinNDTM Bool :=
  ⟨M.k, Fin (M.numStates + 1), M.tm⟩

/-- A representation scheme for coded PTMs: every string decodes to some machine, and a code
followed by any `true`-padding decodes to the machine. -/
structure PTMCode where
  /-- encode a machine as a binary string -/
  encode : CodePTM → List Bool
  /-- decode any binary string to a machine (total by type) -/
  decode : List Bool → CodePTM
  /-- a code followed by any amount of `true`-padding decodes to the machine -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine. -/
theorem PTMCode.decode_encode (c : PTMCode) (M : CodePTM) : c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An action, flattened into a tuple of its fields. -/
private def actionTuple {k : ℕ} {S : Type} (a : Action k Bool S) :
    SignType × (Fin k → Option (Option Bool) × SignType) × Option Bool × Option S :=
  (a.inputTape, a.workTapes, a.output, a.state)

/-- Flattening an action is injective. -/
private theorem actionTuple_injective {k : ℕ} {S : Type} :
    Function.Injective (actionTuple (k := k) (S := S)) := by
  rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h
  simp only [actionTuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- There are finitely many actions over a finite state type. -/
private instance actionFinite {k : ℕ} {S : Type} [Finite S] : Finite (Action k Bool S) :=
  Finite.of_injective _ actionTuple_injective

/-- A coded PTM, flattened into its tape count, state count, initial state and table. -/
private def codeSigma (M : CodePTM) : Σ p : ℕ × ℕ, Fin (p.2 + 1) ×
    (Bool → Fin (p.2 + 1) → Option Bool → (Fin p.1 → Option Bool) →
      Action p.1 Bool (Fin (p.2 + 1))) :=
  ⟨(M.k, M.numStates), M.tm.q₀, M.tm.tr⟩

/-- Flattening a coded PTM is injective. -/
private theorem codeSigma_injective : Function.Injective codeSigma := by
  rintro ⟨k, n, q, tr⟩ ⟨k', n', q', tr'⟩ h
  simp only [codeSigma, Sigma.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- There are countably many coded PTMs. -/
private instance : Countable CodePTM := Function.Injective.countable codeSigma_injective

/-- The one-state machine with no work tapes that halts on its first step. -/
private instance : Nonempty CodePTM :=
  ⟨⟨0, 0, ⟨0, fun _ _ _ _ => ⟨0, fun i => i.elim0, none, none⟩⟩⟩⟩

/-- A lawful representation scheme for coded PTMs exists (non-effective: `M` is coded as
`0^{f M}` for an injection `f` into `ℕ`, and decoding counts the leading zeros). -/
theorem PTMCode.nonempty : Nonempty PTMCode := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat CodePTM
  refine ⟨⟨fun M => List.replicate (f M) false,
    fun s => Function.invFun f (s.takeWhile (· == false)).length, fun M m => ?_⟩⟩
  have hlen : ((List.replicate (f M) false ++ List.replicate m true).takeWhile
      (· == false)).length = f M := by
    rw [List.takeWhile_append_of_pos (by simp)]
    cases m <;> simp [List.replicate_succ]
  simp only [hlen]
  exact Function.leftInverse_invFun hf M

namespace FinNDTM

/-- `Pr[M(x) = 1 within t steps]`: the fraction of coin words of length `t` whose run on `x` has
halted with output exactly `[true]`. [AB09, §7.5.3, p. 138] -/
noncomputable def acceptWithinProb (N : FinNDTM Bool) (x : List Bool) (t : ℕ) : ℚ :=
  open Classical in
  Randomized.randProb t fun w =>
    (N.tm.runWith w (N.tm.initCfg x)).state = none ∧ N.outputWith x w = [true]

/-- Every PTM has a coded copy whose run under every coin word halts exactly when the
original's does, with the same output. -/
theorem exists_codePTM (N : FinNDTM Bool) : ∃ M : CodePTM, ∀ x w : List Bool,
    ((M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x)).state = none ↔
      (N.tm.runWith w (N.tm.initCfg x)).state = none) ∧
    M.toFinNDTM.outputWith x w = N.outputWith x w := by
  rcases N with @⟨k, Q, hQ, dQ, tm⟩
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨k, Fintype.card Q - 1, tm.relabelState e⟩, fun x w => ?_⟩
  have hrun := NDTM.relabelState_runWith tm e (tm.initCfg x) w
  have hinit : (tm.relabelState e).initCfg x = (tm.initCfg x).mapState e := rfl
  simp only [CodePTM.toFinNDTM, outputWith]
  rw [hinit, hrun]
  refine ⟨?_, rfl⟩
  simp only [Cfg.mapState, Option.map_eq_none_iff]

/-- Once every branch has halted by time `T`, the timed acceptance probability at any `t ≥ T`
is `Pr[M(x) = 1]` over `T` coins. -/
theorem acceptWithinProb_eq_outputProb {N : FinNDTM Bool} {x : List Bool} {T t : ℕ}
    (h : N.tm.HaltsWithin x T) (hle : T ≤ t) :
    N.acceptWithinProb x t = N.outputProb x T [true] := by
  classical
  rw [← outputProb_eq_of_haltsWithin h hle]
  unfold acceptWithinProb outputProb
  refine Randomized.randProb_congr fun r => ?_
  have hh := (h.mono hle) (List.ofFn r) List.length_ofFn
  constructor
  · exact fun hr => hr.2
  · exact fun hr => ⟨hh, hr⟩

end FinNDTM

end Turing

namespace Randomized

open Turing Complexity

/-- The language `L` of [AB09, §7.5.3, p. 138]: tuples `⟨α, x, 1^t⟩` (right-nested
`Turing.pairEncode`) such that the PTM decoded from `α` outputs `1` on `x` within `t` steps
with probability at least `2/3`. -/
def ProbAccept (c : PTMCode) : Language Bool :=
  {y | ∃ (α x : List Bool) (t : ℕ),
    y = pairEncode α (pairEncode x (List.replicate t true)) ∧
    2 / 3 ≤ (c.decode α).toFinNDTM.acceptWithinProb x t}

/-- `BPP`-hardness: every language of `BPP` Karp-reduces to `L`. [AB09, §7.5.3, p. 138] -/
def BPPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ BPP_PTM, L' ≤ₚ L

/-- `n^e + 1 ≤ 2 (n+1)^e`. -/
private theorem pow_add_one_le_two_mul (n e : ℕ) : n ^ e + 1 ≤ 2 * (n + 1) ^ e := by
  have h1 : n ^ e ≤ (n + 1) ^ e := Nat.pow_le_pow_left (Nat.le_succ n) e
  have h2 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos n)
  omega

/-- **`L` is `BPP`-hard** [AB09, §7.5.3, p. 138]: for every lawful PTM scheme `c`, every
`L' ∈ BPP` reduces to `ProbAccept c` by `x ↦ ⟨⌞M⌟, x, 1^{2a(|x|+1)^e}⟩`, where `M` decides
`L'` in time `a (n^e + 1)`.

**Proof sketch.** Take a coded copy `M'` of `M` (`FinNDTM.exists_codePTM`) and `α = encode M'`.
The map is polynomial-time by pairing a constant, the identity and a unary polynomial. By
injectivity of the pairing, `f x ∈ ProbAccept c` iff `Pr[M'(x) = 1 within t] ≥ 2/3` at
`t = 2a(|x|+1)^e ≥ a(|x|^e + 1)`; past the halting time this is `Pr[M(x) = 1]`, which is
`≥ 2/3` on members and `≤ 1 − Pr[M(x) = 0] ≤ 1/3` on non-members. -/
theorem probAccept_bppHard (c : PTMCode) : BPPHard (ProbAccept c) := by
  classical
  intro L hL
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hL
  obtain ⟨a, N, hN⟩ := he
  obtain ⟨M, hM⟩ := N.exists_codePTM
  let α := c.encode M
  let t : ℕ → ℕ := fun n => 2 * a * (n + 1) ^ e
  have htT (n : ℕ) : a * (n ^ e + 1) ≤ t n := by
    have := Nat.mul_le_mul_left a (pow_add_one_le_two_mul n e)
    simpa only [t, Nat.mul_assoc, Nat.mul_left_comm a 2] using this
  refine ⟨fun x => pairEncode α (pairEncode x (List.replicate (t x.length) true)), ?_, ?_⟩
  · exact (polyTimeComputable_const α).pairEncode
      (polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary (2 * a) e))
  intro x
  obtain ⟨hhalt, hprob⟩ := hN x
  -- the coded copy has the same timed acceptance probability
  have hacc : (c.decode α).toFinNDTM.acceptWithinProb x (t x.length) =
      N.outputProb x (a * (x.length ^ e + 1)) [true] := by
    rw [show c.decode α = M from c.decode_encode M,
      ← N.acceptWithinProb_eq_outputProb hhalt (htT _)]
    unfold FinNDTM.acceptWithinProb
    exact randProb_congr fun r => by rw [(hM x _).1, (hM x _).2]
  have hmem : pairEncode α (pairEncode x (List.replicate (t x.length) true)) ∈ ProbAccept c ↔
      2 / 3 ≤ (c.decode α).toFinNDTM.acceptWithinProb x (t x.length) := by
    constructor
    · rintro ⟨β, y, s, heq, hs⟩
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj (pairEncode_injective heq)
      obtain ⟨rfl, hrep⟩ := Prod.mk.inj (pairEncode_injective hrest)
      have hst : t x.length = s := by simpa using congrArg List.length hrep
      rw [hst]
      exact hs
    · exact fun h => ⟨α, x, t x.length, rfl, h⟩
  rw [hmem, hacc]
  by_cases hx : x ∈ L
  · simpa only [hx, true_iff, MultiTapeTM.indicator, if_true] using hprob
  · simp only [hx, false_iff, not_le]
    simp only [MultiTapeTM.indicator, hx, if_false] at hprob
    have hdisj : N.outputProb x (a * (x.length ^ e + 1)) [true] ≤
        1 - N.outputProb x (a * (x.length ^ e + 1)) [false] := by
      unfold FinNDTM.outputProb
      rw [← randProb_not]
      exact randProb_mono fun r hr hf => by rw [hr] at hf; simp at hf
    linarith

end Randomized
