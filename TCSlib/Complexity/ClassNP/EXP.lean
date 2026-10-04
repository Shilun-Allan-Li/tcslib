/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* **The certificate length is the explicit formula `C · 2^((|x|+1)^c)`** — the
  same phase-1 audit repair as `Complexity.NP` (finding 1, Argument A: an
  abstract `ExpBound` length function admits undecidable classes). `ExpBound`
  survives as a numerical helper only.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
certificates of length exactly `C · 2^((|x|+1)^c)` — an explicit formula, per
the phase-1 audit repair — with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hL
  have hbound : ∀ n : ℕ, n ^ c + 1 ≤ 2 * 2 ^ n ^ c := by
    intro n
    have hn := Nat.lt_two_pow_self (n := n ^ c)
    omega
  obtain ⟨a, M, hM⟩ := DTIME.mono hbound hc
  refine Set.mem_iUnion.mpr ⟨c, a * 2, M, fun x => ?_⟩
  simpa only [Nat.mul_assoc] using hM x

open Turing Turing.FinTM

/-! ### Private certificate enumeration infrastructure -/

/-- Little-endian value, including leading zeroes at the high end. -/
private def enumValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * enumValue bs + if b then 1 else 0

/-- Increment without extending the width; `none` means exhaustion.
The empty word overflows, so its caller must test it before incrementing. -/
private def enumInc : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (enumInc bs).map (false :: ·)

/-- A width-`w` little-endian representation of the low `w` bits of `i`. -/
private def enumWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)

/-- Every width-`w` word has value strictly below `2^w`. -/
private lemma enumValue_lt (u : List Bool) : enumValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [enumValue]
  | cons b u ih =>
    cases b <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.pow_succ] <;> omega

/-- The representation retains exactly the requested width, even at zero. -/
private lemma enumWord_length (w i : ℕ) : (enumWord w i).length = w := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih => simp only [enumWord, List.length_cons, ih]

/-- The initial rank is represented by precisely the all-false word. -/
private lemma enumWord_zero (w : ℕ) : enumWord w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [enumWord, ih, List.replicate_succ]

/-- In range, the representation has the specified value.
**Proof sketch.** Remove the low bit by division by two. The quotient is
in range for the remaining width, and the remainder is either zero or one. -/
private lemma enumWord_value (w i : ℕ) (hi : i < 2 ^ w) :
    enumValue (enumWord w i) = i := by
  induction w generalizing i with
  | zero => simp only [Nat.pow_zero] at hi; simp [enumWord, enumValue, show i = 0 by omega]
  | succ w ih =>
    have hdiv : i / 2 < 2 ^ w := by rw [Nat.pow_succ] at hi; omega
    simp only [enumWord, enumValue, ih (i / 2) hdiv]
    have hmod := Nat.mod_lt i (by omega : 0 < 2)
    split <;> simp_all <;> omega

/-- Equal-length words with the same value are equal, including trailing
false bits. The parity determines the first bit; divide the remainder by two. -/
private lemma enumValue_injective (u v : List Bool) (hlen : u.length = v.length)
    (hval : enumValue u = enumValue v) : u = v := by
  induction u generalizing v with
  | nil => simpa using hlen.symm
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons b' v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases b <;> cases b' <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte] at hval
      all_goals first | omega | exact congrArg (_ :: ·) (ih v hlen' (by omega))

/-- Every word is the unique representative of its rank at its own width. -/
private lemma enumWord_complete (u : List Bool) :
    enumWord u.length (enumValue u) = u := by
  exact enumValue_injective _ _ (enumWord_length _ _)
    (enumWord_value _ _ (enumValue_lt u))

/-- One fixed-width increment either preserves width and adds one to the
value, or reports overflow exactly at the last rank.
**Proof sketch.** A low false bit changes to true. A low true bit is cleared
and passes the carry to the suffix; suffix overflow is total overflow. -/
private lemma enumInc_spec (u : List Bool) :
    match enumInc u with
    | some v => v.length = u.length ∧ enumValue v = enumValue u + 1
    | none => enumValue u + 1 = 2 ^ u.length := by
  induction u with
  | nil => simp [enumInc, enumValue]
  | cons b u ih =>
    cases b with
    | false => simp [enumInc, enumValue]
    | true =>
      cases he : enumInc u with
      | none =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_none, enumValue, ↓reduceIte,
          List.length_cons, Nat.pow_succ]
        omega
      | some v =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_some, enumValue, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact ⟨by omega, by omega⟩

/-- On canonical candidates, increment advances exactly one rank and reports
overflow only after the last rank. This includes width zero. -/
private lemma enumInc_word (w i : ℕ) (hi : i < 2 ^ w) :
    enumInc (enumWord w i) =
      if i + 1 < 2 ^ w then some (enumWord w (i + 1)) else none := by
  have hs := enumInc_spec (enumWord w i)
  rw [enumWord_length, enumWord_value w i hi] at hs
  cases he : enumInc (enumWord w i) with
  | none => simp only [he] at hs; simp [show ¬i + 1 < 2 ^ w by omega]
  | some v =>
    simp only [he] at hs
    have hv := enumValue_lt v
    rw [hs.1, hs.2] at hv
    rw [if_pos hv]
    congr 1
    exact enumValue_injective v _ (hs.1.trans (enumWord_length _ _).symm)
      (hs.2.trans (enumWord_value w (i + 1) hv).symm)

/-- No candidate repeats among the `2^w` in-range ranks. -/
private lemma enumWord_no_repeat (w i j : ℕ) (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (h : enumWord w i = enumWord w j) : i = j := by
  have := congrArg enumValue h
  simpa only [enumWord_value w i hi, enumWord_value w j hj] using this

/-- Exact-width existential certificates are exactly the in-range candidates. -/
private lemma enumCandidates_iff (w : ℕ) (p : List Bool → Prop) :
    (∃ u, u.length = w ∧ p u) ↔ ∃ i, i < 2 ^ w ∧ p (enumWord w i) := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact ⟨enumValue u, enumValue_lt u, by simpa only [enumWord_complete] using hu⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨enumWord w i, enumWord_length w i, hp⟩

/-- Resulting tape contents and success flag of a fixed-width carry. Overflow
clears the entire word and returns false; it never writes an extra bit. -/
private def enumBump : List Bool → List Bool × Bool
  | [] => ([], false)
  | false :: bs => (true :: bs, true)
  | true :: bs => (false :: (enumBump bs).1, (enumBump bs).2)

/-- The number of leading true bits crossed by the carry. -/
private def enumCarryPos : List Bool → ℕ
  | true :: bs => enumCarryPos bs + 1
  | _ => 0

/-- The carry visits at most the candidate width before detecting overflow. -/
private lemma enumCarryPos_le (u : List Bool) : enumCarryPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [enumCarryPos, List.length_cons] <;> omega

/-- The physical carry's tape contents always retain the original width. -/
private lemma enumBump_length (u : List Bool) : (enumBump u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [enumBump, ih]

/-- The carry's success flag and tape contents implement `enumInc` exactly. -/
private lemma enumBump_inc (u : List Bool) :
    enumInc u = if (enumBump u).2 then some (enumBump u).1 else none := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | false => rfl
    | true => simp only [enumInc, enumBump, ih]; split <;> rfl

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma enumBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma enumBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- One-tape fixed-width increment, followed by a rewind. The live states are
carry (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def enumCarryTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some true => ⟨0, fun _ => (some (some false), .pos), none, some (.inl none)⟩
          | some false => ⟨0, fun _ => (some (some true), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the carry tape, with arbitrary native input-head position. -/
private def enumCarryCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg enumCarryTM.k Bool enumCarryTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One carry transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma enumCarry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    enumCarryTM.tm.step (enumCarryCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => enumCarryCfg x p (.inl (some false)) (pre.length - 1) pre
      | false :: us => enumCarryCfg x p (.inl (some true)) (pre.length - 1) (pre ++ true :: us)
      | true :: us => enumCarryCfg x p (.inl none) (pre.length + 1) (pre ++ false :: us) := by
  unfold MultiTapeTM.step
  change (enumCarryTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, enumBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact enumBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The carry phase takes one step beyond the leading true prefix, including
one blank test on overflow.
**Proof sketch.** Induct on the remaining candidate. Each true bit is cleared
and added to the processed prefix. A false bit or the right blank starts
rewind without changing the width. -/
private lemma enumCarry_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) pre.length (pre ++ u))
        (enumCarryPos u + 1) =
      enumCarryCfg x p (.inl (some (enumBump u).2))
        ((pre.length : ℤ) + enumCarryPos u - 1) (pre ++ (enumBump u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
      enumCarry_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | false =>
      simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
        enumCarry_step x p pre (false :: u)
    | true =>
      simp only [enumCarryPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCarry_step]
      simpa [enumBump, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [false])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma enumCarry_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = enumCarryCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : enumCarryTM.tm.step
        (enumCarryCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width increment and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading true-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns overflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma enumCarry_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * enumCarryPos u + 2 ≤ 2 * u.length + 2 ∧
      enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) 0 u)
          (2 * enumCarryPos u + 2) =
        enumCarryCfg x p (.inr (enumBump u).2) 0 (enumBump u).1 := by
  refine ⟨by have := enumCarryPos_le u; omega, ?_⟩
  have hr := enumCarry_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * enumCarryPos u + 2 = (enumCarryPos u + 1) + (enumCarryPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact enumCarry_rewind x p (enumBump u).1 (enumBump u).2 _
    (by rw [enumBump_length]; exact enumCarryPos_le u)

section EnumCapture

variable {S : Type} [Fintype S] [DecidableEq S]
variable (M : FinTM Bool) (r : ℕ) (next : Option Bool → S)
variable (control : S → Option Bool → (Fin (M.k + (1 + r)) → Option Bool) →
  Action (M.k + (1 + r)) Bool (((Option M.State × Option Bool) × Bool) ⊕ S))

/-- Run a verifier on a work-tape input buffer, capture its first output bit
in finite control, and return live to a controller with access to all tapes.
The tape blocks are verifier work, input buffer, and `r` retained tapes.
The boundary tag supplies the verifier's native clamping behavior. The real
input head and retained tapes do not move during a call. -/
private def enumCaptureTM : FinTM Bool where
  k := M.k + (1 + r)
  State := ((Option M.State × Option Bool) × Bool) ⊕ S
  tm :=
    { q₀ := .inl ((some M.tm.q₀, none), true)
      tr := fun q inp work => match q with
        | .inl ((some q, reg), tag) =>
          let v := work (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1)))
          let a := M.tm.tr q v (fun i => work (Fin.castAdd (1 + r) i))
          let m := virtualMove tag v a.inputTape
          ⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
            some (.inl ((a.state, reg.or a.output), virtualNextTag tag m))⟩
        | .inl ((none, reg), _) => controlAction 0 (some (.inr (next reg)))
        | .inr q => control q inp work }

/-- A complete call invariant: exact source work tapes, an unchanged virtual
input buffer, arbitrary retained tapes, source output captured in finite
control, and empty physical output. The native input `x` can differ from
the verifier input `y`. -/
private def enumCaptureCfg {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) :
    Cfg (enumCaptureTM M r next control).k Bool
      (enumCaptureTM M r next control).State x where
  state := some (.inl ((cfg.state, cfg.output.head?), tag))
  inputPos := p
  workTapes := tapeBlocks cfg.workTapes (bufferTape y) tapes
  workTapePos := tapeBlocks cfg.workTapePos ((cfg.inputPos.val : ℤ) - 1) heads
  output := []

/-- One live source transition is simulated in one physical step, updating
the captured bit before recording a possible halt.
**Proof sketch.** Buffer reads equal native source reads. The virtual movement
lemma proves both clamping and preservation of the boundary tag. The verifier
work block changes in lockstep; the other tape contents are unchanged. The
head-of-append identity gives the captured bit, even on the halting action. -/
private lemma enumCapture_step {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hs : cfg.state ≠ none) :
    ∃ tag', VirtualTag (M.tm.step cfg).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.step
          (enumCaptureCfg M r next control cfg tag p tapes heads) =
        enumCaptureCfg M r next control (M.tm.step cfg) tag' p tapes heads := by
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    let m := virtualMove tag cfg.inputSymbol a.inputTape
    have hm := virtualMove_correct cfg tag htag a.inputTape
    have hc : M.tm.step cfg = a.apply cfg := by simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs' : (enumCaptureCfg M r next control cfg tag p tapes heads).state =
          some (.inl ((some q, cfg.output.head?), tag)) := by simp [enumCaptureCfg, hq]
      have hv : (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1))) = cfg.inputSymbol := by
        simp [enumCaptureCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.castAdd (1 + r) i)) = cfg.workTapeSymbols := by
        funext i
        simp [enumCaptureCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs']
      dsimp only [enumCaptureTM]
      rw [hv, hr, hq]
      change (⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
        some (.inl ((a.state, cfg.output.head?.or a.output), virtualNextTag tag m))⟩ :
        Action (M.k + (1 + r)) Bool _).apply _ =
          enumCaptureCfg M r next control (a.apply cfg) _ p tapes heads
      refine Cfg.ext ?_ (moveInputPos_zero p) ?_ ?_ ?_
      · simp [enumCaptureCfg, Action.apply, List.head?_append, Option.head?_toList]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [enumCaptureCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · simp [enumCaptureCfg, Action.apply]

/-- Lockstep through the first source halt, with an exact virtual-input
simulation, no physical emissions, and all retained tapes intact. -/
private lemma enumCapture_run {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    ∃ tag', VirtualTag (M.tm.runFrom cfg t).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control cfg tag p tapes heads) t =
        enumCaptureCfg M r next control (M.tm.runFrom cfg t) tag' p tapes heads := by
  induction t with
  | zero => exact ⟨tag, htag, rfl⟩
  | succ t ih =>
    obtain ⟨tag', htag', he⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨tag'', htag'', he'⟩ :=
      enumCapture_step M r next control _ tag' htag' p tapes heads (h t (by omega))
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using htag''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The administrative return step dispatches on the updated register and
preserves every tape, head, and the empty physical output. -/
private lemma enumCapture_transfer {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (h : cfg.state = none) :
    (enumCaptureTM M r next control).tm.step
        (enumCaptureCfg M r next control cfg tag p tapes heads) =
      { enumCaptureCfg M r next control cfg tag p tapes heads with
        state := some (.inr (next cfg.output.head?)) } := by
  unfold MultiTapeTM.step
  simp only [enumCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Given a prepared buffer and fresh source tapes, a singleton-output call
returns its bit to the live controller within the source budget plus one.
This holds for any native input and parked head, including empty verifier
input. The complete returned configuration certifies retention and silence.
**Proof sketch.** Take the first source halting time. Start its virtual head
at cell zero with the right-boundary-compatible tag `true`. Apply lockstep
through the halt, then transfer. Absorbing source halting identifies its full
configuration with the one at the supplied budget. -/
private lemma enumCapture_returns (x y : List Bool) (b : Bool) (T : ℕ)
    (p : Fin (x.length + 2)) (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hM : M.ComputesInTime y [b] T) :
    ∃ t, t ≤ T + 1 ∧ ∃ tag,
      VirtualTag (M.tm.runFrom (M.tm.initCfg y) T).inputPos tag ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control (M.tm.initCfg y) true p tapes heads) t =
        { enumCaptureCfg M r next control (M.tm.runFrom (M.tm.initCfg y) T)
            tag p tapes heads with state := some (.inr (next (some b))) } := by
  classical
  obtain ⟨hh, hout⟩ := (computesInTime_iff M y [b] T).mp hM
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg y) t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  have hs : (M.tm.runFrom (M.tm.initCfg y) t).state = none := Nat.find_spec hex
  have he : M.tm.runFrom (M.tm.initCfg y) T = M.tm.runFrom (M.tm.initCfg y) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  obtain ⟨tag, htag, hr⟩ := enumCapture_run M r next control (M.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    (fun s hs => Nat.find_min hex hs)
  refine ⟨t + 1, by omega, tag, by rwa [he], ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hr,
    enumCapture_transfer M r next control _ tag p tapes heads hs, ← he, hout]
  rfl

end EnumCapture

/-- Boolean result of testing `count` consecutive candidate ranks, starting
with `i`. The recursive branch represents one rejected call. -/
private def enumAny (accept : ℕ → Bool) (i : ℕ) : ℕ → Bool
  | 0 => false
  | count + 1 => if accept i then true else enumAny accept (i + 1) count

/-- The abstract loop accepts exactly when an in-range candidate accepts.
**Proof sketch.** Separate the first rank from the remaining interval. -/
private lemma enumAny_iff (accept : ℕ → Bool) (i count : ℕ) :
    enumAny accept i count = true ↔
      ∃ j, i ≤ j ∧ j < i + count ∧ accept j = true := by
  induction count generalizing i with
  | zero =>
    simp only [enumAny, Bool.false_eq_true, false_iff]
    rintro ⟨j, hj, hj', _⟩
    omega
  | succ count ih =>
    change (if accept i then true else enumAny accept (i + 1) count) = true ↔ _
    by_cases h : accept i = true
    · simp only [if_pos h, true_iff]
      exact ⟨i, le_refl _, by omega, h⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨j, hj, hj', ha⟩
        exact ⟨j, by omega, by omega, ha⟩
      · rintro ⟨j, hj, hj', ha⟩
        have hne : j ≠ i := by intro he; subst j; exact h ha
        exact ⟨j, by omega, by omega, ha⟩

/-- For the actual verifier's indicator, testing all ranks gives exactly the
definition's existential over certificates of width `w`. This is independent
of the machine implementation, and includes width zero. -/
private lemma enumAny_certificates (x : List Bool) (w : ℕ) (V : Language Bool) :
    enumAny (fun i => MultiTapeTM.indicator V (x ++ enumWord w i)) 0 (2 ^ w) = true ↔
      ∃ u, u.length = w ∧ x ++ u ∈ V := by
  classical
  rw [enumAny_iff, enumCandidates_iff]
  simp [MultiTapeTM.indicator]

/-- A timed loop invariant combines bounded accept-or-advance segments into
one bounded singleton-output computation. The terminal configuration is the
post-overflow rejection configuration, so every candidate, including the last,
is tested before exhaustion.
**Proof sketch.** Induct on the remaining number of candidates. Acceptance
terminates immediately. Rejection advances to the next canonical configuration;
compose run segments and add their bounds. This lemma does not assert that
any particular machine satisfies the required per-round contracts. -/
private lemma enumLoop_run (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (accept : ℕ → Bool) (B i count : ℕ)
    (hend : (cfg (i + count)).state = none ∧ (cfg (i + count)).output = [false])
    (hround : ∀ j, i ≤ j → j < i + count → ∃ t, t ≤ B ∧
      if accept j then
        (M.tm.runFrom (cfg j) t).state = none ∧ (M.tm.runFrom (cfg j) t).output = [true]
      else M.tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t, t ≤ count * B ∧ (M.tm.runFrom (cfg i) t).state = none ∧
      (M.tm.runFrom (cfg i) t).output = [enumAny accept i count] := by
  induction count generalizing i with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa [enumAny] using hend
  | succ count ih =>
    obtain ⟨t, ht, hc⟩ := hround i (le_refl _) (by omega)
    by_cases hb : accept i = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · rw [Nat.succ_mul]; omega
      · simpa [enumAny, hb] using hc.2
    · simp only [hb] at hc
      have hend' : (cfg (i + 1 + count)).state = none ∧
          (cfg (i + 1 + count)).output = [false] := by
        simpa only [show i + 1 + count = i + (count + 1) by omega] using hend
      obtain ⟨s, hs, hhalt, hout⟩ := ih (i + 1) hend'
        (fun j hj hj' => hround j (by omega) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [enumAny, hb] using hout

/-- A fixed polynomial in `n+1` in the exponent is absorbed into `n^e`,
with a uniform multiplicative constant for lengths zero and one.
**Proof sketch.** For `n ≥ 2`, use `K ≤ 2^K ≤ n^K` and `n+1 ≤ n^2`.
For `n ≤ 1`, bound the exponent by `K·2^k` and absorb its exponential. -/
private lemma enumExponent_bound (K k : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ A * 2 ^ n ^ e := by
  refine ⟨2 ^ (K * 2 ^ k), K + 2 * k, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hK : K ≤ n ^ K :=
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
    have hn' : n + 1 ≤ n ^ 2 := by
      calc n + 1 ≤ 2 * n := by omega
           _ ≤ n * n := Nat.mul_le_mul_right n hn
           _ = n ^ 2 := by ring
    have hexp : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
      calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
             Nat.mul_le_mul hK (Nat.pow_le_pow_left hn' k)
           _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by omega) hexp).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
           Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
         _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
           Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- The audited round budget is pointwise bounded by an `EXP` budget, for
all coefficients and degrees, including zero.
**Proof sketch.** Set `k=max 1 c`. Both `n+1` and the width are bounded by
constant multiples of `(n+1)^k`. Replace the polynomial round overhead by
`2^(d·(n+width+1))`, add the exponents, and use `enumExponent_bound`. -/
private lemma enumBudget_bound (a C c d : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ,
      a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
        A * 2 ^ n ^ e := by
  let k := max 1 c
  let K := C + d * (C + 1)
  obtain ⟨A, e, hA⟩ := enumExponent_bound K k
  refine ⟨a * A, e, fun n => ?_⟩
  have hc : (n + 1) ^ c ≤ (n + 1) ^ k :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right 1 c)
  have hn : n + 1 ≤ (n + 1) ^ k := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left 1 c)
  have hw : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ k := by
    calc n + C * (n + 1) ^ c + 1 = (n + 1) + C * (n + 1) ^ c := by omega
         _ ≤ (n + 1) ^ k + C * (n + 1) ^ k :=
           Nat.add_le_add hn (Nat.mul_le_mul_left C hc)
         _ = (C + 1) * (n + 1) ^ k := by ring
  have he : C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
      K * (n + 1) ^ k := by
    calc C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
        C * (n + 1) ^ k + d * ((C + 1) * (n + 1) ^ k) :=
          Nat.add_le_add (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left d hw)
         _ = K * (n + 1) ^ k := by dsimp [K]; ring
  have hb : (n + C * (n + 1) ^ c + 1) ^ d ≤
      2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
    calc (n + C * (n + 1) ^ c + 1) ^ d ≤
        (2 ^ (n + C * (n + 1) ^ c + 1)) ^ d :=
          Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) d
         _ = 2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
  calc a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
      a * (2 ^ (C * (n + 1) ^ c) * 2 ^ (d * (n + C * (n + 1) ^ c + 1))) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hb
       _ = a * 2 ^ (C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1)) := by
        rw [Nat.pow_add]
       _ ≤ a * 2 ^ (K * (n + 1) ^ k) :=
        Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) he)
       _ ≤ a * A * 2 ^ n ^ e := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a (hA n)

/-- The catalog counter and the predecessor's counter have the same recursive
equations, including overflow on the empty word. -/
private lemma enumCont_inc_eq (s : List Bool) : incFixed s = enumInc s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp only [incFixed, enumInc, ih]

/-- Stalling on overflow preserves the exact candidate width. -/
private lemma enumCont_step_length (s : List Bool) :
    ((incFixed s).getD s).length = s.length := by
  rw [enumCont_inc_eq]
  have h := enumInc_spec s
  cases hi : enumInc s with
  | none => rfl
  | some u => simp only [hi] at h; exact h.1

/-- Before exhaustion, the stalled catalog orbit is exactly the predecessor's
rank enumeration. No identity is asserted at the terminal rank `2^w`.
**Proof sketch.** The initial word is `enumWord w 0`. At a successor rank
still below `2^w`, the proved increment equation returns `some` of the next
word, so the fallback branch is never used. -/
private lemma enumCont_orbit (w : ℕ) : ∀ i, i < 2 ^ w →
    (fun s => (incFixed s).getD s)^[i] (List.replicate w false) =
      enumWord w i := by
  intro i
  induction i with
  | zero => intro _; exact (enumWord_zero w).symm
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), enumCont_inc_eq,
      enumInc_word w i (by omega), if_pos hi]
    rfl

/-- The exact fuel word is a unary all-true word of the certificate width.
**Proof sketch.** At successor width, `2^(w+1)-1 = 2*(2^w-1)+1`;
`Nat.bit1_bits` prepends a true bit. The base case is zero fuel. -/
private lemma enumCont_fuel_bits (w : ℕ) :
    Nat.bits (2 ^ w - 1) = List.replicate w true := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hp : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have he : 2 ^ (w + 1) - 1 = 2 * (2 ^ w - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [he, Nat.bit1_bits, ih, List.replicate_succ]

/-- A history tape can contain blank entries; its length is tracked on a
separate all-true clock tape. Cells outside its finite list are blank. -/
private def enumCont_sparse (w : List (Option Bool)) (z : ℤ) : Option Bool :=
  if 0 ≤ z then (w[z.toNat]?).join else none

/-- Appending a possibly blank history symbol writes just the next cell. -/
private lemma enumCont_sparse_append (w : List (Option Bool)) (b : Option Bool) :
    enumCont_sparse (w ++ [b]) =
      Function.update (enumCont_sparse w) (w.length : ℤ) b := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp [enumCont_sparse]
  · rw [Function.update_of_ne hz]
    by_cases hnonneg : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [enumCont_sparse, if_pos hnonneg]
      by_cases hlt : z.toNat < w.length
      · rw [List.getElem?_append_left hlt]
      · have hgt : w.length + 1 ≤ z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by omega)]
    · simp only [enumCont_sparse, if_neg hnonneg]

/-- Erasing the last history cell recovers its prefix, even if the erased
entry was itself blank. -/
private lemma enumCont_sparse_erase (w : List (Option Bool)) (b : Option Bool) :
    Function.update (enumCont_sparse (w ++ [b])) (w.length : ℤ) none =
      enumCont_sparse w := by
  rw [enumCont_sparse_append, Function.update_idem]
  have hblank : enumCont_sparse w (w.length : ℤ) = none := by
    simp [enumCont_sparse]
  rw [← hblank]
  exact Function.update_eq_self _ _

/-- Three tape symbols encode the three source head moves. -/
private def enumCont_moveCode : SignType → Option Bool
  | .neg => some false
  | .zero => none
  | .pos => some true

/-- Decode the inverse move for the backward restoration pass. -/
private def enumCont_unmove : Option Bool → SignType
  | some false => .pos
  | none => .zero
  | some true => .neg

/-- A recorded move and its inverse cancel as integer head displacements. -/
private lemma enumCont_unmove_cast (d : SignType) :
    (enumCont_unmove (enumCont_moveCode d)).cast = -(d.cast : ℤ) := by
  cases d <;> rfl

/-- A history entry retains every overwritten symbol and every source move.
No source state or native-input movement is needed for work-tape restoration. -/
private abbrev EnumContEntry (k : ℕ) :=
  (Fin k → Option Bool) × (Fin k → SignType)

/-- Instrument one source action with a clock cell and two history tracks per
source tape. The source action and output are otherwise unchanged. -/
private def enumCont_logAction {k : ℕ} {S : Type} (old : Fin k → Option Bool)
    (a : Action k Bool S) : Action (k + (1 + (k + k))) Bool S :=
  ⟨a.inputTape,
    tapeBlocks a.workTapes (some (some true), .pos)
      (Fin.addCases (fun i => (some (old i), .pos))
        (fun i => (some (enumCont_moveCode (a.workTapes i).2), .pos))),
    a.output, a.state⟩

/-- The logged source keeps its original finite state set. The extra tapes
are a unary step clock, old-symbol histories, and movement histories. -/
private def enumCont_logTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + (1 + (M.k + M.k))
  State := M.State
  tm := {
    q₀ := M.tm.q₀
    tr := fun q inp work =>
      let old := fun i : Fin M.k => work (Fin.castAdd (1 + (M.k + M.k)) i)
      enumCont_logAction old (M.tm.tr q inp old) }

/-- The correspondence stores exactly the source configuration and the
finite history; every history head is one cell past the recorded entries. -/
private def enumCont_logCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) :
    Cfg (k + (1 + (k + k))) Bool S x :=
  ⟨c.state, c.inputPos,
    tapeBlocks c.workTapes (bufferTape (List.replicate h.length true))
      (Fin.addCases (fun i => enumCont_sparse (h.map (fun e => e.1 i)))
        (fun i => enumCont_sparse (h.map (fun e => enumCont_moveCode (e.2 i))))),
    tapeBlocks c.workTapePos (h.length : ℤ) (fun _ => h.length), c.output⟩

/-- One logged action preserves source semantics and appends exactly one
history entry, including a halting or emitting action.
**Proof sketch.** Split the physical tapes into source, clock, old-symbol,
and movement blocks. Source fields apply the original action; each history
field is the single-cell append identity at its current length. -/
private lemma enumCont_log_apply {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) (a : Action k Bool S) :
    (enumCont_logAction c.workTapeSymbols a).apply (enumCont_logCfg c h) =
      enumCont_logCfg (a.apply c)
        (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
          List.replicate_add, bufferTape_append]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
            enumCont_sparse_append, Fin.addCases]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
            Fin.addCases]

/-- Record precisely the actions actually executed by a source run. No entry
is added after the source has halted. -/
private def enumCont_history {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c₀ : Cfg k Bool S x) : ℕ → List (EnumContEntry k)
  | 0 => []
  | t + 1 =>
    let c := tm.runFrom c₀ t
    match c.state with
    | none => enumCont_history tm c₀ t
    | some q => enumCont_history tm c₀ t ++
        [(c.workTapeSymbols, fun i => ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i).2)]

/-- Logging is lockstep with the source, from arbitrary prepared source
configurations. The source input, output, and halting time are unchanged.
**Proof sketch.** Induct on elapsed time. Halted configurations remain fixed;
otherwise the source-block reads agree and `enumCont_log_apply` records the
next action. This also covers the final emission on the halting action. -/
private lemma enumCont_log_run (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (t : ℕ) :
    (enumCont_logTM M).tm.runFrom (enumCont_logCfg c₀ []) t =
      enumCont_logCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    let c := M.tm.runFrom c₀ t
    have hr : (fun i : Fin M.k =>
        (enumCont_logCfg c (enumCont_history M.tm c₀ t)).workTapeSymbols
          (Fin.castAdd (1 + (M.k + M.k)) i)) = c.workTapeSymbols := by
      funext i
      simp [enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hsrun : (M.tm.runFrom c₀ t).state = c.state := rfl
    cases hs : c.state with
    | none =>
      have hn : (M.tm.runFrom c₀ t).state = none := hsrun.trans hs
      simp only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step,
        enumCont_history, enumCont_logCfg, hn]
    | some q =>
      have hq : (M.tm.runFrom c₀ t).state = some q := hsrun.trans hs
      have hstate : (enumCont_logCfg (M.tm.runFrom c₀ t)
          (enumCont_history M.tm c₀ t)).state = some q := hq
      simp only [MultiTapeTM.step, hstate]
      change (enumCont_logAction _ ((M.tm.tr q _ _))).apply _ = _
      rw [hr, enumCont_log_apply]
      simp only [enumCont_history, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.step, hq]
      rfl

/-- The restoration controller alternates inverse head movement with writing
the old symbols. It erases history as it goes and halts with history heads at
zero when the clock's left blank is reached. Native input is stationary. -/
private def enumCont_undoTM (k : ℕ) : FinTM Bool where
  k := k + (1 + (k + k))
  State := Option (Fin k → Option Bool)
  tm := {
    q₀ := none
    tr := fun q _ work => match q with
      | none =>
        if (work (Fin.natAdd k (Fin.castAdd (k + k) 0))).isSome then
          ⟨0, tapeBlocks
            (fun i => (none, enumCont_unmove
              (work (Fin.natAdd k (Fin.natAdd 1 (Fin.natAdd k i))))))
            (some none, 0) (fun _ => (some none, 0)), none,
            some (some (fun i => work (Fin.natAdd k (Fin.natAdd 1 (Fin.castAdd k i)))))⟩
        else
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos)
            (fun _ => (none, .pos)), none, none⟩
      | some old =>
        ⟨0, tapeBlocks (fun i => (some (old i), 0)) (none, .neg)
          (fun _ => (none, .neg)), none, some none⟩ }

/-- At a restoration checkpoint the heads inspect the last remaining
history entry. The native input position and source control are irrelevant
to undoing the source work fields, so the former is explicit. -/
private def enumCont_undoCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨some none, p, (enumCont_logCfg c h).workTapes,
    tapeBlocks c.workTapePos ((h.length : ℤ) - 1) (fun _ => (h.length : ℤ) - 1), []⟩

/-- The completed restoration retains exactly the source's initial work
fields and leaves every history tape blank with its head at zero. -/
private def enumCont_undoResult {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨none, p, (enumCont_logCfg c []).workTapes,
    tapeBlocks c.workTapePos 0 (fun _ => 0), []⟩

/-- Undoing a tape write at the old head restores its original contents,
including no-write actions and writes of blank. -/
private lemma enumCont_restore_cell {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (i : Fin k) :
    Function.update ((a.apply c).workTapes i) (c.workTapePos i) (c.workTapeSymbols i) =
      c.workTapes i := by
  rw [Action.apply_workTapes, Function.update_idem]
  exact Function.update_eq_self _ _

/-- Erasing the last clock mark exposes exactly the preceding clock word. -/
private lemma enumCont_clock_erase (n : ℕ) :
    Function.update (bufferTape (List.replicate (n + 1) true)) (n : ℤ) none =
      bufferTape (List.replicate n true) := by
  rw [List.replicate_add, List.replicate_one, bufferTape_append,
    List.length_replicate, Function.update_idem]
  have hblank : bufferTape (List.replicate n true) (n : ℤ) = none := by simp
  rw [← hblank]
  exact Function.update_eq_self _ _

/-- Between inverse movement and inverse writing, the source heads are back
at their old positions and the last history entry is already erased. -/
private def enumCont_undoMid {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨some (some c.workTapeSymbols), p, (enumCont_logCfg (a.apply c) h).workTapes,
    tapeBlocks c.workTapePos (h.length : ℤ) (fun _ => h.length), []⟩

/-- The first restoration transition reverses the last source head moves,
retains the old symbols in finite control, and erases their history cells.
**Proof sketch.** At the newest clock mark, the parallel tracks read the
last appended entry. The inverse displacement returns every source head to
its pre-action location. Single-cell erase identities recover each prefix. -/
private lemma enumCont_undo_back {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step
      (enumCont_undoCfg (a.apply c)
        (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p) =
      enumCont_undoMid c a h p := by
  let u := enumCont_undoCfg (a.apply c)
    (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p
  have hc : u.workTapeSymbols (Fin.natAdd k (Fin.castAdd (k + k) 0)) = some true := by
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
  have ho : (fun i : Fin k => u.workTapeSymbols
      (Fin.natAdd k (Fin.natAdd 1 (Fin.castAdd k i)))) = c.workTapeSymbols := by
    funext i
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks,
      enumCont_sparse]
  have hm : (fun i : Fin k => u.workTapeSymbols
      (Fin.natAdd k (Fin.natAdd 1 (Fin.natAdd k i)))) =
      fun i => enumCont_moveCode (a.workTapes i).2 := by
    funext i
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks,
      enumCont_sparse, Fin.addCases]
    congr 3
    apply Fin.ext
    simp
  change ((enumCont_undoTM k).tm.tr none _ u.workTapeSymbols).apply u = _
  simp only [enumCont_undoTM, hc, Option.isSome_some, ↓reduceIte]
  rw [ho]
  have hm' (i : Fin k) := congrFun hm i
  have herase (f : EnumContEntry k → Option Bool) (b : Option Bool) :
      Function.update (enumCont_sparse (h.map f ++ [b])) (h.length : ℤ) none =
        enumCont_sparse (h.map f) := by
    simpa only [List.length_map] using enumCont_sparse_erase (h.map f) b
  simp only [hm']
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply,
          tapeBlocks, enumCont_clock_erase]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply,
            tapeBlocks, Fin.addCases, herase]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks,
        enumCont_unmove_cast]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks, Fin.addCases]

/-- The second restoration transition writes the retained old symbols and
backs the history heads up to the preceding entry. -/
private lemma enumCont_undo_write {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step (enumCont_undoMid c a h p) =
      enumCont_undoCfg c h p := by
  change ((enumCont_undoTM k).tm.tr (some c.workTapeSymbols) _ _).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg,
        Action.apply, tapeBlocks] using enumCont_restore_cell c a j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg,
          Action.apply, tapeBlocks]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, Action.apply,
          tapeBlocks, sub_eq_add_neg]

/-- With no history left, one silent transition restores the history heads
to zero and halts. This also handles a source that took no steps. -/
private lemma enumCont_undo_empty {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step (enumCont_undoCfg c [] p) =
      enumCont_undoResult c p := by
  change ((enumCont_undoTM k).tm.tr none _ _).apply _ = _
  have hc : (enumCont_undoCfg c [] p).workTapeSymbols
      (Fin.natAdd k (Fin.castAdd (k + k) 0)) = none := by
    simp [enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
  simp only [enumCont_undoTM, hc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]

/-- A logged live source prefix can be completely undone in `2t+1` steps.
The theorem restores the full original work tapes and heads, with blank
history, while preserving any supplied native input position.
**Proof sketch.** Peel the last source action. Two proved transitions first
reverse its moves and erase its history, then restore its overwritten cells.
Induction undoes the shorter prefix; the empty prefix takes one final step. -/
private lemma enumCont_undo_run (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    (enumCont_undoTM M.k).tm.runFrom
      (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p) (2 * t + 1) =
      enumCont_undoResult c₀ p := by
  induction t with
  | zero =>
    simpa only [Nat.mul_zero, Nat.zero_add, MultiTapeTM.runFrom_zero,
      enumCont_history, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
      using enumCont_undo_empty c₀ p
  | succ t ih =>
    have hs : (M.tm.runFrom c₀ t).state ≠ none := hlive t (by omega)
    cases hq : (M.tm.runFrom c₀ t).state with
    | none => exact False.elim (hs hq)
    | some q =>
      have he : 2 * (t + 1) + 1 = 2 + (2 * t + 1) := by omega
      let c := M.tm.runFrom c₀ t
      let a := M.tm.tr q c.inputSymbol c.workTapeSymbols
      have hsrun : M.tm.runFrom c₀ (t + 1) = a.apply c := by
        rw [MultiTapeTM.runFrom_succ_eq_step']
        simp only [MultiTapeTM.step, hq]
        rfl
      have hhist : enumCont_history M.tm c₀ (t + 1) =
          enumCont_history M.tm c₀ t ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)] := by
        simp only [enumCont_history, hq]
        rfl
      have htwo : (enumCont_undoTM M.k).tm.runFrom
          (enumCont_undoCfg (a.apply c)
            (enumCont_history M.tm c₀ t ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p) 2 =
          enumCont_undoCfg c (enumCont_history M.tm c₀ t) p := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
          MultiTapeTM.runFrom_zero, enumCont_undo_back, enumCont_undo_write]
      rw [hsrun, hhist, he, MultiTapeTM.runFrom_add, htwo]
      exact ih (fun j hj => hlive j (by omega))

/-- Any known halted endpoint is reached at the first halting time, with a
live source at every earlier time. The bound is never increased. -/
private lemma enumCont_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c₀ : Cfg k Bool S x) (T : ℕ)
    (hh : (tm.runFrom c₀ T).state = none) :
    ∃ t ≤ T, (∀ j < t, ¬(tm.runFrom c₀ j).Halted) ∧
      tm.runFrom c₀ t = tm.runFrom c₀ T := by
  classical
  have hex : ∃ t, (tm.runFrom c₀ t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  refine ⟨t, ht, fun j hj => Nat.find_min hex hj, ?_⟩
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
  rw [hr, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]

/-- Administrative actions preserve the source bank and only move the native
input and the final capture tape. -/
private def enumCont_bufferAction {L : ℕ} {H : Type}
    (m d : SignType) (q : Option H) : Action (L + 1) Bool H :=
  ⟨m, fun i => (none, if i.val < L then 0 else d), none, q⟩

/-- Entry into restoration moves all history heads from the right blank to
the newest entry, leaving source heads fixed. -/
private def enumCont_undoEntry (k : ℕ) :
    Action (enumCont_undoTM k).k Bool (enumCont_undoTM k).State :=
  ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, .neg)),
    none, some none⟩

/-- A clean subroutine logs and captures a source, undoes all source work,
rewinds the native input and captured word, and halts silently. Its retained
output word lives on the last work tape; it emits no physical output. -/
private def enumCont_cleanTM (M : FinTM Bool) : FinTM Bool where
  k := (enumCont_logTM M).k + 1
  State := M.State ⊕ (Fin 6 ⊕ (enumCont_undoTM M.k).State)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl q => captureAction Sum.inl (.inr (.inl 0))
          ((enumCont_logTM M).tm.tr q inp (fun i => work i.castSucc))
      | .inr (.inr q) => captureAction (fun q => .inr (.inr q)) (.inr (.inl 1))
          ((enumCont_undoTM M.k).tm.tr q inp (fun i => work i.castSucc))
      | .inr (.inl q) => match q.val with
        | 0 => captureAction (fun q => .inr (.inr q)) (.inr (.inl 1))
            (enumCont_undoEntry M.k)
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inl 3)))
        | 3 => enumCont_bufferAction 0 .neg (some (.inr (.inl 4)))
        | 4 => match work (Fin.last (enumCont_logTM M).k) with
          | some _ => enumCont_bufferAction 0 .neg (some (.inr (.inl 4)))
          | none => enumCont_bufferAction 0 .pos (some (.inr (.inl 5)))
        | _ => controlAction 0 none }

/-- Clean administrative configurations expose only the native and capture
heads. The source work fields are already restored and the histories blank. -/
private def enumCont_cleanCfg (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool)
    (q : Option (enumCont_cleanTM M).State) (p : Fin (x.length + 2)) (h : ℤ) :
    Cfg (enumCont_cleanTM M).k Bool (enumCont_cleanTM M).State x :=
  ⟨q, p,
    (fun i => if hi : i.val < (enumCont_logTM M).k then
      (enumCont_logCfg c₀ []).workTapes ⟨i, hi⟩ else bufferTape y),
    (fun i => if hi : i.val < (enumCont_logTM M).k then
      (enumCont_logCfg c₀ []).workTapePos ⟨i, hi⟩ else h), []⟩

/-- The clean subroutine's first phase is the public captured simulation of
the logged source. Halting emissions are retained on the capture tape. -/
private lemma enumCont_clean_capture (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    (enumCont_cleanTM M).tm.runFrom
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
      captureCfg Sum.inl (.inr (.inl 0)) [] []
        (enumCont_logCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t)) := by
  rw [capture_run (enumCont_logTM M).tm (enumCont_cleanTM M).tm Sum.inl (.inr (.inl 0))
    (fun _ _ _ => rfl) [] [] (enumCont_logCfg c₀ []) t]
  · rw [enumCont_log_run]
  · intro j hj
    rw [enumCont_log_run]
    exact hlive j hj

/-- After source halt, one silent dispatch parks every history head on its
last entry and starts the captured restoration, retaining the source output. -/
private lemma enumCont_clean_undo_entry (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (h : List (EnumContEntry M.k))
    (hs : c.state = none) :
    (enumCont_cleanTM M).tm.step
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c h)) =
      captureCfg (fun q => .inr (.inr q)) (.inr (.inl 1)) c.output []
        (enumCont_undoCfg c h c.inputPos) := by
  have hstate : (captureCfg (fun q => (Sum.inl q : (enumCont_cleanTM M).State))
      (.inr (.inl 0)) [] [] (enumCont_logCfg c h)).state = some (.inr (.inl 0)) := by
    simp [captureCfg, enumCont_logCfg, hs]
  simp only [MultiTapeTM.step, hstate]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, captureCfg, enumCont_undoEntry,
        enumCont_logCfg, enumCont_undoCfg, Action.apply]
    · simp only [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, enumCont_undoEntry, captureCfg,
        Fin.coe_castSucc, enumCont_undoCfg, Action.apply,
        enumCont_logCfg, List.nil_append, List.append_nil]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [tapeBlocks, Fin.addCases, j.isLt,
          show j.val < M.k + (1 + (M.k + M.k)) from Nat.lt_of_lt_of_le j.isLt (by omega)]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [tapeBlocks, Fin.addCases, j.isLt]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, captureCfg, enumCont_undoEntry,
        enumCont_logCfg, enumCont_undoCfg, Action.apply]
    · simp only [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, enumCont_undoEntry, captureCfg,
        Fin.coe_castSucc, enumCont_undoCfg, Action.apply,
        enumCont_logCfg]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [tapeBlocks, Fin.addCases, j.isLt,
          show j.val < M.k + (1 + (M.k + M.k)) from Nat.lt_of_lt_of_le j.isLt (by omega)]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [tapeBlocks, Fin.addCases, sub_eq_add_neg]

/-- The captured restoration returns within `2t+1` steps with the original
source work restored and its completed output retained separately.
**Proof sketch.** Take the restoration machine's first halt below its proved
exact bound, apply `capture_run`, and identify the returned configuration
field by field. Its empty output appends nothing to the retained source word. -/
private lemma enumCont_clean_restore (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    ∃ r ≤ 2 * t + 1,
      (enumCont_cleanTM M).tm.runFrom
        (captureCfg (fun q => .inr (.inr q)) (.inr (.inl 1))
          (M.tm.runFrom c₀ t).output []
          (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p)) r =
        enumCont_cleanCfg M c₀ (M.tm.runFrom c₀ t).output
          (some (.inr (.inl 1))) p ((M.tm.runFrom c₀ t).output.length : ℤ) := by
  have hu := enumCont_undo_run M c₀ p t hlive
  obtain ⟨r, hr, hl, he⟩ := enumCont_first_halt (enumCont_undoTM M.k).tm
    (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p)
    (2 * t + 1) (by rw [hu]; rfl)
  refine ⟨r, hr, ?_⟩
  rw [capture_run (enumCont_undoTM M.k).tm (enumCont_cleanTM M).tm
    (fun q => .inr (.inr q)) (.inr (.inl 1)) (fun _ _ _ => rfl)
    _ [] _ r hl, he, hu]
  simp [captureCfg, enumCont_undoResult, enumCont_cleanCfg, enumCont_logCfg,
    enumCont_logTM, enumCont_undoTM]
  exact ⟨rfl, rfl⟩

/-- Moving the clean subroutine's two exposed heads preserves every tape and
the empty physical output. -/
private lemma enumCont_buffer_apply (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool)
    (q q' : Option (enumCont_cleanTM M).State) (p : Fin (x.length + 2)) (h : ℤ)
    (m d : SignType) :
    (enumCont_bufferAction m d q').apply (enumCont_cleanCfg M c₀ y q p h) =
      enumCont_cleanCfg M c₀ y q' (moveInputPos p m) (h + d.cast) := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext i
  by_cases hi : i.val < (enumCont_logTM M).k <;>
    simp [enumCont_bufferAction, enumCont_cleanCfg, Action.apply, hi]

/-- A mandatory left step followed by a boundary scan restores the native
head in at most its old position plus two steps. This private derivation
uses the proved `rewind_scan`, following the timed wrapper's template. -/
private lemma enumCont_rewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- The retained output word rewinds without being erased. Starting just
left of cell `j`, the scan returns its head to zero in exactly `j+1` steps. -/
private lemma enumCont_clean_buffer_rewind (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool) (p : Fin (x.length + 2)) :
    ∀ j, j ≤ y.length →
      (enumCont_cleanTM M).tm.runFrom
        (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((j : ℤ) - 1)) (j + 1) =
        enumCont_cleanCfg M c₀ y (some (.inr (.inl 5))) p 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((enumCont_cleanTM M).tm.tr (.inr (.inl 4)) _ _).apply _ = _
    have hr : (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((0 : ℤ) - 1)).workTapeSymbols
        (Fin.last (enumCont_logTM M).k) = none := by
      simp [enumCont_cleanCfg, Cfg.workTapeSymbols]
    simp only [enumCont_cleanTM, Nat.cast_zero]
    rw [hr, enumCont_buffer_apply]
    simp [SignType.cast]
  | succ j ih =>
    intro hj
    have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
    rw [hz, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (enumCont_cleanTM M).tm.step
        (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p j) =
        enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((j : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((enumCont_cleanTM M).tm.tr (.inr (.inl 4)) _ _).apply _ = _
      have hr : (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p j).workTapeSymbols
          (Fin.last (enumCont_logTM M).k) = some (y[j]'(by omega)) := by
        simp [enumCont_cleanCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < y.length)]
      simp only [enumCont_cleanTM, hr]
      rw [enumCont_buffer_apply]
      simp [SignType.cast, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- A halting source call can be made clean: retain its output on the final
tape, restore every source work field, blank all histories, and rewind both
exposed heads. The full duration is at most `3T+|x|+|y|+8`.
**Proof sketch.** Capture the logged run through its first halt; undo the
recorded actions; rewind native input; rewind the retained word; halt. Each
administrative transition is charged, and all phases keep physical output
empty. Only the actual source time is used in the restoration bound. -/
private lemma enumCont_clean_complete (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool) (T : ℕ)
    (hh : (M.tm.runFrom c₀ T).state = none)
    (ho : (M.tm.runFrom c₀ T).output = y) :
    ∃ τ ≤ 3 * T + x.length + y.length + 8,
      (enumCont_cleanTM M).tm.runFrom
        (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) τ =
        enumCont_cleanCfg M c₀ y none 1 0 := by
  obtain ⟨t, ht, hlive, he⟩ := enumCont_first_halt M.tm c₀ T hh
  have hs : (M.tm.runFrom c₀ t).state = none := by rw [he]; exact hh
  have hout : (M.tm.runFrom c₀ t).output = y := by rw [he]; exact ho
  have hcap := enumCont_clean_capture M c₀ t hlive
  have hentry := enumCont_clean_undo_entry M (M.tm.runFrom c₀ t)
    (enumCont_history M.tm c₀ t) hs
  obtain ⟨r, hr, hrest⟩ := enumCont_clean_restore M c₀ (M.tm.runFrom c₀ t).inputPos t hlive
  have hfirst : (enumCont_cleanTM M).tm.runFrom
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) (t + 1 + r) =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
        (M.tm.runFrom c₀ t).inputPos (y.length : ℤ) := by
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step', hcap, hentry, hrest, hout]
  obtain ⟨u, hu, hrew⟩ := enumCont_rewind (enumCont_cleanTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inl 3)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
      (M.tm.runFrom c₀ t).inputPos (y.length : ℤ)) rfl
  have hrew' : (enumCont_cleanTM M).tm.runFrom
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
        (M.tm.runFrom c₀ t).inputPos (y.length : ℤ)) u =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 3))) 1 (y.length : ℤ) := hrew
  have hback : (enumCont_cleanTM M).tm.step
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 3))) 1 (y.length : ℤ)) =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) 1 ((y.length : ℤ) - 1) := by
    change (enumCont_bufferAction 0 .neg _).apply _ = _
    rw [enumCont_buffer_apply]
    simp [sub_eq_add_neg, SignType.cast]
  have hlast : (enumCont_cleanTM M).tm.step
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 5))) 1 0) =
      enumCont_cleanCfg M c₀ y none 1 0 := by
    change (controlAction 0 none).apply _ = _
    rw [controlAction_apply]
    simp [moveInputPos_zero, enumCont_cleanCfg]
  refine ⟨t + 1 + r + u + 1 + (y.length + 1) + 1, ?_, ?_⟩
  · change u ≤ (M.tm.runFrom c₀ t).inputPos.val + 2 at hu
    have hp := (M.tm.runFrom c₀ t).inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_add _ _ (y.length + 1),
      MultiTapeTM.runFrom_succ_eq_step' (t := t + 1 + r + u),
      MultiTapeTM.runFrom_add _ _ u, hfirst, hrew', hback,
      enumCont_clean_buffer_rewind M c₀ y 1 y.length (le_refl _), hlast]

/-- The assembly source emits native input followed by the candidate already
on its sole work tape. Its two phases never write the candidate. -/
private def enumCont_concatTM : FinTM Bool where
  k := 1
  State := Bool
  tm := {
    q₀ := false
    tr := fun q inp work =>
      if q then match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some true⟩
        | none => controlAction 0 none
      else match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some false⟩
        | none => controlAction 0 (some true) }

/-- Assembly configurations keep the candidate word fixed while exposing
the input head, candidate head, and emitted prefix. -/
private def enumCont_concatCfg (x s : List Bool) (q : Option Bool)
    (p : Fin (x.length + 2)) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool Bool x := ⟨q, p, fun _ => bufferTape s, fun _ => z, out⟩

/-- The native-input scan emits exactly the remaining input and switches to
the candidate phase, preserving the candidate and its head at zero.
**Proof sketch.** Induct on the remaining native suffix. A bit is emitted
and advances the native head; the right blank takes one silent phase change. -/
private lemma enumCont_concat_native (x s pre rest : List Bool) (hx : x = pre ++ rest) :
    enumCont_concatTM.tm.runFrom
      (enumCont_concatCfg x s (some false) ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre)
      (rest.length + 1) =
      enumCont_concatCfg x s (some true) (Fin.last (x.length + 1)) 0 x := by
  induction rest generalizing pre with
  | nil =>
    have hp : x = pre := by simpa using hx
    subst pre
    simp only [List.length_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have hr : (enumCont_concatCfg x s (some false) ⟨x.length + 1, by omega⟩ 0 x).inputSymbol =
        none := by simp [enumCont_concatCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (enumCont_concatTM.tm.tr false _ _).apply _ = _
    simp only [enumCont_concatTM, Bool.false_eq_true, ↓reduceIte, hr]
    rw [controlAction_apply]
    simp [moveInputPos_zero, enumCont_concatCfg]
    rfl
  | cons b rest ih =>
    have hread : (enumCont_concatCfg x s (some false)
        ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre).inputSymbol = some b := by
      rw [inputSymbol_at _ pre.length (by simp [hx]) rfl]
      simp [hx]
    have hstep : enumCont_concatTM.tm.step
        (enumCont_concatCfg x s (some false) ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre) =
        enumCont_concatCfg x s (some false)
          ⟨(pre ++ [b]).length + 1, by simp [hx]⟩ 0 (pre ++ [b]) := by
      unfold MultiTapeTM.step
      change (enumCont_concatTM.tm.tr false _ _).apply _ = _
      simp only [enumCont_concatTM, Bool.false_eq_true, ↓reduceIte, hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · apply Fin.ext
        dsimp only [Action.apply, enumCont_concatCfg]
        rw [moveInputPos_pos_of_ne_right _ (by simp [hx])]
        simp
      · funext i; simp [Action.apply, enumCont_concatCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (pre ++ [b]) (by simpa only [List.append_assoc, List.singleton_append] using hx)

/-- The candidate scan appends the exact tape word to the emitted native
input and halts at its right blank. Empty candidates take the final step. -/
private lemma enumCont_concat_candidate (x s pre rest : List Bool) (p : Fin (x.length + 2)) (out : List Bool)
    (hs : s = pre ++ rest) :
    enumCont_concatTM.tm.runFrom
      (enumCont_concatCfg x s (some true) p pre.length (out ++ pre))
      (rest.length + 1) =
      enumCont_concatCfg x s none p s.length (out ++ s) := by
  induction rest generalizing pre with
  | nil =>
    have hp : s = pre := by simpa using hs
    subst pre
    simp only [List.length_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (enumCont_concatTM.tm.tr true _ _).apply _ = _
    simp only [enumCont_concatTM, ↓reduceIte, enumCont_concatCfg, Cfg.workTapeSymbols,
      bufferTape_nat, List.getElem?_length]
    rw [controlAction_apply]
    simp [moveInputPos_zero]
  | cons b rest ih =>
    have hr : (enumCont_concatCfg x s (some true) p
        pre.length (out ++ pre)).workTapeSymbols 0 = some b := by
      simp [enumCont_concatCfg, Cfg.workTapeSymbols, hs]
    have hstep : enumCont_concatTM.tm.step
        (enumCont_concatCfg x s (some true) p pre.length (out ++ pre)) =
        enumCont_concatCfg x s (some true) p
          (pre ++ [b]).length (out ++ (pre ++ [b])) := by
      unfold MultiTapeTM.step
      change (enumCont_concatTM.tm.tr true _ _).apply _ = _
      simp only [enumCont_concatTM, ↓reduceIte, hr]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext i; simp [enumCont_concatCfg, Action.apply]
      · simp [enumCont_concatCfg, Action.apply, List.append_assoc]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (pre ++ [b]) (by simpa only [List.append_assoc, List.singleton_append] using hs)

/-- Assembly from the candidate seam emits exactly `x ++ s` in
`|x|+|s|+2` steps. The fixed candidate tape is retained. -/
private lemma enumCont_concat_run (x s : List Bool) :
    enumCont_concatTM.tm.runFrom
      (Cfg.ofWords (input := x) false (fun _ => s)) (x.length + s.length + 2) =
      enumCont_concatCfg x s none (Fin.last (x.length + 1)) s.length (x ++ s) := by
  have hn := enumCont_concat_native x s [] x rfl
  have hs := enumCont_concat_candidate x s [] s (Fin.last (x.length + 1)) x rfl
  simp only [List.length_nil, List.append_nil, Nat.zero_add,
    Nat.cast_zero] at hn hs
  have hp : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by apply Fin.ext; simp
  rw [hp] at hn
  change enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some false) 1 0 []) _ = _
  rw [show x.length + s.length + 2 = (x.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hn, hs]

/-- Buffered composition also works from a prepared first-machine work
configuration. Its second machine still receives genuine fresh work tapes.
**Proof sketch.** Use the first source halt, the public buffered lockstep and
rewind equations, then the public relocated second-phase simulation. -/
private lemma enumCont_prepared_comp (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M₁.k Bool M₁.State x) (y z : List Bool) (T₁ T₂ : ℕ)
    (hh : (M₁.tm.runFrom c₀ T₁).state = none)
    (ho : (M₁.tm.runFrom c₀ T₁).output = y)
    (h₂ : M₂.ComputesInTime y z T₂) :
    ∃ t ≤ T₁ + y.length + 2 + T₂,
      ((bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c₀) t).state = none ∧
      ((bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c₀) t).output = z := by
  obtain ⟨t, ht, hlive, he⟩ := enumCont_first_halt M₁.tm c₀ T₁ hh
  let c := M₁.tm.runFrom c₀ t
  have hs : c.state = none := by dsimp [c]; rw [he]; exact hh
  have hout : c.output = y := by dsimp [c]; rw [he]; exact ho
  have hfirst := bufferedFirstCfg_run M₁ M₂ c₀ t hlive
  have hrew := bufferedFirstCfg_rewind M₁ M₂ c hs
  obtain ⟨tag, _, hrun⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg c.output) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
    c.inputPos c.workTapes c.workTapePos T₂
  have h₂' : (M₂.tm.runFrom (M₂.tm.initCfg c.output) T₂).state = none ∧
      (M₂.tm.runFrom (M₂.tm.initCfg c.output) T₂).output = z := by
    rw [hout]
    exact (computesInTime_iff _ _ _ _).mp h₂
  refine ⟨t + (c.output.length + 2) + T₂, by rw [hout]; omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hfirst, hrew, hrun]
  exact ⟨by simp only [bufferedSecondCfg, h₂'.1, Option.map_none], h₂'.2⟩

/-- The prepared assembly source occupies tape zero; the composition buffer
and verifier work tapes are exactly blank at the candidate seam. -/
private lemma enumCont_round_seam (MV : FinTM Bool) (x s : List Bool) (phase : Bool) :
    bufferedFirstCfg enumCont_concatTM MV (Cfg.ofWords (input := x) phase (fun _ => s)) =
      Cfg.ofWords (.inl (some phase) : (bufferedCompTM enumCont_concatTM MV).State)
        (stateWord (bufferedCompTM enumCont_concatTM MV).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
      simp [bufferedFirstCfg, Cfg.ofWords, stateWord, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [bufferedFirstCfg, Cfg.ofWords, stateWord, tapeBlocks, enumCont_concatTM]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [bufferedFirstCfg, Cfg.ofWords, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [bufferedFirstCfg, Cfg.ofWords, tapeBlocks]

/-- The prepared verifier call accepts the exact assembled input `x ++ s`.
Its bound includes assembly, the buffer rewind, and the verifier's actual
polynomial budget on that input. -/
private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
    ∃ t ≤ a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4,
      ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
        (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
          (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).state = none ∧
      ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
        (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
          (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).output =
        [MultiTapeTM.indicator V (x ++ s)] := by
  obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM MV
    (Cfg.ofWords (input := x) false (fun _ => s)) (x ++ s)
    [MultiTapeTM.indicator V (x ++ s)] (x.length + s.length + 2)
    (a * ((x ++ s).length + 1) ^ d)
    (by rw [enumCont_concat_run]; rfl) (by rw [enumCont_concat_run]; rfl) (hV (x ++ s))
  rw [enumCont_round_seam MV x s false] at hh ho
  simp only [List.length_append] at ht
  exact ⟨t, by omega, hh, ho⟩

/-- Relabel live states and redirect halt to a live return state, preserving
the complete action. This wrapper is used only for already-silent calls. -/
private def enumCont_returnAction {k : ℕ} {S H : Type}
    (emb : S → H) (ret : H) (a : Action k Bool S) : Action k Bool H :=
  ⟨a.inputTape, a.workTapes, a.output, some ((a.state.map emb).getD ret)⟩

/-- The live-return correspondence preserves all configuration fields except
the control state, including work-tape results. -/
private def enumCont_returnCfg {k : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (ret : H) (c : Cfg k Bool S x) : Cfg k Bool H x :=
  ⟨some ((c.state.map emb).getD ret), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- A host with the redirected transition table simulates a source through
its first halt and returns the exact completed configuration.
**Proof sketch.** One redirected action commutes with the configuration map.
Induct through live source steps; a halting action selects the live return
state while preserving its final writes and output. -/
private lemma enumCont_return_run {k : ℕ} {S H : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (ret : H)
    (htr : ∀ q inp work, host.tr (emb q) inp work =
      enumCont_returnAction emb ret (tm.tr q inp work))
    (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c₀ j).Halted) :
    host.runFrom (enumCont_returnCfg emb ret c₀) t =
      enumCont_returnCfg emb ret (tm.runFrom c₀ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    have hs : (tm.runFrom c₀ t).state ≠ none := hlive t (by omega)
    cases hq : (tm.runFrom c₀ t).state with
    | none => exact False.elim (hs hq)
    | some q =>
      simp only [MultiTapeTM.step, enumCont_returnCfg, hq, Option.map_some, Option.getD_some]
      rw [htr]
      rfl

/-- Combining the prepared verifier call with the clean wrapper gives a
repeatable call: the candidate is retained, all other original source work
is restored to blank, and the sole verdict is held on the capture tape.
The concrete body still has to dispatch, clear that verdict, and increment. -/
private lemma enumCont_clean_verifier (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
    let Q := bufferedCompTM enumCont_concatTM MV
    let c₀ := Cfg.ofWords (input := x) Q.tm.q₀ (stateWord Q.k s)
    ∃ t ≤ 3 * (a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4) +
        x.length + 9,
      (enumCont_cleanTM Q).tm.runFrom
        (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
        enumCont_cleanCfg Q c₀ [MultiTapeTM.indicator V (x ++ s)] none 1 0 := by
  dsimp only
  obtain ⟨t, ht, hh, ho⟩ := enumCont_verifier_call MV V a d hV x s
  obtain ⟨r, hr, he⟩ := enumCont_clean_complete (bufferedCompTM enumCont_concatTM MV)
    (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
      (stateWord (bufferedCompTM enumCont_concatTM MV).k s))
    [MultiTapeTM.indicator V (x ++ s)] t hh ho
  exact ⟨r, by simp only [List.length_singleton] at hr; omega, he⟩

/-- Pad an action with inactive high tapes and embed its finite control. -/
private def enumCont_padAction {k K : ℕ} {S H : Type}
    (emb : S → H) (a : Action k Bool S) : Action K Bool H :=
  ⟨a.inputTape, fun i => if hi : i.val < k then a.workTapes ⟨i, hi⟩ else (none, 0),
    a.output, a.state.map emb⟩

/-- Pad a source configuration with blank stationary high tapes. -/
private def enumCont_padCfg {k K : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (c : Cfg k Bool S x) : Cfg K Bool H x :=
  ⟨c.state.map emb, c.inputPos,
    (fun i => if hi : i.val < k then c.workTapes ⟨i, hi⟩ else fun _ => none),
    (fun i => if hi : i.val < k then c.workTapePos ⟨i, hi⟩ else 0), c.output⟩

/-- Padding commutes with one action; the new high tapes remain blank. -/
private lemma enumCont_pad_apply {k K : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (c : Cfg k Bool S x) (a : Action k Bool S) :
    (enumCont_padAction (K := K) emb a).apply (enumCont_padCfg emb c) =
      enumCont_padCfg emb (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val < k <;> simp [enumCont_padAction, enumCont_padCfg, Action.apply, hi]
  · funext i
    by_cases hi : i.val < k <;> simp [enumCont_padAction, enumCont_padCfg, Action.apply, hi]

/-- A machine may run on an initial tape block of a larger controller.
**Proof sketch.** The source-block reads agree when the source fits. One
step commutes with padding, including the absorbing halted case; iterate. -/
private lemma enumCont_pad_run {k K : ℕ} {S H : Type} {x : List Bool}
    (hk : k ≤ K) (tm : MultiTapeTM k Bool S) (host : MultiTapeTM K Bool H)
    (emb : S → H)
    (htr : ∀ q inp work, host.tr (emb q) inp work =
      enumCont_padAction emb (tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (c : Cfg k Bool S x) (t : ℕ) :
    host.runFrom (enumCont_padCfg emb c) t = enumCont_padCfg emb (tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step (enumCont_padCfg emb) ?_ c t
  intro c
  cases hq : c.state with
  | none => simp only [MultiTapeTM.step, enumCont_padCfg, hq, Option.map_none]
  | some q =>
    have hs : (enumCont_padCfg (K := K) emb c).state = some (emb q) := by
      simp only [enumCont_padCfg, hq, Option.map_some]
    have hw : (fun i : Fin k => (enumCont_padCfg (K := K) emb c).workTapeSymbols
        ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i
      simp [enumCont_padCfg, Cfg.workTapeSymbols, i.isLt]
    have hin : (enumCont_padCfg (K := K) emb c).inputSymbol = c.inputSymbol := rfl
    simp only [MultiTapeTM.step, hs, hq]
    rw [htr, hw, hin, enumCont_pad_apply]

/-- Three finite source routines share a common padded tape block. The
startup routine is the initial branch; prepared calls may select either
other branch without moving their candidate off tape zero. -/
private def enumCont_sources (Q R U : FinTM Bool) : FinTM Bool where
  k := Q.k + R.k + U.k
  State := Q.State ⊕ (R.State ⊕ U.State)
  tm := {
    q₀ := .inr (.inr U.tm.q₀)
    tr := fun q inp work => match q with
      | .inl q => enumCont_padAction Sum.inl
          (Q.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩))
      | .inr (.inl q) => enumCont_padAction (fun q => .inr (.inl q))
          (R.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩))
      | .inr (.inr q) => enumCont_padAction (fun q => .inr (.inr q))
          (U.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩)) }

/-- Move or write the candidate at tape zero and the final capture tape,
preserving every intervening tape. -/
private def enumCont_endsAction {L : ℕ} {H : Type}
    (a b : Option (Option Bool)) (d : SignType) (q : Option H) : Action (L + 1) Bool H :=
  ⟨0, fun i => if i.val = 0 then (a, d) else if i.val = L then (b, d) else (none, 0), none, q⟩

/-- The concrete body uses one clean source block for initialization,
verification, and increment. Administrative states are the anchor (0),
seed copy (1), unused reserve (2), verdict (3), increment check (4), result
copy (5), and synchronized rewind (6). The stopped variant freezes only
the anchor and is used to certify first returns without an interior visit. -/
private def enumCont_bodyTM (B : FinTM Bool) (qverify qinc : B.State) (stopped : Bool) :
    FinTM Bool where
  k := (enumCont_logTM B).k + 1
  State := ((enumCont_cleanTM B).State × Fin 3) ⊕ Fin 7
  tm := {
    q₀ := .inl ((enumCont_cleanTM B).tm.q₀, 0)
    tr := fun q inp work => match q with
      | .inl (q, mode) => enumCont_returnAction (fun q => .inl (q, mode))
          (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4))
          ((enumCont_cleanTM B).tm.tr q inp work)
      | .inr q => match q.val with
        | 0 => if stopped then controlAction 0 (some (.inr 0))
            else controlAction 0 (some (.inl (.inl qverify, 1)))
        | 3 => match work (Fin.last (enumCont_logTM B).k) with
          | some true => ⟨0, fun _ => (none, 0), some true, none⟩
          | _ => ⟨0, fun i => (if i.val = (enumCont_logTM B).k then some none else none, 0),
              none, some (.inl (.inl qinc, 2))⟩
        | 4 => if work (Fin.last (enumCont_logTM B).k) = none then
              controlAction 0 (some (.inr 0))
            else controlAction 0 (some (.inr 5))
        | 6 => match work 0 with
          | some _ => enumCont_endsAction none none .neg (some (.inr 6))
          | none => enumCont_endsAction none none .pos (some (.inr 0))
        | _ => match work (Fin.last (enumCont_logTM B).k) with
          | some b => enumCont_endsAction (some (some (if q.val = 1 then false else b)))
              (some none) .pos (some (.inr q))
          | none => enumCont_endsAction none none .neg (some (.inr 6)) }

/-- Starting assembly in its candidate phase supplies just that candidate to
the catalog incrementer. Its output is empty exactly on overflow; a clean
wrapper will retain the original candidate for that branch. -/
private lemma enumCont_increment_call (I : FinTM Bool) (j : ℕ)
    (hI : I.ComputesFunInTime (fun s => (incFixed s).getD []) (fun n => j * (n + 1)))
    (x s : List Bool) :
    ∃ t ≤ (j + 3) * (s.length + 1),
      ((bufferedCompTM enumCont_concatTM I).tm.runFrom
        (Cfg.ofWords (input := x) (.inl (some true))
          (stateWord (bufferedCompTM enumCont_concatTM I).k s)) t).state = none ∧
      ((bufferedCompTM enumCont_concatTM I).tm.runFrom
        (Cfg.ofWords (input := x) (.inl (some true))
          (stateWord (bufferedCompTM enumCont_concatTM I).k s)) t).output =
        (incFixed s).getD [] := by
  have hs := enumCont_concat_candidate x s [] s 1 [] rfl
  simp only [List.length_nil, List.nil_append, Nat.cast_zero] at hs
  obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM I
    (Cfg.ofWords (input := x) true (fun _ => s)) s ((incFixed s).getD [])
    (s.length + 1) (j * (s.length + 1))
    (by change (enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some true) 1 0 []) _).state = none
        rw [hs]; rfl)
    (by change (enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some true) 1 0 []) _).output = s
        rw [hs]; rfl) (hI s)
  rw [enumCont_round_seam I x s true] at hh ho
  refine ⟨t, ht.trans ?_, hh, ho⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Padding preserves the candidate-on-zero convention when the source has
at least one work tape. All added tapes are blank and parked at zero. -/
private lemma enumCont_pad_words {k K : ℕ} {S H : Type} (hk : 0 < k) (_hle : k ≤ K)
    (emb : S → H) (q : S) (x s : List Bool) :
    enumCont_padCfg (K := K) emb (Cfg.ofWords (input := x) q (stateWord k s)) =
      Cfg.ofWords (emb q) (stateWord K s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val < k
    · simp [enumCont_padCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [enumCont_padCfg, Cfg.ofWords, stateWord, hi, hn]
  · funext i
    simp [enumCont_padCfg, Cfg.ofWords]

/-- The same padding identity for empty initial work is valid even when the
source machine has no work tapes. -/
private lemma enumCont_pad_init {k K : ℕ} {S H : Type} (emb : S → H)
    (q : S) (x : List Bool) :
    enumCont_padCfg (k := k) (K := K) emb (Cfg.init q x) =
      Cfg.ofWords (emb q) (stateWord K []) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    simp [enumCont_padCfg, Cfg.init, Cfg.ofWords, stateWord]
  · funext i
    simp [enumCont_padCfg, Cfg.init, Cfg.ofWords]

/-- Overwriting the first remaining candidate cell extends the completed
prefix and drops the old cell, also when the old word is initially empty. -/
private lemma enumCont_overwrite (pre old : List Bool) (b : Bool) :
    Function.update (bufferTape (pre ++ old)) (pre.length : ℤ) (some b) =
      bufferTape (pre ++ b :: old.drop 1) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : z.toNat ≠ pre.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hp : 0 < z.toNat - pre.length := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
        rw [hm]
        cases old <;> simp
    · simp [bufferTape, h0]

/-- The erased capture prefix consists entirely of blanks. Replacing its
next symbol by blank increases that prefix by one cell. -/
private lemma enumCont_sparse_clear (p : ℕ) (b : Bool) (rest : List Bool) :
    Function.update (enumCont_sparse (List.replicate p none ++ (b :: rest).map some))
      (p : ℤ) none =
      enumCont_sparse (List.replicate (p + 1) none ++ rest.map some) := by
  funext z
  by_cases hz : z = (p : ℤ)
  · subst z; simp [enumCont_sparse, List.getElem?_append]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : z.toNat ≠ p := by omega
      by_cases hp : z.toNat < p
      · simp [enumCont_sparse, h0, List.getElem?_append, hp,
          show z.toNat < p + 1 by omega]
      · simp [enumCont_sparse, h0, List.getElem?_append, hp,
          show ¬z.toNat < p + 1 by omega,
          show z.toNat - p = (z.toNat - (p + 1)) + 1 by omega]
    · simp [enumCont_sparse, h0]

/-- Tape configurations for the administrative copy and rewind scans. Only
the candidate and final capture tape may be nonblank; their heads coincide. -/
private def enumCont_pairCfg {L : ℕ} {S : Type} {x : List Bool}
    (q : Option S) (u v : ℤ → Option Bool) (h : ℤ) : Cfg (L + 1) Bool S x :=
  ⟨q, 1, (fun i => if i.val = 0 then u else if i.val = L then v else fun _ => none),
    (fun i => if i.val = 0 ∨ i.val = L then h else 0), []⟩

/-- The two-ended administrative action changes exactly those tape cells and
their common head, preserving native input and physical silence. -/
private lemma enumCont_ends_apply {L : ℕ} {S : Type} {x : List Bool} (_hL : 0 < L)
    (q q' : Option S) (u v : ℤ → Option Bool) (h : ℤ)
    (a b : Option (Option Bool)) (d : SignType) :
    (enumCont_endsAction (L := L) a b d q').apply (enumCont_pairCfg (x := x) q u v h) =
      enumCont_pairCfg q' (Function.update u h (a.getD (u h)))
        (Function.update v h (b.getD (v h))) (h + (d : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      cases a <;> simp [enumCont_endsAction, enumCont_pairCfg, Action.apply,
        Function.update_eq_self]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = L
      · cases b <;> simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl,
          Function.update_eq_self]
      · simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl]
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      simp [enumCont_endsAction, enumCont_pairCfg, Action.apply]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = L <;>
        simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl]

/-- A sparse list of blank entries is an everywhere blank tape. -/
private lemma enumCont_sparse_blanks (n : ℕ) :
    enumCont_sparse (List.replicate n none) = fun _ => none := by
  funext z
  by_cases hz : 0 ≤ z <;> by_cases hn : z.toNat < n <;>
    simp [enumCont_sparse, hz, hn]

/-- Lifting every word symbol into the sparse representation gives the usual
buffer tape. -/
private lemma enumCont_sparse_some (w : List Bool) :
    enumCont_sparse (w.map some) = bufferTape w := by
  funext z
  by_cases hz : 0 ≤ z
  · simp only [enumCont_sparse, bufferTape, if_pos hz, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · simp [enumCont_sparse, bufferTape, hz]

/-- The copy scan overwrites the candidate from left to right and erases each
captured symbol. The old suffix is explicit, so initialization from an empty
candidate and replacement of an equal-width candidate share this proof.
**Proof sketch.** One step uses the overwrite and sparse-clear identities;
induct on the remaining captured suffix. Its right blank starts rewind. -/
private lemma enumCont_copy_scan {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qc qr : S) (f : Bool → Bool)
    (htr : ∀ inp work, tm.tr qc inp work = match work (Fin.last L) with
      | some b => enumCont_endsAction (some (some (f b))) (some none) .pos (some qc)
      | none => enumCont_endsAction none none .neg (some qr))
    (pre old rest : List Bool) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qc) (bufferTape (pre ++ old))
      (enumCont_sparse (List.replicate pre.length none ++ rest.map some)) pre.length)
      (rest.length + 1) =
      enumCont_pairCfg (some qr) (bufferTape (pre ++ rest.map f ++ old.drop rest.length))
        (fun _ => none) ((pre.length : ℤ) + rest.length - 1) := by
  induction rest generalizing pre old with
  | nil =>
    have hv : enumCont_sparse (List.replicate pre.length none ++ ([] : List Bool).map some) =
        (fun _ => none) := by simpa using enumCont_sparse_blanks pre.length
    rw [hv]
    simp only [List.length_nil, Nat.zero_add, List.map_nil, List.drop_zero, List.append_nil,
      Int.natCast_zero, add_zero]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    change (tm.tr qc _ _).apply _ = _
    rw [htr]
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qc) (bufferTape (pre ++ old))
        (fun _ => none) pre.length).workTapeSymbols (Fin.last L) = none := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols, Nat.ne_of_gt hL]
    rw [hr, enumCont_ends_apply hL]
    simp only [Option.getD_none, Function.update_eq_self]
    simp [sub_eq_add_neg]
  | cons b rest ih =>
    let c := enumCont_pairCfg (L := L) (x := x) (some qc) (bufferTape (pre ++ old))
      (enumCont_sparse (List.replicate pre.length none ++ (b :: rest).map some)) pre.length
    have hr : c.workTapeSymbols (Fin.last L) = some b := by
      simp [c, enumCont_pairCfg, Cfg.workTapeSymbols, Nat.ne_of_gt hL, enumCont_sparse]
    have he : tm.step c = enumCont_pairCfg (some qc)
        (bufferTape ((pre ++ [f b]) ++ old.drop 1))
        (enumCont_sparse (List.replicate (pre ++ [f b]).length none ++ rest.map some))
        (pre ++ [f b]).length := by
      change (tm.tr qc _ _).apply c = _
      rw [htr, hr]
      dsimp only [c]
      rw [enumCont_ends_apply hL]
      simp only [Option.getD_some, enumCont_overwrite, enumCont_sparse_clear,
        List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      simp [List.append_assoc]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, he, ih]
    simp [List.map_cons, List.append_assoc, add_comm, add_left_comm]

/-- Rewind the two endpoint heads together across the completed candidate.
The left blank takes one positive move, restoring both heads to cell zero. -/
private lemma enumCont_pair_rewind {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qr qa : S)
    (htr : ∀ inp work, tm.tr qr inp work = match work 0 with
      | some _ => enumCont_endsAction none none .neg (some qr)
      | none => enumCont_endsAction none none .pos (some qa))
    (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qr) (bufferTape w) (fun _ => none) (j - 1))
      (j + 1) = enumCont_pairCfg (some qa) (bufferTape w) (fun _ => none) 0 := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    change (tm.tr qr _ _).apply _ = _
    rw [htr]
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qr) (bufferTape w)
        (fun _ => none) (0 - 1)).workTapeSymbols 0 = none := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols]
    simp only [Nat.cast_zero]
    rw [hr, enumCont_ends_apply hL]
    simp only [Option.getD_none, Function.update_eq_self]
    simp
  | succ j ih =>
    have hj' : j < w.length := by omega
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qr) (bufferTape w)
        (fun _ => none) ((j + 1 : ℕ) - 1)).workTapeSymbols 0 = some w[j] := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj']
    have he : tm.step (enumCont_pairCfg (x := x) (some qr) (bufferTape w)
        (fun _ => none) ((j + 1 : ℕ) - 1)) =
        enumCont_pairCfg (some qr) (bufferTape w) (fun _ => none) (j - 1) := by
      change (tm.tr qr _ _).apply _ = _
      rw [htr, hr, enumCont_ends_apply hL]
      simp only [Option.getD_none, Function.update_eq_self]
      simp [sub_eq_add_neg, add_assoc]
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    exact ih (by omega)

/-- Copying a captured word at least as long as the old candidate completely
replaces it, erases capture, and restores the canonical seam in linear time. -/
private lemma enumCont_copy_complete {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qc qr qa : S) (f : Bool → Bool)
    (hc : ∀ inp work, tm.tr qc inp work = match work (Fin.last L) with
      | some b => enumCont_endsAction (some (some (f b))) (some none) .pos (some qc)
      | none => enumCont_endsAction none none .neg (some qr))
    (hr : ∀ inp work, tm.tr qr inp work = match work 0 with
      | some _ => enumCont_endsAction none none .neg (some qr)
      | none => enumCont_endsAction none none .pos (some qa))
    (old v : List Bool) (hv : old.length ≤ v.length) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qc) (bufferTape old) (bufferTape v) 0)
      (2 * v.length + 2) =
      enumCont_pairCfg (some qa) (bufferTape (v.map f)) (fun _ => none) 0 := by
  have hc' := enumCont_copy_scan (x := x) hL tm qc qr f hc [] old v
  simp only [List.length_nil, List.replicate_zero, List.nil_append, Nat.cast_zero,
    zero_add, enumCont_sparse_some, List.drop_eq_nil_iff.mpr hv, List.append_nil] at hc'
  rw [show 2 * v.length + 2 = (v.length + 1) + (v.length + 1) by omega,
    MultiTapeTM.runFrom_add, hc']
  exact enumCont_pair_rewind hL tm qr qa hr (v.map f) v.length (by simp)

/-- Empty history adds only blank stationary tapes to a candidate seam. -/
private lemma enumCont_log_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s : List Bool) (q : B.State) :
    enumCont_logCfg (Cfg.ofWords (input := x) q (stateWord B.k s)) [] =
      Cfg.ofWords q (stateWord (enumCont_logTM B).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks]
    · have hn : B.k + j.val ≠ 0 := by omega
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks, Nat.ne_of_gt hB]
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
          simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks,
            Fin.addCases, Nat.ne_of_gt hB] <;> exact enumCont_sparse_blanks 0
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logCfg, Cfg.ofWords, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_logCfg, Cfg.ofWords, tapeBlocks]

/-- Appending one output tape to a candidate seam has the two-endpoint tape
layout used by the administrative controller. -/
private lemma enumCont_extend_words {L : ℕ} (hL : 0 < L) (s y : List Bool) :
    (fun i : Fin (L + 1) => if hi : i.val < L then
      bufferTape (stateWord L s ⟨i, hi⟩) else bufferTape y) =
      (fun i => if i.val = 0 then bufferTape s else if i.val = L then bufferTape y
        else fun _ => none) := by
  funext i
  by_cases hz : i.val = 0
  · have he : i = 0 := Fin.ext hz
    subst i
    simp [stateWord, hL]
  · have he : i ≠ 0 := by intro he; apply hz; simp [he]
    by_cases hi : i.val < L
    · have hn : i.val ≠ L := by omega
      simp [stateWord, hi, hz, hn]
    · have hl : i.val = L := by have := i.isLt; omega
      simp [hl, Nat.ne_of_gt hL]

/-- The clean wrapper's entry configuration at a prepared source seam. -/
private lemma enumCont_clean_entry_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s : List Bool) (q : B.State) :
    captureCfg (fun q => (Sum.inl q : (enumCont_cleanTM B).State)) (.inr (.inl 0)) [] []
      (enumCont_logCfg (Cfg.ofWords (input := x) q (stateWord B.k s)) []) =
      enumCont_pairCfg (some (.inl q)) (bufferTape s) (fun _ => none) 0 := by
  rw [enumCont_log_words B hB]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa only [captureCfg, Cfg.ofWords, List.append_nil, bufferTape_nil] using
      enumCont_extend_words (by omega) s []
  · funext i
    simp [captureCfg, Cfg.ofWords, enumCont_pairCfg]

/-- The completed clean call has restored the candidate seam and retained
only its captured output on the last tape. -/
private lemma enumCont_clean_exit_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s y : List Bool) (q : B.State) (q' : Option (enumCont_cleanTM B).State) :
    enumCont_cleanCfg B (Cfg.ofWords (input := x) q (stateWord B.k s)) y q' 1 0 =
      enumCont_pairCfg q' (bufferTape s) (bufferTape y) 0 := by
  unfold enumCont_cleanCfg
  rw [enumCont_log_words B hB]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact enumCont_extend_words (by dsimp [enumCont_logTM]; omega) s y
  · funext i
    simp [Cfg.ofWords, enumCont_pairCfg]

/-- A clean call inside the body redirects the clean wrapper's first halt to
the appropriate live administrative state. This is a complete configuration
equation: all scratch is blank, both endpoint heads are zero, and output is
physically empty. -/
private lemma enumCont_body_call (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi q : B.State) (stop : Bool) (mode : Fin 3) (x s y : List Bool) (T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) q (stateWord B.k s)) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) q (stateWord B.k s)) T).output = y) :
    ∃ t ≤ 3 * T + x.length + y.length + 8,
      (enumCont_bodyTM B qv qi stop).tm.runFrom
        (enumCont_pairCfg (x := x) (some (.inl (.inl q, mode)))
          (bufferTape s) (fun _ => none) 0) t =
        enumCont_pairCfg (some (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4)))
          (bufferTape s) (bufferTape y) 0 := by
  obtain ⟨r, hr, he⟩ := enumCont_clean_complete B
    (Cfg.ofWords (input := x) q (stateWord B.k s)) y T hh ho
  rw [enumCont_clean_entry_words B hB, enumCont_clean_exit_words B hB] at he
  obtain ⟨t, ht, hlive, hend⟩ := enumCont_first_halt (enumCont_cleanTM B).tm _ r
    (by rw [he]; rfl)
  have hrun := enumCont_return_run (enumCont_cleanTM B).tm (enumCont_bodyTM B qv qi stop).tm
    (fun q => .inl (q, mode))
    (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4))
    (fun _ _ _ => rfl) (enumCont_pairCfg (x := x) (some (.inl q))
      (bufferTape s) (fun _ => none) 0) t hlive
  rw [hend, he] at hrun
  exact ⟨t, ht.trans hr, hrun⟩

/-- With empty capture and zero endpoint heads, the administrative tape
layout is exactly the public canonical candidate seam. -/
private lemma enumCont_pair_words {L : ℕ} {S : Type} {x : List Bool}
    (q : S) (s : List Bool) :
    enumCont_pairCfg (L := L) (x := x) (some q) (bufferTape s) (fun _ => none) 0 =
      Cfg.ofWords q (stateWord (L + 1) s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      simp [enumCont_pairCfg, Cfg.ofWords, stateWord, he]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      simp [enumCont_pairCfg, Cfg.ofWords, stateWord, he]
  · funext i; simp [enumCont_pairCfg, Cfg.ofWords]

/-- Initialization runs the clean unary generator, copies its marks as false
candidate bits, erases the marks, and rewinds to the canonical anchor. -/
private lemma enumCont_body_start (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x : List Bool) (w T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).output =
      List.replicate w true) :
    ∃ t ≤ 3 * T + x.length + 3 * w + 10,
      (enumCont_bodyTM B qv qi stop).tm.runFrom ((enumCont_bodyTM B qv qi stop).tm.initCfg x) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k (List.replicate w false)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi B.tm.q₀ stop 0 x []
    (List.replicate w true) T hh ho
  have hi : enumCont_pairCfg (x := x) (some (.inl (.inl B.tm.q₀, (0 : Fin 3))))
      (bufferTape []) (fun _ => none) 0 = (enumCont_bodyTM B qv qi stop).tm.initCfg x := by
    rw [enumCont_pair_words]
    simp [enumCont_bodyTM, enumCont_cleanTM, enumCont_logTM,
      MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord]
  rw [hi] at he
  have hc := enumCont_copy_complete (x := x)
    (show 0 < (enumCont_logTM B).k by dsimp [enumCont_logTM]; omega)
    (enumCont_bodyTM B qv qi stop).tm (.inr 1) (.inr 6) (.inr 0) (fun _ => false)
    (by intro inp work; rfl) (by intro inp work; rfl) [] (List.replicate w true) (by simp)
  simp only [List.length_replicate, List.map_replicate, enumCont_pair_words] at hc
  refine ⟨t + (2 * w + 2), ?_, ?_⟩
  · simp only [List.length_replicate] at ht; omega
  · rw [MultiTapeTM.runFrom_add, he]
    exact hc

/-- A genuine round leaves the anchor in one silent stationary transition. -/
private lemma enumCont_body_depart (B : FinTM Bool) (qv qi : B.State) (x s : List Bool) :
    (enumCont_bodyTM B qv qi false).tm.step
      (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) =
      enumCont_pairCfg (some (.inl (.inl qv, 1))) (bufferTape s) (fun _ => none) 0 := by
  rw [enumCont_pair_words]
  change (controlAction 0 (some (.inl (.inl qv, (1 : Fin 3)) :
    (enumCont_bodyTM B qv qi false).State))).apply _ = _
  rw [controlAction_apply]
  simp [moveInputPos_zero, Cfg.ofWords]
  exact ⟨rfl, rfl⟩

/-- A captured true verdict emits the sole physical accepting bit and halts. -/
private lemma enumCont_body_accept (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s : List Bool) :
    let c := enumCont_pairCfg (x := x) (some (.inr (3 : Fin 7))) (bufferTape s)
      (bufferTape [true]) 0
    ((enumCont_bodyTM B qv qi stop).tm.step c).state = none ∧
      ((enumCont_bodyTM B qv qi stop).tm.step c).output = [true] := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  simp [MultiTapeTM.step, enumCont_bodyTM, enumCont_pairCfg, Cfg.workTapeSymbols,
    hL, Action.apply, bufferTape]

/-- A false verdict is erased before entering the clean increment call. -/
private lemma enumCont_body_reject (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s : List Bool) :
    (enumCont_bodyTM B qv qi stop).tm.step
      (enumCont_pairCfg (x := x) (some (.inr 3)) (bufferTape s) (bufferTape [false]) 0) =
      enumCont_pairCfg (some (.inl (.inl qi, 2))) (bufferTape s) (fun _ => none) 0 := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  have hv : Function.update (bufferTape [false]) (0 : ℤ) none = fun _ => none := by
    rw [show [false] = [] ++ [false] by rfl, bufferTape_append]
    simp only [List.length_nil, Nat.cast_zero, Function.update_idem]
    simp [Function.update_eq_self]
  have hr : (enumCont_pairCfg (L := (enumCont_logTM B).k) (x := x)
      (some (.inr (3 : Fin 7)) : Option (enumCont_bodyTM B qv qi stop).State)
      (bufferTape s) (bufferTape [false]) 0).workTapeSymbols (Fin.last (enumCont_logTM B).k) =
      some false := by simp [enumCont_pairCfg, Cfg.workTapeSymbols, hL, bufferTape]
  change ((enumCont_bodyTM B qv qi stop).tm.tr (.inr 3) _ _).apply _ = _
  simp only [enumCont_bodyTM, hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      simp [enumCont_pairCfg, Action.apply, Ne.symm hL]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = (enumCont_logTM B).k <;>
        simp [enumCont_pairCfg, Action.apply, he, hl, hv]
  · funext i
    simp [enumCont_pairCfg, Action.apply]

/-- The catalog's empty overflow output preserves the old candidate. Every
nonempty increment result has the exact old width and is the stalled step. -/
private lemma enumCont_increment_cases (s : List Bool) :
    let v := (incFixed s).getD []
    (v = [] ∧ (incFixed s).getD s = s) ∨
      (v ≠ [] ∧ v.length = s.length ∧ (incFixed s).getD s = v) := by
  have hlen := enumCont_step_length s
  cases hi : incFixed s with
  | none => simp
  | some v =>
    rw [hi] at hlen
    simp only [Option.getD_some] at hlen ⊢
    by_cases hv : v = []
    · subst v
      have hs : s = [] := List.length_eq_zero_iff.mp hlen.symm
      simp [hs]
    · exact Or.inr ⟨hv, hlen, trivial⟩

/-- The increment-result check preserves all fields and chooses the anchor
on overflow or the copy phase on a nonempty result. -/
private lemma enumCont_body_check (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s v : List Bool) :
    (enumCont_bodyTM B qv qi stop).tm.step
      (enumCont_pairCfg (x := x) (some (.inr 4)) (bufferTape s) (bufferTape v) 0) =
      enumCont_pairCfg (some (.inr (if v = [] then 0 else 5)))
        (bufferTape s) (bufferTape v) 0 := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  have hv : bufferTape v 0 = none ↔ v = [] := by cases v <;> simp [bufferTape]
  change ((enumCont_bodyTM B qv qi stop).tm.tr (.inr 4) _ _).apply _ = _
  simp only [enumCont_bodyTM]
  have hr : (enumCont_pairCfg (L := (enumCont_logTM B).k) (x := x)
      (some (.inr (4 : Fin 7)) : Option (enumCont_bodyTM B qv qi stop).State)
      (bufferTape s) (bufferTape v) 0).workTapeSymbols (Fin.last (enumCont_logTM B).k) =
      bufferTape v 0 := by simp [enumCont_pairCfg, Cfg.workTapeSymbols, hL]
  rw [hr]
  simp only [hv]
  by_cases he : v = [] <;> simp only [he, ↓reduceIte, controlAction_apply]
  all_goals
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    simp [enumCont_pairCfg]

/-- A clean increment call followed by copy and rewind implements the exact
stalled fixed-width step. Empty overflow results preserve the candidate;
successful results replace every candidate cell in place. -/
private lemma enumCont_body_increment (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x s : List Bool) (T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) T).output =
      (incFixed s).getD []) :
    ∃ t ≤ 3 * T + x.length + 3 * s.length + 11,
      (enumCont_bodyTM B qv qi stop).tm.runFrom
        (enumCont_pairCfg (x := x) (some (.inl (.inl qi, 2)))
          (bufferTape s) (fun _ => none) 0) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k ((incFixed s).getD s)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi qi stop 2 x s ((incFixed s).getD []) T hh ho
  simp only [show (2 : Fin 3).val = 2 by decide, show ¬(2 : ℕ) = 0 by decide,
    show ¬(2 : ℕ) = 1 by decide, ↓reduceIte] at he
  rcases enumCont_increment_cases s with ⟨hv, hs⟩ | ⟨hv, hl, hs⟩
  · refine ⟨t + 1, ?_, ?_⟩
    · rw [hv] at ht; simp only [List.length_nil] at ht; omega
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, enumCont_body_check, if_pos hv, hv,
        hs, bufferTape_nil, enumCont_pair_words]
      rfl
  · have hc := enumCont_copy_complete (x := x)
      (show 0 < (enumCont_logTM B).k by dsimp [enumCont_logTM]; omega)
      (enumCont_bodyTM B qv qi stop).tm (.inr 5) (.inr 6) (.inr 0) id
      (by intro inp work; rfl) (by intro inp work; rfl) s ((incFixed s).getD []) (by omega)
    simp only [List.map_id, enumCont_pair_words] at hc
    refine ⟨(t + 1) + (2 * ((incFixed s).getD []).length + 2), ?_, ?_⟩
    · rw [hl] at ht ⊢; omega
    · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step' (t := t), he,
        enumCont_body_check, if_neg hv, hc, hs]
      rfl

/-- Starting just after departure, one verifier call either emits acceptance
or clears the verdict and completes one exact candidate update. This raw
segment is valid in both controller variants; first-return guards are added
separately using the stopped anchor. -/
private lemma enumCont_body_round_raw (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x s : List Bool) (b : Bool) (Tv Ti : ℕ)
    (hv : (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).output = [b])
    (hi : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).output =
        (incFixed s).getD []) :
    ∃ t ≤ 3 * Tv + 3 * Ti + 2 * x.length + 3 * s.length + 21,
      if b then
        ((enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t).state = none ∧
        ((enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t).output = [true]
      else (enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k ((incFixed s).getD s)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi qv stop 1 x s [b] Tv hv.1 hv.2
  simp only [show (1 : Fin 3).val = 1 by decide, show ¬(1 : ℕ) = 0 by decide,
    ↓reduceIte] at he
  simp only [List.length_singleton] at ht
  cases b with
  | false =>
    obtain ⟨r, hr, hrun⟩ := enumCont_body_increment B hB qv qi stop x s Ti hi.1 hi.2
    refine ⟨(t + 1) + r, by omega, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step', he,
      enumCont_body_reject, hrun]
  | true =>
    refine ⟨t + 1, by omega, ?_⟩
    simp only [↓reduceIte, MultiTapeTM.runFrom_succ_eq_step', he]
    exact enumCont_body_accept B qv qi stop x s

/-- An anchor whose transition is a stationary self-loop preserves its
complete configuration for every subsequent step. -/
private lemma enumCont_absorb {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ inp work, tm.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (hc : c.state = some qa) (t : ℕ) : tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    simp only [MultiTapeTM.step, hc, ha, controlAction_apply]
    apply Cfg.ext
    · exact hc.symm
    · exact moveInputPos_zero _
    · rfl
    · rfl
    · rfl

/-- Two transition tables differing only at the anchor agree on every run
prefix that has not yet visited that anchor. -/
private lemma enumCont_agree_run {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (c : Cfg k Bool S x) (t : ℕ)
    (hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa) :
    tm.runFrom c t = stop.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hn j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (stop.runFrom c t).state with
    | none => simp only [MultiTapeTM.step, hs]
    | some q =>
      have hq : q ≠ qa := by intro he; subst q; exact hn t (by omega) hs
      simp only [MultiTapeTM.step, hs, ha q hq]

/-- The first visit to a stopped anchor transfers to the active machine with
the same full endpoint and no earlier anchor visit. Absorption identifies
the first endpoint with the supplied bounded endpoint. -/
private lemma enumCont_first_anchor {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (hs : ∀ inp work, stop.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (T : ℕ) (hT : (stop.runFrom c T).state = some qa) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some qa) ∧
      tm.runFrom c t = stop.runFrom c T := by
  classical
  have hex : ∃ t, (stop.runFrom c t).state = some qa := ⟨T, hT⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hT
  have hend : (stop.runFrom c t).state = some qa := Nat.find_spec hex
  have hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa := fun j hj => Nat.find_min hex hj
  have he : stop.runFrom c T = stop.runFrom c t := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
    rw [hr, MultiTapeTM.runFrom_add, enumCont_absorb stop qa hs _ hend]
  refine ⟨t, ht, ?_, ?_⟩
  · intro j hj
    rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
    exact hn j hj
  · rw [enumCont_agree_run tm stop qa ha c t hn, he]

/-- A halted stopped run never visited the live absorbing anchor. Its entire
bounded run therefore transfers unchanged to the active machine. -/
private lemma enumCont_halt_transfer {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (hs : ∀ inp work, stop.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (T : ℕ) (hT : (stop.runFrom c T).state = none) :
    tm.runFrom c T = stop.runFrom c T ∧
      ∀ j ≤ T, (tm.runFrom c j).state ≠ some qa := by
  have hn : ∀ j ≤ T, (stop.runFrom c j).state ≠ some qa := by
    intro j hj hjq
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hj
    have he : stop.runFrom c T = stop.runFrom c j := by
      rw [hr, MultiTapeTM.runFrom_add, enumCont_absorb stop qa hs _ hjq]
    have he' := congrArg Cfg.state he
    rw [hT, hjq] at he'
    contradiction
  refine ⟨enumCont_agree_run tm stop qa ha c T (fun j hj => hn j (by omega)), ?_⟩
  intro j hj
  rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
  exact hn j hj

/-- The active and stopped body have identical transitions away from the
anchor. Their tape counts and finite state types are definitionally equal. -/
private lemma enumCont_body_agree (B : FinTM Bool) (qv qi : B.State)
    (q : (enumCont_bodyTM B qv qi false).State) (hq : q ≠ .inr 0) (inp work) :
    (enumCont_bodyTM B qv qi false).tm.tr q inp work =
      (enumCont_bodyTM B qv qi true).tm.tr q inp work := by
  cases q with
  | inl q => rfl
  | inr q =>
    have hz : q.val ≠ 0 := by
      intro he
      apply hq
      congr 1
      exact Fin.ext he
    simp only [enumCont_bodyTM]
    split <;> first | contradiction | rfl

/-- Startup satisfies the loop export's first-anchor guard as well as its
full canonical configuration equality. -/
private lemma enumCont_body_start_guarded (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (x : List Bool) (w T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).output =
      List.replicate w true) :
    ∃ t ≤ 3 * T + x.length + 3 * w + 10,
      (∀ j < t, ((enumCont_bodyTM B qv qi false).tm.runFrom
        ((enumCont_bodyTM B qv qi false).tm.initCfg x) j).state ≠ some (.inr 0)) ∧
      (enumCont_bodyTM B qv qi false).tm.runFrom ((enumCont_bodyTM B qv qi false).tm.initCfg x) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k (List.replicate w false)) := by
  obtain ⟨r, hr, he⟩ := enumCont_body_start B hB qv qi true x w T hh ho
  change (enumCont_bodyTM B qv qi true).tm.runFrom
    ((enumCont_bodyTM B qv qi false).tm.initCfg x) r =
      Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k (List.replicate w false)) at he
  obtain ⟨t, ht, hn, hend⟩ := enumCont_first_anchor
    (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
    (enumCont_body_agree B qv qi) (by intro inp work; rfl)
    ((enumCont_bodyTM B qv qi false).tm.initCfg x) r (by rw [he]; rfl)
  rw [he] at hend
  exact ⟨t, ht.trans hr, hn, hend⟩

/-- The active round has positive duration and no strict interior visit to
the anchor. Rejection uses the first stopped-anchor visit; acceptance never
visits that live absorbing state. In either case departure adds one step. -/
private lemma enumCont_body_round_guarded (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (x s : List Bool) (b : Bool) (Tv Ti : ℕ)
    (hv : (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).output = [b])
    (hi : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).output =
        (incFixed s).getD []) :
    ∃ t, 0 < t ∧ t ≤ 3 * Tv + 3 * Ti + 2 * x.length + 3 * s.length + 22 ∧
      (∀ j, 0 < j → j < t →
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) j).state
            ≠ some (.inr 0)) ∧
      if b then
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t).state
            = none ∧
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t).output
            = [true]
      else (enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k ((incFixed s).getD s)) := by
  obtain ⟨r, hr, he⟩ := enumCont_body_round_raw B hB qv qi true x s b Tv Ti hv hi
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    obtain ⟨t, ht, hn, hend⟩ := enumCont_first_anchor
      (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
      (enumCont_body_agree B qv qi) (by intro inp work; rfl)
      (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
        (bufferTape s) (fun _ => none) 0) r (by rw [he]; rfl)
    refine ⟨t + 1, by omega, by omega, ?_, ?_⟩
    · intro j hj hjt
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart]
      exact hn i (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart, hend, he]
      rfl
  | true =>
    simp only [↓reduceIte] at he ⊢
    obtain ⟨hend, hn⟩ := enumCont_halt_transfer
      (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
      (enumCont_body_agree B qv qi) (by intro inp work; rfl)
      (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
        (bufferTape s) (fun _ => none) 0) r he.1
    refine ⟨r + 1, by omega, by omega, ?_, ?_⟩
    · intro j hj hjr
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart]
      exact hn i (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart, hend]
      exact he

/-- A prepared source call may use the initial tape block of the shared
source machine; padding preserves its halt and exact emitted word. -/
private lemma enumCont_lift_call (M B : FinTM Bool) (hM : 0 < M.k) (hk : M.k ≤ B.k)
    (emb : M.State → B.State)
    (htr : ∀ q inp work, B.tm.tr (emb q) inp work =
      enumCont_padAction emb (M.tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (q : M.State) (x s y : List Bool) (T : ℕ)
    (hh : (M.tm.runFrom (Cfg.ofWords (input := x) q (stateWord M.k s)) T).state = none)
    (ho : (M.tm.runFrom (Cfg.ofWords (input := x) q (stateWord M.k s)) T).output = y) :
    (B.tm.runFrom (Cfg.ofWords (input := x) (emb q) (stateWord B.k s)) T).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) (emb q) (stateWord B.k s)) T).output = y := by
  rw [← enumCont_pad_words hM hk emb q x s,
    enumCont_pad_run hk M.tm B.tm emb htr]
  exact ⟨by simp [enumCont_padCfg, hh], ho⟩

/-- Initial calls pad correctly even for a zero-work-tape source. -/
private lemma enumCont_lift_init (M B : FinTM Bool) (hk : M.k ≤ B.k)
    (emb : M.State → B.State)
    (htr : ∀ q inp work, B.tm.tr (emb q) inp work =
      enumCont_padAction emb (M.tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (x y : List Bool) (T : ℕ) (h : M.ComputesInTime x y T) :
    (B.tm.runFrom (Cfg.ofWords (input := x) (emb M.tm.q₀) (stateWord B.k [])) T).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) (emb M.tm.q₀) (stateWord B.k [])) T).output = y := by
  obtain ⟨hh, ho⟩ := (computesInTime_iff M x y T).mp h
  rw [← enumCont_pad_init (k := M.k) emb M.tm.q₀ x]
  change (B.tm.runFrom (enumCont_padCfg emb (M.tm.initCfg x)) T).state = none ∧
    (B.tm.runFrom (enumCont_padCfg emb (M.tm.initCfg x)) T).output = y
  rw [enumCont_pad_run hk M.tm B.tm emb htr]
  refine ⟨?_, ho⟩
  change ((M.tm.runFrom (M.tm.initCfg x) T).state.map emb) = none
  rw [hh]
  rfl

/-- One input-independent polynomial bounds both body phases. The degree
dominates the verifier degree, unary-generator degree, and linear scans;
the coefficient absorbs every fixed administrative transition. -/
private lemma enumCont_common_bound (a d f c j n w : ℕ) :
    let P := (n + w + 1) ^ (d + c + 2)
    let A := 3 * a + 3 * f + 3 * j + 60
    3 * (f * (n + 1) ^ (c + 1)) + n + 3 * w + 10 ≤ A * P ∧
      3 * (a * (n + w + 1) ^ d + 2 * (n + w) + 4) +
        3 * ((j + 3) * (w + 1)) + 2 * n + 3 * w + 22 ≤ A * P := by
  dsimp only
  let P := (n + w + 1) ^ (d + c + 2)
  have hn : n + w + 1 ≤ P := by
    calc n + w + 1 = (n + w + 1) ^ 1 := by simp
      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hd : (n + w + 1) ^ d ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hf : (n + 1) ^ (c + 1) ≤ P :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have ha' := Nat.mul_le_mul_left a hd
  have hf' := Nat.mul_le_mul_left f hf
  have hj' := Nat.mul_le_mul_left (j + 3) (show w + 1 ≤ P by omega)
  change _ ≤ (3 * a + 3 * f + 3 * j + 60) * P ∧
    _ ≤ (3 * a + 3 * f + 3 * j + 60) * P
  simp only [Nat.add_mul, Nat.mul_assoc] at hj' ⊢
  omega

/-- A concrete body with polynomial startup and exact seam restoration gives
the frozen enumerator configuration contract by the audited loop export.
This lemma is conditional only on the two explicit body obligations below.
**Proof sketch.** Use the catalog unary generator for the fuel bits, enlarging
the common coefficient and degree to cover both fuel and body. Instantiate
`exists_loopCfgTM` with the exact-width invariant and stalled increment.
The terminal is `(2^w-1)+1=2^w`; on candidate indices use `enumCont_orbit`.
Finally absorb the export's additive one using `1 ≤ (n+w+1)^D`, exactly as
in infrastructure round 3, item 5. All constants are fixed before the input. -/
private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
    (body : FinTM Bool) (anchor : body.State)
    (hstart : ∀ x : List Bool,
      ∃ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D,
        (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
        body.tm.runFrom (body.tm.initCfg x) t =
          Cfg.ofWords anchor (stateWord body.k (List.replicate (C * (x.length + 1) ^ c) false)))
    (hround : ∀ (x s : List Bool), s.length = C * (x.length + 1) ^ c →
      ∃ t, 0 < t ∧ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if MultiTapeTM.indicator V (x ++ s) then
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = [true]
        else
          body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k ((incFixed s).getD s))) :
    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  obtain ⟨F, f, hF⟩ := computesFunInTime_polyUnary C c
  let T := fun n => (A + f) * (n + C * (n + 1) ^ c + 1) ^ (D + c + 1)
  have hbody (n : ℕ) : A * (n + C * (n + 1) ^ c + 1) ^ D ≤ T n := by
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hfuel : F.ComputesFunInTime
      (fun x => Nat.bits (2 ^ (C * (x.length + 1) ^ c) - 1)) T := by
    intro x
    dsimp only
    rw [enumCont_fuel_bits]
    apply (hF x).mono
    exact Nat.mul_le_mul (by omega)
      ((Nat.pow_le_pow_left (by omega : x.length + 1 ≤
        x.length + C * (x.length + 1) ^ c + 1) (c + 1)).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
  obtain ⟨E, K, hE⟩ := exists_loopCfgTM body F anchor
    (fun x s => s.length = C * (x.length + 1) ^ c)
    (fun _ s => (incFixed s).getD s)
    (fun x s => MultiTapeTM.indicator V (x ++ s))
    (fun x => List.replicate (C * (x.length + 1) ^ c) false)
    (fun n => 2 ^ (C * (n + 1) ^ c) - 1) T hfuel
    (by intro x; exact List.length_replicate)
    (by intro x s hs; exact (enumCont_step_length s).trans hs)
    (by
      intro x
      obtain ⟨t, ht, hi, hh⟩ := hstart x
      exact ⟨t, ht.trans (hbody x.length), hi, hh⟩)
    (by
      intro x s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround x s hs
      exact ⟨t, htpos, ht.trans (hbody x.length), hi, hh⟩)
  refine ⟨K * (A + f + 1), D + c + 1, E, fun x => ?_⟩
  obtain ⟨cfg, startup, ht, hi, _, hend, hout, hr⟩ := hE x
  have hone : 1 ≤ 2 ^ (C * (x.length + 1) ^ c) := Nat.one_le_two_pow
  have hterminal : 2 ^ (C * (x.length + 1) ^ c) - 1 + 1 =
      2 ^ (C * (x.length + 1) ^ c) := Nat.sub_add_cancel hone
  rw [hterminal] at hend hout
  have hbudget : K * (T x.length + 1) ≤ K * (A + f + 1) *
      (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) := by
    have hp : 1 ≤ (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) :=
      Nat.one_le_pow _ _ (by omega)
    calc K * (T x.length + 1) ≤ K * (T x.length +
        (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1)) :=
          Nat.mul_le_mul_left K (Nat.add_le_add_left hp _)
      _ = _ := by dsimp [T]; ring
  refine ⟨cfg, startup, ht.trans hbudget, hi, hend, hout, ?_⟩
  intro i hi
  obtain ⟨t, ht, hh⟩ := hr i (by omega)
  rw [enumCont_orbit _ i hi] at hh
  exact ⟨t, ht.trans hbudget, hh⟩

/-- **Continuation frontier; admitted in this partial delivery.** There is one
uniform finite machine with a polynomial startup and a polynomially bounded
accept-or-advance segment for each exact-width candidate. The configuration
after the last rejected candidate is a halted singleton rejection.

**Proof sketch / remaining construction.** Evaluate `C(n+1)^c` and construct
the all-false candidate while retaining the instance; assemble `x ++ u` on
the virtual input buffer. Use `enumCapture_returns` for the captured call.
On rejection, clear the bounded visited work region, reset all source and
buffer heads and the captured bit, and use `enumCarry_correct` to increment.
Its `enumBump_inc`/`enumInc_word` specification supplies the next rank or the
overflow signal. Emit the single final answer only on acceptance or overflow.
Prove the startup and per-round configuration equalities below with a uniform
polynomial budget. These machine assembly and reset obligations are NOT
discharged by the counter, capture, and abstract loop lemmas alone. -/
private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  obtain ⟨U, f, hU⟩ := computesFunInTime_polyUnary C c
  obtain ⟨I, j, hI⟩ := computesFunInTime_incFixed
  let Q := bufferedCompTM enumCont_concatTM MV
  let R := bufferedCompTM enumCont_concatTM I
  let B := enumCont_sources Q R U
  let qv : B.State := .inl Q.tm.q₀
  let qi : B.State := .inr (.inl (.inl (some true)))
  have hQ : 0 < Q.k := by dsimp [Q, bufferedCompTM, enumCont_concatTM]; omega
  have hR : 0 < R.k := by dsimp [R, bufferedCompTM, enumCont_concatTM]; omega
  have hQB : Q.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hRB : R.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hUB : U.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hB : 0 < B.k := lt_of_lt_of_le hQ hQB
  apply enumCont_from_body C c (3 * a + 3 * f + 3 * j + 60) (d + c + 2) V
    (enumCont_bodyTM B qv qi false) (.inr 0)
  · intro x
    have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
      (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
      (f * (x.length + 1) ^ (c + 1)) (hU x)
    obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
      (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
    exact ⟨t, ht.trans (enumCont_common_bound a d f c j x.length
      (C * (x.length + 1) ^ c)).1, hn, he⟩
  · intro x s hs
    obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V a d hV x s
    obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
    have hv := enumCont_lift_call Q B hQ hQB Sum.inl
      (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
    have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
      (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
    obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
      (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
    refine ⟨t, htpos, ?_, hn, he⟩
    have hb := (enumCont_common_bound a d f c j x.length s.length).2
    rw [hs] at hb
    apply le_trans (show t ≤ 3 * (a * (x.length + s.length + 1) ^ d +
      2 * (x.length + s.length) + 4) + 3 * ((j + 3) * (s.length + 1)) +
      2 * x.length + 3 * s.length + 22 by omega)
    simpa only [hs] using hb

/-! **Continuation completion note (batch E2-cont A).** The historical
partial-fill descriptions above and below are retained under the statement
freeze. The former `enumMachine_contracts` admission is now discharged.
The new private body has proved initialization, exact buffered verifier
input, captured silent output, complete reversible scratch restoration,
in-place candidate replacement, and positive first-return round contracts.
`enumCont_from_body` supplies the audited exact-width loop instantiation,
catalog-generated `2^w-1` fuel, bounded rank orbit, terminal `2^w`, and
uniform startup/round budgets. -/

/-- Assuming the single machine-construction frontier, the proved loop
invariant gives a decider with the audited exponential-times-polynomial
budget. This lemma inherits exactly that pending admission.
**Proof sketch.** Start the loop after initialization, apply `enumLoop_run`
for all `2^width` candidates, and identify its Boolean answer using exact
candidate coverage. Since `2^width ≥ 1`, startup is absorbed by doubling the
coefficient. The final computation has exactly one output bit. -/
private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool),
      E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
        (fun n => b * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ e) := by
  classical
  obtain ⟨b, e, E, hE⟩ := enumMachine_contracts C c a d V MV hV
  refine ⟨2 * b, e, E, fun x => ?_⟩
  obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
  let w := C * (x.length + 1) ^ c
  let B := b * (x.length + w + 1) ^ e
  let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
  obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
    (by simpa only [Nat.zero_add] using And.intro hend hout)
    (fun j _ hj => hround j (by simpa only [Nat.zero_add] using hj))
  have hb : enumAny accept 0 (2 ^ w) =
      MultiTapeTM.indicator
        {z | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} x := by
    have ha := enumAny_certificates x w V
    change enumAny accept 0 (2 ^ w) = true ↔ _ at ha
    cases he : enumAny accept 0 (2 ^ w) with
    | false =>
      have hx : ¬∃ u, u.length = w ∧ x ++ u ∈ V := by
        intro hx
        have := ha.mpr hx
        rw [he] at this
        contradiction
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
    | true =>
      have hx := ha.mp he
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
  have hcomp : E.ComputesInTime x [enumAny accept 0 (2 ^ w)] (startup + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hinit]
    exact ⟨hh, ho⟩
  rw [hb] at hcomp
  apply hcomp.mono
  have hB : B ≤ 2 ^ w * B := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
       _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
       _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
           (x.length + C * (x.length + 1) ^ c + 1) ^ e := by dsimp [B, w]; ring

/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
machine — a **new obligation**; the explicit formula is what makes the width
computable at all, phase-1 audit finding 1 and question 4) and lay out a
width-`Q n` all-`false` candidate certificate; in each round, assemble
`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
candidate as a **fixed-width** counter and repeat, rejecting on width overflow
after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
definition's length — no majorant mismatch (audit question 4). The remaining
machine obligations, named for the fill per phase-1 finding 5 and round-2
finding 2: fixed-width increment with overflow detection (the private
`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
is a template, not a citable API — promotion or private re-derivation is a
fill-time decision); retention of `x` and the candidate across rounds;
**a verifier-call simulation that captures `MV`'s decision bit in finite
control, suppresses its physical emissions, and redirects its halt to the
loop controller** — the output tape is append-only, so forwarding per-round
emissions would accumulate (`[false, true]` across two rounds) and violate
`DecidesInTime`'s singleton contract; the real output stays empty until the
final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
and the captured bit between rounds (a bounded region — each head moves at
most one cell per step); and a timed loop invariant covering all of the above
(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
`L ∈ EXP`.
+
+**Partial-fill appendix.** The fixed-width carry, buffered captured-call
+simulation, abstract timed-loop invariant, and final budget normalization
+are proved below the class definitions. The machine's initialization,
+reset, and controller assembly remain the single private admission
+`enumMachine_contracts`; the present theorem still depends on `sorryAx`. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  rintro L ⟨C, c, V, hV, hL⟩
  obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
  obtain ⟨b, e, E, hE⟩ := enumDecider C c a d V MV hMV
  obtain ⟨A, f, hbound⟩ := enumBudget_bound b C c e
  have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
    Set.ext (fun x => (hL x).symm)
  rw [heq] at hE
  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x => (hE x).mono (hbound x.length)⟩

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take `C = 1` and
certificate length `p n = 2^((n+1)^c)` — nondecreasing in `n` (constant `2` at
`c = 0`), so that `n ↦ n + p n` is **strictly increasing** (the monotonicity
belongs to the sum, not to `p` — phase-1 audit, finding 8) — and the verifier
`V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y` of length `m`,
recover the unique `n` with `n + p n = m` by scanning `n ≤ m` (each evaluation
writes `2^((n+1)^c)` in binary, `(n+1)^c + 1 ≤ (m+1)^c + 1` bits — polynomial
in `m`, the audit's own check), reject if no split exists (including `m = 0`),
split off `x`, and run `L`'s decider: its `a · 2^(n^c)` budget is at most
`a · m`. Fixed-degree arithmetic and the split/copy machinery are named new
machine obligations for the fill. Certificates carry no information; padding
buys the verifier its time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  sorry

end Complexity
