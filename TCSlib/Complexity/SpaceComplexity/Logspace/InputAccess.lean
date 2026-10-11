/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random access to a general input in logarithmic space

A logspace machine reads its input at a position held in binary on a work tape [AB09, §4.1:
"a pointer into the input"]. The received `LogProg` layer has no such access for a general
(non-unary) input: the input instructions of `Complexity.LogProg.ARM` presuppose inputs
`⟨1ⁿ, w⟩` or `⟨1ⁿ, ⟨u, w⟩⟩`, and a call's virtual input is the whole input or its leading run
of `1`s followed by register words (P0 reception audit, `audits/ch34-p0-findings.md`). This
file supplies the missing piece twice, at the two levels later logspace programs use:

* **as a program fragment**: `Complexity.LogProg.readIn_run` reads bit `i` of the input,
  `i` held in binary on a register, into the control state (a counter register stepped up to
  `i` in lockstep with the input head, the received equality, increment, rewind and clear
  fragments), and restores everything else;
* **as a language pair**: `Complexity.implicitlyLogspaceComputable_id` — the bit and length
  languages of the identity, `Complexity.inputBitLang` and `Complexity.inputLenLang`, are in
  `L` — so an abstract register machine reads its own input at a register-held position by a
  `whole`-mode call with that register as its one argument (`Complexity.LogProg.vword_whole₁`,
  `Complexity.indicator_indexLang_pairEncode`).

Phase P4.4b of `AroraBarakChapters3-4Plan.md` (the B7 statement mini-phase, recorded in
`audits/ch4-p44-resolutions-addendum.md`). The fragment is campaign-owned and lives here,
not in `Machines/`, by decision D3; it is built only from received fragments.

## Main definitions

* `Complexity.LogProg.RdPh`, `Complexity.LogProg.readTr` — the phases and the transition
  table of the input-read fragment.
* `Complexity.inputBitLang`, `Complexity.inputLenLang` — `{⟨u, i⟩ | uᵢ = 1}` and
  `{⟨u, i⟩ | i < |u|}`.

## Main results

* `Complexity.LogProg.vword_whole₁` — a `whole` call with one argument presents `⟨u, V r⟩`.
* `Complexity.indicator_indexLang_pairEncode` — the answer of an `indexLang` decider on a
  genuine pair.
* `Complexity.pairEncode_ne_nil` — no pair is empty (so `[]` lies in no `indexLang`).
* `Complexity.LogProg.readIn_run` — the input-read fragment (proved; phase-P4.4b
  statement).
* `Complexity.implicitlyLogspaceComputable_id` — input random access in `L` (sorried;
  phase-P4.4b statement), with `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; §4.3, Definition 4.16.)
-/

namespace Complexity

open Turing

/-- No pair encoding is the empty word: `pairEncode x y` contains the separator. -/
theorem pairEncode_ne_nil (x y : List Bool) : pairEncode x y ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [length_pairEncode] at this

/-- **The answer of an index-language decider on a genuine pair**: the indicator of
`indexLang p` at `⟨u, bits v⟩` is the decision of `p u v`. -/
theorem indicator_indexLang_pairEncode (p : List Bool → ℕ → Prop) (u : List Bool) (v : ℕ) :
    MultiTapeTM.indicator (indexLang p : Set (List Bool)) (pairEncode u (Nat.bits v)) =
      @decide (p u v) (Classical.dec _) := by
  rw [LogProg.indicator_eq_decide]
  exact decide_eq_decide.mpr (pairEncode_mem_indexLang p u v)

namespace LogProg

/-- **A `whole`-mode call with one argument** presents the pair of the whole input and the
argument register's word: its virtual input is `⟨u, V r⟩`. -/
theorem vword_whole₁ {m d : ℕ} {Λ : Type} (u : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .whole, [r], l₁, l₀⟩ u V) = pairEncode u (V r) := by
  simp [callSegs, Mode.seg0, argSegs, vword, render, pairEncode_eq_dbl]

/-! ## The input-read fragment -/

/-- The phases of the input-read fragment: the equality test of the counter with the index
(`eC`, `eBy`, `eBn`), the read (`yes`) or advance (`no`) step, the counter increment (`iC`,
`iB`), and, carrying the symbol read, the input rewind (`rw₁`, `rw₂`) and the counter clear
(`cR`, `cE`). -/
inductive RdPh where
  | eC | eBy | eBn
  | yes | no
  | iC | iB
  | rw₁ (a : Option Bool) | rw₂ (a : Option Bool)
  | cR (a : Option Bool) | cE (a : Option Bool)
  deriving DecidableEq, Fintype

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- **The transition table of the input-read fragment** on index register `r` and counter
register `s`, its phases embedded by `st` and its exits by `ex`. With the input head on
position `k + 1` (input symbol `k`) and the counter holding `bits k`: compare the counter with
the index (`eq_run`); if equal, take the symbol under the head; if not, stop at the right
blank, or else step the input head right and increment the counter (`inc_run`). Then rewind
the input head to position `1` (`rewind_x`) and clear the counter (`clr_run`), exiting into
`ex a` with the symbol `a` taken. -/
def readTr (r s : Fin m) (st : RdPh → Λ) (ex : Option Bool → Λ) :
    RdPh → Option Bool → (Fin m → Option Bool) → Action m Bool Λ
  | .eC, _, w => eqCAct s r (st .eC) (st .eBy) (st .eBn) (w s) (w r)
  | .eBy, _, w => eqBAct s r (st .eBy) (st .yes) (w s)
  | .eBn, _, w => eqBAct s r (st .eBn) (st .no) (w s)
  | .yes, a, _ => goAct (st (.rw₁ a))
  | .no, a, _ =>
    match a with
    | none => goAct (st (.rw₁ none))
    | some _ => xAct s 1 0 (st .iC)
  | .iC, _, w => incCAct s (st .iC) (st .iB) (w s)
  | .iB, _, w => incBAct s (st .iB) (st .eC) (w s)
  | .rw₁ a, _, _ => xAct s (-1) 0 (st (.rw₂ a))
  | .rw₂ a, b, _ => rw2Act s (st (.rw₂ a)) (st (.cR a)) b
  | .cR a, _, w => toEndAct s (st (.cR a)) (st (.cE a)) (w s)
  | .cE a, _, w => clrEAct s (st (.cE a)) (ex a) (w s)

/-- A proof-only instance of the frozen read table, with disjoint phase and exit labels.
Exits halt, which lets the received fragments' non-call trace clauses recover phase
membership before the final exit. The eventual transport does not require `st` injective. -/
private def readModel (r s : Fin m) : RProg m 0 (RdPh ⊕ Option Bool) :=
  ⟨⟨.inl .eC, fun l a w => match l with
    | .inl ph => readTr r s Sum.inl Sum.inr ph a w
    | .inr _ => junkAct⟩, fun _ => none⟩

/-- A read-fragment boundary with its input position and canonical counter explicit. -/
private def readAt (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (s : Fin m)
    (l : RdPh ⊕ Option Bool) (ip : Fin (x.length + 2)) (k : ℕ) :
    Cfg m Bool (RdPh ⊕ Option Bool) x :=
  ⟨some l, ip, Function.update c.workTapes s (FinTM.bufferTape (Nat.bits k)),
    Function.update c.workTapePos s 0, c.output⟩

/-- The frame and head-range assertion, before restricting the control label to a phase. -/
private def readFrame (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (d : Cfg m Bool (RdPh ⊕ Option Bool) x) : Prop :=
  ∃ l ip f p q, d = ⟨some l, ip, Function.update c.workTapes s f,
      Function.update (Function.update c.workTapePos s p) r q, c.output⟩ ∧
    -1 ≤ p ∧ p ≤ (Nat.bits (x.length + 1)).length ∧
    -1 ≤ q ∧ q ≤ (Nat.bits (x.length + 1)).length

/-- A counter-only fragment view satisfies the frame. -/
private theorem readFrame_reg (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (hrp : c.workTapePos r = 0) (l l' : RdPh ⊕ Option Bool)
    (ip : Fin (x.length + 2)) (k : ℕ) (f : ℤ → Option Bool) (p : ℤ)
    (hp : -1 ≤ p) (hp' : p ≤ (Nat.bits (x.length + 1)).length) :
    readFrame c r s (regCfg (readAt c s l ip k) l' s f p) := by
  refine ⟨l', ip, f, p, 0, ?_, hp, hp', by omega, by omega⟩
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simp [regCfg, readAt]
  · simp [regCfg, readAt, Function.update_of_ne hrs, hrp]

/-- A boundary configuration is framed with both active heads at the origin. -/
private theorem readFrame_at (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (hrp : c.workTapePos r = 0) (l : RdPh ⊕ Option Bool)
    (ip : Fin (x.length + 2)) (k : ℕ) : readFrame c r s (readAt c s l ip k) := by
  have he : regCfg (readAt c s l ip k) l s (FinTM.bufferTape (Nat.bits k)) 0 =
      readAt c s l ip k := by simp [regCfg, readAt]
  rw [← he]
  exact readFrame_reg c r s hrs hrp l l ip k _ 0 (by omega) (by omega)

/-- The comparison fragment is framed, with its common head position bounded by the
counter word rather than by the possibly much longer index word.

**Proof sketch.** Apply the received equality fragment with the counter as its first
register. Its trace moves the two heads together, so the counter length bounds both;
rewrite its configuration view into the frame and use monotonicity of binary length. -/
private theorem read_eq (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (i k : ℕ) (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i))
    (hrp : c.workTapePos r = 0) (hk : k ≤ x.length)
    (ip : Fin (x.length + 2)) :
    ∃ T, rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl .eC) ip k) T =
        readAt c s (.inl (if k = i then .yes else .no)) ip k ∧
      ∀ n < T, readFrame c r s
        (rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl .eC) ip k) n) := by
  obtain ⟨T, he, hm⟩ := eq_run (readModel r s) (fun j => j.elim0) s r (Ne.symm hrs)
    (.inl .eC) (.inl .eBy) (.inl .eBn) (.inl .yes) (.inl .no)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl
    (readAt c s (.inl .eC) ip k) k i (by simp [readAt])
    (by simp [readAt, hrs, hr])
  have view (l : RdPh ⊕ Option Bool) :
      eqCfg (readAt c s (.inl .eC) ip k) l s r 0 = readAt c s l ip k := by
    simp [eqCfg, readAt, Function.update_of_ne hrs, hrp]
  rw [view, view] at he
  refine ⟨T, ?_, fun n hn => ?_⟩
  · simpa only [apply_ite Sum.inl] using he
  · rw [view] at hm
    obtain ⟨l, p, he', _, hlo, hhi⟩ := hm n hn
    refine ⟨l, ip, FinTM.bufferTape (Nat.bits k), p, p, ?_, hlo, ?_, hlo, ?_⟩
    · rw [he']; simp [eqCfg, readAt]
    all_goals
      have hw := length_bits_mono (show k ≤ x.length + 1 by omega)
      omega

/-- One ordinary model step applies the frozen table. -/
private theorem read_one (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (ph : RdPh) (ip : Fin (x.length + 2)) (k : ℕ) :
    rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl ph) ip k) 1 =
      (readTr r s Sum.inl Sum.inr ph (inSym x ip.val)
        (readAt c s (.inl ph) ip k).workTapeSymbols).apply (readAt c s (.inl ph) ip k) := by
  rw [rrun_one, rstep_noncall (readModel r s) (fun j => j.elim0) _ (.inl ph) rfl rfl]
  simp only [MultiTapeTM.step, readModel, readAt, inputSymbol_eq, inSym]

/-- Rewind and clear restore the boundary input head and the empty counter.

**Proof sketch.** Invoke `rewind_x` at the current input position, then `clr_run` on the
counter. Both leave the index tape and all unrelated tapes unchanged. -/
private theorem read_cleanup (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (hrp : c.workTapePos r = 0) (k : ℕ) (hk : k ≤ x.length)
    (ip : Fin (x.length + 2)) (a : Option Bool) :
    ∃ T, rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl (.rw₁ a)) ip k) T =
        readAt c s (.inr a) 1 0 ∧
      ∀ n < T, readFrame c r s
        (rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl (.rw₁ a)) ip k) n) := by
  obtain ⟨A, heA, hmA⟩ := rewind_x (readModel r s) (fun j => j.elim0)
    (readAt c s (.inl (.rw₁ a)) ip k) s 0 (.inl (.rw₁ a)) (.inl (.rw₂ a)) (.inl (.cR a))
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl ip
  have xv (l : RdPh ⊕ Option Bool) (jp : Fin (x.length + 2)) :
      xCfg (readAt c s (.inl (.rw₁ a)) ip k) l jp s 0 = readAt c s l jp k := by
    simp [xCfg, readAt]
  rw [xv, xv] at heA
  have hone : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by
    apply Fin.ext; simp
  rw [hone] at heA
  obtain ⟨B, heB, hmB⟩ := clr_run (readModel r s) (fun j => j.elim0) s
    (.inl (.cR a)) (.inl (.cE a)) (.inr a)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (readAt c s (.inl (.cR a)) 1 k) k
  have rv (l : RdPh ⊕ Option Bool) (j : ℕ) :
      regCfg (readAt c s (.inl (.cR a)) 1 k) l s (FinTM.bufferTape (Nat.bits j)) 0 =
      readAt c s l 1 j := by simp [regCfg, readAt]
  rw [rv, rv] at heB
  refine ⟨A + B, by rw [rrun_add, heA, heB], fun n hn => ?_⟩
  by_cases hnA : n < A
  · rw [xv] at hmA
    obtain ⟨l, jp, he, _⟩ := hmA n hnA
    rw [he, xv]
    exact readFrame_at c r s hrs hrp l jp k
  · have hn' : n = A + (n - A) := by omega
    rw [hn', rrun_add, heA]
    rw [rv] at hmB
    obtain ⟨l, f, p, he, _, hlo, hhi⟩ := hmB (n - A) (by omega)
    rw [he]
    exact readFrame_reg c r s hrs hrp _ l 1 k f p hlo
      (hhi.trans (by exact_mod_cast length_bits_mono (show k ≤ x.length + 1 by omega)))

/-- Advance one counter/input position when both the requested index and the input end
are still ahead.

**Proof sketch.** The received equality fragment answers no. One table step advances the
input head, and the received increment fragment advances the counter. -/
private theorem read_advance (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (i k : ℕ) (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i))
    (hrp : c.workTapePos r = 0) (hk : k < min i x.length) :
    ∃ T, rrun (readModel r s) (fun j => j.elim0)
        (readAt c s (.inl .eC) ⟨k + 1, by omega⟩ k) T =
        readAt c s (.inl .eC) ⟨k + 2, by omega⟩ (k + 1) ∧
      ∀ n < T, readFrame c r s (rrun (readModel r s) (fun j => j.elim0)
        (readAt c s (.inl .eC) ⟨k + 1, by omega⟩ k) n) := by
  obtain ⟨A, heA, hmA⟩ := read_eq c r s hrs i k hr hrp (by omega) ⟨k + 1, by omega⟩
  rw [if_neg (show k ≠ i by omega)] at heA
  have he1 : rrun (readModel r s) (fun j => j.elim0)
      (readAt c s (.inl .no) ⟨k + 1, by omega⟩ k) 1 =
      readAt c s (.inl .iC) ⟨k + 2, by omega⟩ k := by
    rw [read_one, inSym_succ, List.getElem?_eq_getElem (show k < x.length by omega)]
    simp only [readTr]
    refine Cfg.ext rfl ?_ ?_ ?_ (by simp [Action.apply, xAct, readAt])
    · apply Fin.ext
      simpa only [Action.apply, xAct, readAt] using
        (moveInputPos_pos_val (x := x) ⟨k + 1, by omega⟩ (by dsimp; omega))
    · funext j z; simp [Action.apply, xAct, readAt]
    · funext j; simp [Action.apply, xAct, readAt]
  obtain ⟨B, heB, hmB⟩ := inc_run (readModel r s) (fun j => j.elim0) s
    (.inl .iC) (.inl .iB) (.inl .eC) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
    (readAt c s (.inl .iC) ⟨k + 2, by omega⟩ k) k
  have rv (l : RdPh ⊕ Option Bool) (j : ℕ) :
      regCfg (readAt c s (.inl .iC) ⟨k + 2, by omega⟩ k) l s (FinTM.bufferTape (Nat.bits j)) 0 =
      readAt c s l ⟨k + 2, by omega⟩ j := by simp [regCfg, readAt]
  rw [rv, rv] at heB
  refine ⟨A + (1 + B), by rw [rrun_add, heA, rrun_add, he1, heB], fun n hn => ?_⟩
  by_cases hnA : n < A
  · exact hmA n hnA
  · have hn' : n = A + (n - A) := by omega
    rw [hn', rrun_add, heA]
    by_cases heq : n - A = 0
    · rw [heq, rrun_zero]
      exact readFrame_at c r s hrs hrp _ _ _
    · have hn'' : n - A = 1 + (n - A - 1) := by omega
      rw [hn'', rrun_add, he1]
      rw [rv] at hmB
      obtain ⟨l, f, p, he, _, hlo, hhi⟩ := hmB (n - A - 1) (by omega)
      rw [he]
      exact readFrame_reg c r s hrs hrp _ l _ k f p hlo
        (hhi.trans (by exact_mod_cast length_bits_mono (show k + 1 ≤ x.length + 1 by omega)))

/-- At the smaller of the desired index and input length, read the answer and clean up.

**Proof sketch.** Equality selects the requested cell when the index is reached; otherwise
this is the right blank and the requested answer is also `none`. Rewind and clear complete
the routine. -/
private theorem read_finish (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (i : ℕ) (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i))
    (hrp : c.workTapePos r = 0) :
    ∃ T, rrun (readModel r s) (fun j => j.elim0)
        (readAt c s (.inl .eC) ⟨min i x.length + 1, by omega⟩ (min i x.length)) T =
        readAt c s (.inr x[i]?) 1 0 ∧
      ∀ n < T, readFrame c r s (rrun (readModel r s) (fun j => j.elim0)
        (readAt c s (.inl .eC) ⟨min i x.length + 1, by omega⟩ (min i x.length)) n) := by
  let k := min i x.length
  let ip : Fin (x.length + 2) := ⟨k + 1, by dsimp [k]; omega⟩
  obtain ⟨A, heA, hmA⟩ := read_eq c r s hrs i k hr hrp (by dsimp [k]; omega) ip
  have he1 : rrun (readModel r s) (fun j => j.elim0)
      (readAt c s (.inl (if k = i then .yes else .no)) ip k) 1 =
      readAt c s (.inl (.rw₁ x[i]?)) ip k := by
    by_cases hki : k = i
    · rw [if_pos hki, read_one]
      have hin : inSym x ip.val = x[i]? := by dsimp [ip]; rw [inSym_succ, hki]
      rw [hin]
      simp [readTr, goAct, Action.apply, readAt]
    · have hklen : k = x.length := by dsimp [k] at *; omega
      have hi : x.length ≤ i := by dsimp [k] at *; omega
      rw [if_neg hki, read_one]
      have hin : inSym x ip.val = none := by dsimp [ip]; rw [inSym_succ, hklen]; simp
      rw [hin, List.getElem?_eq_none hi]
      simp [readTr, goAct, Action.apply, readAt]
  obtain ⟨B, heB, hmB⟩ := read_cleanup c r s hrs hrp k (by dsimp [k]; omega) ip x[i]?
  refine ⟨A + (1 + B), by rw [rrun_add, heA, rrun_add, he1, heB], fun n hn => ?_⟩
  by_cases hnA : n < A
  · exact hmA n hnA
  · have hn' : n = A + (n - A) := by omega
    rw [hn', rrun_add, heA]
    by_cases heq : n - A = 0
    · rw [heq, rrun_zero]
      exact readFrame_at c r s hrs hrp _ _ _
    · have hn'' : n - A = 1 + (n - A - 1) := by omega
      rw [hn'', rrun_add, he1]
      exact hmB (n - A - 1) (by omega)

/-- The proof-only model executes the whole routine with the original frame.

**Proof sketch.** Induct on the counter up to `min i |x|`, concatenate each bounded advance,
then append `read_finish`. All sub-runs come from the received fragments. -/
private theorem read_model_run (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (r s : Fin m)
    (hrs : r ≠ s) (i : ℕ) (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i))
    (hrp : c.workTapePos r = 0) :
    ∃ T, rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl .eC) 1 0) T =
        readAt c s (.inr x[i]?) 1 0 ∧
      ∀ n < T, readFrame c r s
        (rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl .eC) 1 0) n) := by
  have rounds : ∀ (k : ℕ) (hk : k ≤ min i x.length), ∃ T,
      rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl .eC) 1 0) T =
        readAt c s (.inl .eC) ⟨k + 1, by omega⟩ k ∧
      ∀ n < T, readFrame c r s
        (rrun (readModel r s) (fun j => j.elim0) (readAt c s (.inl .eC) 1 0) n) := by
    intro k
    induction k with
    | zero => intro hk; exact ⟨0, rfl, fun n hn => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨A, heA, hmA⟩ := ih (by omega)
      obtain ⟨B, heB, hmB⟩ := read_advance c r s hrs i k hr hrp (by omega)
      refine ⟨A + B, by rw [rrun_add, heA, heB], fun n hn => ?_⟩
      by_cases hnA : n < A
      · exact hmA n hnA
      · have hn' : n = A + (n - A) := by omega
        rw [hn', rrun_add, heA]
        exact hmB (n - A) (by omega)
  obtain ⟨A, heA, hmA⟩ := rounds (min i x.length) le_rfl
  obtain ⟨B, heB, hmB⟩ := read_finish c r s hrs i hr hrp
  refine ⟨A + B, by rw [rrun_add, heA, heB], fun n hn => ?_⟩
  by_cases hnA : n < A
  · exact hmA n hnA
  · have hn' : n = A + (n - A) := by omega
    rw [hn', rrun_add, heA]
    exact hmB (n - A) (by omega)

/-- The proof-only model has no calls, so its register run is its ordinary machine run. -/
private theorem read_run_eq (r s : Fin m) (c : Cfg m Bool (RdPh ⊕ Option Bool) x) (n : ℕ) :
    rrun (readModel r s) (fun j => j.elim0) c n = (readModel r s).tm.runFrom c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rrun_succ, ih, MultiTapeTM.runFrom_succ_eq_step']
    cases hs : ((readModel r s).tm.runFrom c n).state <;>
      simp [rstep, MultiTapeTM.step, hs, readModel]

/-- Every state strictly before an exit in the proof-only model is a fragment phase.

**Proof sketch.** The final exit is live. Earlier configurations are live because halts are
absorbing. An earlier exit would halt on its next step, contradicting that liveness. -/
private theorem read_model_phase (r s : Fin m) (c : Cfg m Bool (RdPh ⊕ Option Bool) x)
    (T : ℕ) (a : Option Bool)
    (hT : (rrun (readModel r s) (fun j => j.elim0) c T).state = some (.inr a)) :
    ∀ n < T, ∃ ph, (rrun (readModel r s) (fun j => j.elim0) c n).state = some (.inl ph) := by
  simp only [read_run_eq] at hT ⊢
  have hl := (readModel r s).tm.runFrom_state_ne_none_of_le c T
    (by rw [hT]; simp)
  intro n hn
  cases he : ((readModel r s).tm.runFrom c n).state with
  | none => exact (hl n (by omega) he).elim
  | some l =>
    cases l with
    | inl ph => exact ⟨ph, rfl⟩
    | inr b =>
      exfalso
      apply hl (n + 1) (by omega)
      rw [MultiTapeTM.runFrom_succ_eq_step']
      simp [MultiTapeTM.step, he, readModel, junkAct, Action.apply]

/-- The frozen table commutes with replacing its phase and exit labels. -/
private theorem read_action_map (r s : Fin m) (st : RdPh → Λ) (ex : Option Bool → Λ)
    (ph : RdPh) (a : Option Bool) (w : Fin m → Option Bool) :
    (readTr r s Sum.inl Sum.inr ph a w).mapState (Sum.elim st ex) = readTr r s st ex ph a w := by
  cases ph <;>
    simp [readTr, eqCAct, eqBAct, incCAct, incBAct, rw2Act, toEndAct, clrEAct,
      regAct, mv2Act, xAct, goAct, Action.mapState, apply_ite] <;>
    repeat' first | split | rfl

section Read

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r s : Fin m) (hrs : r ≠ s)
  (st : RdPh → Λ) (ex : Option Bool → Λ)
  (htr : ∀ ph a w, P.tm.tr (st ph) a w = readTr r s st ex ph a w)
  (hc : ∀ ph, P.call (st ph) = none)

include hrs htr hc in
/-- **The input-read fragment** (phase P4.4b; proved): from phase `eC`, with
`bits i` on the index register `r`, an empty counter register `s`, both heads on cell `0` and
the input head on position `1`, the program reaches the exit `ex x[i]?` — symbol `i` of the
input, `none` when `i ≥ |x|` — in the same configuration otherwise (registers, heads, input
position and output restored). Throughout, only registers `s` and `r` change (the tape of `s`,
the heads of both), both heads stay in `[-1, |bits (|x| + 1)|]`, and every state is an
ordinary fragment state: the fragment's space is these two ranges, independently of `i`.
A hand-built fragment: no received layer reads a general input at a register-held position
(the `Parse` fragments assume unary-first inputs).

**Proof sketch.** Induction on the counter value `k ≤ min i |x|`, the input head on position
`k + 1`. `eq_run` (with `r₁ := s`, so both heads stay within `|bits k|`) compares `bits k`
with `bits i`. If `k = i`, phase `yes` takes `inSym x (i + 1) = x[i]?`. Otherwise phase `no`
reads `inSym x (k + 1)`: at the right blank (`k = |x| < i`) the symbol taken is
`none = x[i]?`; on a letter (`k < |x|`) the head steps right and `inc_run` turns `bits k` into
`bits (k + 1)`, `k + 1 ≤ |x|`. Then `rewind_x` returns the input head to position `1`, and
`clr_run` empties the counter (its head within `|bits k|`). -/
theorem readIn_run (c : Cfg m Bool Λ x) (i : ℕ)
    (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i)) (hs : c.workTapes s = FinTM.bufferTape [])
    (hrp : c.workTapePos r = 0) (hsp : c.workTapePos s = 0) (hip : c.inputPos.val = 1) :
    ∃ T, rrun P oracle { c with state := some (st .eC) } T = { c with state := some (ex x[i]?) } ∧
      ∀ t < T, ∃ (ph : RdPh) (ip : Fin (x.length + 2)) (f : ℤ → Option Bool) (q q' : ℤ),
        rrun P oracle { c with state := some (st .eC) } t =
          ⟨some (st ph), ip, Function.update c.workTapes s f,
            Function.update (Function.update c.workTapePos s q) r q', c.output⟩ ∧
        -1 ≤ q ∧ q ≤ (Nat.bits (x.length + 1)).length ∧
        -1 ≤ q' ∧ q' ≤ (Nat.bits (x.length + 1)).length := by
  let c₀ : Cfg m Bool (RdPh ⊕ Option Bool) x :=
    ⟨some (.inl .eC), c.inputPos, c.workTapes, c.workTapePos, c.output⟩
  let d₀ := readAt c₀ s (.inl .eC) 1 0
  let rename : (RdPh ⊕ Option Bool) → Λ := Sum.elim st ex
  obtain ⟨T, hT, hmid⟩ := read_model_run c₀ r s hrs i hr hrp
  have hphase := read_model_phase r s d₀ T x[i]? (by rw [hT]; rfl)
  have hm : ∀ n ≤ T, rrun P oracle (d₀.mapState rename) n =
      (rrun (readModel r s) (fun j => j.elim0) d₀ n).mapState rename := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      obtain ⟨ph, hph⟩ := hphase n (by omega)
      rw [rrun_succ, ih (by omega), rrun_succ]
      rw [rstep_noncall P oracle _ (st ph) (by simp [Cfg.mapState, hph, rename]) (hc ph),
        rstep_noncall (readModel r s) (fun j => j.elim0) _ (.inl ph) hph rfl]
      simp only [MultiTapeTM.step, Cfg.mapState, hph, Option.map_some, rename, Sum.elim_inl]
      rw [htr]
      rw [← read_action_map]
      rfl
  have hstart : d₀.mapState rename = {c with state := some (st .eC)} := by
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simpa [d₀, c₀, readAt, Cfg.mapState] using hip.symm
    · simp [d₀, c₀, readAt, Cfg.mapState, Nat.zero_bits, ← hs, Function.update_eq_self]
    · simp [d₀, c₀, readAt, Cfg.mapState, ← hsp, Function.update_eq_self]
  rw [← hstart]
  refine ⟨T, ?_, fun n hn => ?_⟩
  · rw [hm T le_rfl, hT]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simpa [readAt, Cfg.mapState] using hip.symm
    · simp [readAt, c₀, Cfg.mapState, Nat.zero_bits, ← hs, Function.update_eq_self]
    · simp [readAt, c₀, Cfg.mapState, ← hsp, Function.update_eq_self]
  · obtain ⟨ph, hph⟩ := hphase n hn
    obtain ⟨l, ip, f, p, q, he, hlo, hhi, hlo', hhi'⟩ := hmid n hn
    have hl : l = Sum.inl ph := by rw [he] at hph; exact Option.some.inj hph
    subst l
    refine ⟨ph, ip, f, p, q, ?_, hlo, hhi, hlo', hhi'⟩
    rw [hm n (by omega), he]
    rfl

end Read

end LogProg

/-! ## Input access as a language pair -/

/-- The bit language of the identity: `{⟨u, bits i⟩ | uᵢ = 1}` (`0`-based; `false` beyond the
end). -/
def inputBitLang : Language Bool := indexLang fun u i => u.getD i false = true

/-- The length language of the identity: `{⟨u, bits i⟩ | i < |u|}`. -/
def inputLenLang : Language Bool := indexLang fun u i => i < u.length

/-- **Input random access is logspace** (phase P4.4b; spec, fill pending): the identity is
implicitly logspace computable — its output bound is trivial and its two query languages,
`Complexity.inputBitLang` and `Complexity.inputLenLang`, are in `L`. [AB09, §4.1: a pointer
into the input] It is stated, and will be proved, as a corollary of
`Complexity.LogProg.readIn_run`.

**Proof sketch.** The bound is `|x| ≤ 1 · (|x| + 1)^1`. For the two languages, one call-free
register program with a mode bit, compiled against the empty bank `LogProg.Dbl.nilTM` as in
`LogProg.dblLang_mem` (`compile_space`): on `y`, validate `y = pairEncode z (bits r)` (an
aligned two-cell scan to the first aligned `[false, true]`, then a canonical tail — empty or
ending in `true`), reading each cell with `readIn_run`; reject otherwise. Then walk a counter
`k` over the pairs of `dbl z`, comparing `bits k` with the tail in lockstep (the comparison
pattern of `LogProg.cmpPlain_run`); on a match answer cell `2k` (resp. `true`), at the
separator answer `false`. Each register holds a counter of at most `|bits (|y| + 1)|` bits,
and `readIn_run` keeps every head within `[-1, |bits (|y| + 1)|]`. So each work tape visits
`O(logSpace |y|)` cells, its origin and the boundary cells included (an interval `[-1, W]` has
`W + 2` cells), and `compile_space` gives the space bound from these ranges. -/
theorem implicitlyLogspaceComputable_id : ImplicitlyLogspaceComputable id := by
  sorry

/-- `Complexity.inputBitLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputBitLang_mem : inputBitLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.1

/-- `Complexity.inputLenLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputLenLang_mem : inputLenLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.2

end Complexity
