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
* `Complexity.pairEncode_getD` — a shared bit-address formula for doubled fields,
  separators, and suffixes of paired inputs.
* `Complexity.LogProg.alignedPair_loop` — a bounded ARM pair scan at any positive stride.
* `Complexity.LogProg.register_update_le` — the shared register-bound update rule.
* `Complexity.LogProg.registerCopy_loop` — copy by bounded counting, preserving the source.
* `Complexity.LogProg.registerScale_loop` — consume a source into a scaled destination.
* `Complexity.LogProg.canonicalTail_loop` — canonical-tail and width validation before decoding.
* `Complexity.LogProg.boundedDecode_loop` — reverse binary decoding after the width check.
* `Complexity.LogProg.indexedSeek_loop` — bounded positioning within a strided segment.
* `Complexity.LogProg.inputLength_loop` — a bounded ARM loop counting a general input
  through its length-query oracle.
* `Complexity.LogProg.readIn_run` — the input-read fragment (proved; phase-P4.4b
  statement).
* `Complexity.implicitlyLogspaceComputable_id` — input random access in `L` (proved;
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

/-- Reading a paired word by position selects a doubled first-field bit, a separator bit,
or a suffix bit. The default is `false` beyond the complete word. This common address rule
serves the nested layouts of index dropping, query reshaping, and multiplication.

**Proof sketch.** Within the first field, write the address as twice its quotient by two
plus its parity and cite `getElem?_dbl`. Outside that field, the append lookup rule exposes
the separator or the suffix. -/
theorem pairEncode_getD (u v : List Bool) (j : ℕ) :
    (pairEncode u v).getD j false =
      if j < 2 * u.length then u.getD (j / 2) false
      else if j = 2 * u.length then false
      else if j = 2 * u.length + 1 then true
      else v.getD (j - 2 * u.length - 2) false := by
  by_cases hj : j < 2 * u.length
  · rw [if_pos hj, pairEncode_eq_dbl, List.getD_eq_getElem?_getD,
      List.append_assoc, List.getElem?_append_left (by simpa using hj)]
    have hc : j / 2 < u.length := by omega
    have hread : (dbl u)[j]? = some u[j / 2] := by
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · have he : 2 * (j / 2) + (false : Bool).toNat = j := by simp; omega
        simpa only [he] using getElem?_dbl u (j / 2) hc false
      · have he : 2 * (j / 2) + (true : Bool).toNat = j := by simp; omega
        simpa only [he] using getElem?_dbl u (j / 2) hc true
    rw [hread]
    simp [List.getD_eq_getElem?_getD, hc]
  · rw [if_neg hj, pairEncode_eq_dbl, List.getD_eq_getElem?_getD,
      List.append_assoc, List.getElem?_append_right (by simp; omega)]
    simp only [length_dbl]
    by_cases he : j = 2 * u.length
    · subst j; simp
    · rw [if_neg he]
      by_cases he' : j = 2 * u.length + 1
      · subst j; simp
      · rw [if_neg he', show j - 2 * u.length = (j - 2 * u.length - 2) + 1 + 1 by omega]
        rfl

namespace LogProg

open Classical

/-- A length-query/increment loop counts the host input, with all registers bounded by
the chosen bound. The oracle law is needed only up to the first failing query, at the
input length. This shared ARM fragment is used by the query validators.

**Proof sketch.** Induct on the input length minus the current counter. Below the end,
the length call succeeds and increment reduces the remaining count. At the end, the call
fails and exits. The counter never exceeds the input length; all other registers stay
unchanged. Both instructions meet the received ARM syntactic preconditions. -/
theorem inputLength_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool) (r : Fin m) (j : Fin d)
    (scan inc done : Λ)
    (hscan : A scan = .call j .whole [r] inc done)
    (hinc : A inc = .inc r scan)
    (hquery : ∀ n ≤ x.length, oracle j (pairEncode x (Nat.bits n)) = decide (n < x.length))
    (B : ℕ) (hB : x.length ≤ B) (v : Fin m → ℕ)
    (hv : ∀ s, v s ≤ B) (hr : v r ≤ x.length) :
    AReach A oracle x (fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B)
      (some scan, v, none) (some done, Function.update v r x.length, none) := by
  generalize hN : x.length - v r = N
  induction N using Nat.strong_induction_on generalizing v with
  | h N ih =>
    have hs : astep A oracle x (some scan, v, none) =
        (some (if v r < x.length then inc else done), v, none) := by
      simp only [astep, hscan, vword_whole₁, hquery (v r) hr, decide_eq_true_eq]
    have hg : PreS A x (some scan, v, none) ∧ ∀ s, v s ≤ B :=
      ⟨by simp [PreS, hscan], hv⟩
    by_cases hlt : v r < x.length
    · let v' := Function.update v r (v r + 1)
      have hv' : ∀ s, v' s ≤ B := by
        intro s
        by_cases he : s = r
        · subst s; dsimp [v']; rw [Function.update_self]; omega
        · simpa [v', Function.update_of_ne he] using hv s
      have hr' : v' r ≤ x.length := by simp [v']; omega
      have hremain : x.length - v' r < N := by simp [v']; omega
      have hc := ih (x.length - v' r) hremain v' hv' hr' rfl
      have hi : astep A oracle x (some inc, v, none) = (some scan, v', none) := by
        simp [astep, hinc, v']
      apply AReach.step hg
      rw [hs, if_pos hlt]
      apply AReach.step ⟨by simp [PreS, hinc], hv⟩
      rw [hi]
      simpa only [v', Function.update_idem] using hc
    · have he : v r = x.length := by omega
      have hp := AReach.single (A := A) (oracle := oracle) (x := x)
        (G := fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B) (a := (some scan, v, none)) hg
      have hs' : astep A oracle x (some scan, v, none) = (some done, v, none) := by
        rw [hs, if_neg hlt]
      have hvdone : Function.update v r x.length = v := by
        rw [← he, Function.update_eq_self]
      rw [hvdone]
      simpa only [hs'] using hp

/-- A bounded straight sequence of register increments. The labels may belong to any
larger ARM; no new reachability relation is needed. -/
private lemma arm_increments {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool) (r : Fin m)
    (labels : ℕ → Λ) (k B : ℕ)
    (hcode : ∀ i < k, A (labels i) = .inc r (labels (i + 1)))
    (v : Fin m → ℕ) (hv : ∀ s, v s ≤ B) (hk : v r + k ≤ B) :
    AReach A oracle x (fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B)
      (some (labels 0), v, none)
      (some (labels k), Function.update v r (v r + k), none) := by
  induction k generalizing labels v with
  | zero => simpa only [Nat.add_zero, Function.update_eq_self] using
      (AReach.refl (A := A) (oracle := oracle) (x := x)
        (G := fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B) (some (labels 0), v, none))
  | succ k ih =>
    have hc := hcode 0 (by omega)
    apply AReach.step ⟨by simp [PreS, hc], hv⟩
    simp only [astep, hc]
    have hv' : ∀ s, Function.update v r (v r + 1) s ≤ B := by
      intro s
      by_cases hs : s = r
      · subst s; simp; omega
      · simpa [Function.update_of_ne hs] using hv s
    have hp := ih (fun i => labels (i + 1))
      (fun i hi => hcode (i + 1) (by omega)) (Function.update v r (v r + 1)) hv'
      (by simp; omega)
    simpa only [Function.update_self, Function.update_idem, Nat.add_assoc,
      Nat.add_comm 1 k] using hp

/-- An aligned pair scan using the input-bit oracle, at any positive stride. It rejects
exactly failed pair decodes and otherwise leaves the pointer just beyond the separator.
The scan imposes no canonicality condition on either field. Four increment chains move
past a first `false`, a first `true`, an equal pair, or the separator respectively.

**Proof sketch.** Induct by two input letters. An empty word fails the first end test;
a singleton fails the second. Equal letters advance and recur, `01` exits at the payload,
and `10` rejects. Each advance is `arm_increments`; all pointer values stay below the
supplied end address. This is the shared aligned-scan argument for nested query layouts. -/
theorem alignedPair_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (r limit : Fin m) (j : Fin d) (scan first : Λ) (test read : Bool → Λ)
    (fail done : Λ) (advance : Fin 4 → ℕ → Λ) (stride B : ℕ)
    (hstride : 0 < stride) (hrlimit : r ≠ limit)
    (hscan : A scan = .jeq r limit fail first)
    (hfirst : A first = .call j .whole [r] (advance 1 0) (advance 0 0))
    (htest : ∀ b, A (test b) = .jeq r limit fail (read b))
    (hread : ∀ b, A (read b) = .call j .whole [r]
      (if b then advance 2 0 else advance 3 0) (if b then fail else advance 2 0))
    (hadvance : ∀ k i, i < stride → A (advance k i) = .inc r (advance k (i + 1)))
    (hend : advance 0 stride = test false ∧ advance 1 stride = test true ∧
      advance 2 stride = scan ∧ advance 3 stride = done)
    (w : List Bool) (v : Fin m → ℕ) (hv : ∀ s, v s ≤ B)
    (hlimit : v limit = v r + stride * w.length)
    (horacle : ∀ i < w.length,
      oracle j (pairEncode x (Nat.bits (v r + stride * i))) = w.getD i false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length,
        AReach A oracle x (fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B)
          (some scan, v, none) (some fail, Function.update v r (v r + stride * t), none)
    | some (a, _) =>
        AReach A oracle x (fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B)
          (some scan, v, none)
          (some done, Function.update v r (v r + stride * (2 * a.length + 2)), none) := by
  let G := fun a : AConf m Λ => PreS A x a ∧ ∀ s, a.2.1 s ≤ B
  have upd : ∀ (v : Fin m → ℕ) (q : ℕ), (∀ s, v s ≤ B) → q ≤ B →
      ∀ s, Function.update v r q s ≤ B := by
    intro v q hv hq s
    by_cases hs : s = r
    · subst s; simpa using hq
    · simpa [Function.update_of_ne hs] using hv s
  have initial : ∀ (b : Bool) (tail : List Bool) (v : Fin m → ℕ),
      (∀ s, v s ≤ B) → v limit = v r + stride * (b :: tail).length →
      oracle j (pairEncode x (Nat.bits (v r))) = b →
      AReach A oracle x G (some scan, v, none)
        (some (test b), Function.update v r (v r + stride), none) := by
    intro b tail v hv hl ho
    have hstep : v r + stride ≤ B := by
      have := hv limit
      have := Nat.le_mul_of_pos_right stride (show 0 < (b :: tail).length by simp)
      omega
    have hne : v r ≠ v limit := by
      have := Nat.le_mul_of_pos_right stride (show 0 < (b :: tail).length by simp)
      omega
    apply AReach.step ⟨by simp [PreS, hscan, hrlimit], hv⟩
    simp only [astep, hscan, if_neg hne]
    apply AReach.step ⟨by simp [PreS, hfirst], hv⟩
    simp only [astep, hfirst, vword_whole₁, ho]
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, hend.1] using
        arm_increments A oracle x r (advance 0) stride B (hadvance 0) v hv hstep
    · simpa only [↓reduceIte, hend.2.1] using
        arm_increments A oracle x r (advance 1) stride B (hadvance 1) v hv hstep
  induction w using List.twoStepInduction generalizing v with
  | nil =>
    simp only [pairDecode]
    refine ⟨0, by simp, ?_⟩
    have he : v r = v limit := by simpa using hlimit.symm
    simpa only [astep, hscan, if_pos he, Nat.mul_zero, Nat.add_zero,
      Function.update_eq_self] using
      (AReach.single (A := A) (oracle := oracle) (x := x) (G := G)
        (a := (some scan, v, none)) ⟨by simp [PreS, hscan, hrlimit], hv⟩)
  | singleton b =>
    have ho := horacle 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at ho
    have hi := initial b [] v hv hlimit ho
    let v' := Function.update v r (v r + stride)
    have hv' : ∀ s, v' s ≤ B := by
      apply upd v _ hv
      have := hv limit
      simp only [List.length_singleton, Nat.mul_one] at hlimit
      omega
    have he : v' r = v' limit := by simp [v', hrlimit.symm]; simpa using hlimit.symm
    have hp : AReach A oracle x G (some (test b), v', none) (some fail, v', none) := by
      simpa only [astep, htest, if_pos he] using
        (AReach.single (A := A) (oracle := oracle) (x := x) (G := G)
          (a := (some (test b), v', none)) ⟨by simp [PreS, htest, hrlimit], hv'⟩)
    cases b <;> simp only [pairDecode] <;>
      exact ⟨1, by simp, by simpa [Nat.mul_one] using hi.trans hp⟩
  | cons_cons b c tail ih _ =>
    have hb := horacle 0 (by simp)
    have hc := horacle 1 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at hb
    simp only [Nat.mul_one, List.getD_cons_succ, List.getD_cons_zero] at hc
    have hi := initial b (c :: tail) v hv hlimit hb
    let v' := Function.update v r (v r + stride)
    let v'' := Function.update v r (v r + 2 * stride)
    have hbound : v r + 2 * stride ≤ B := by
      have := hv limit
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hlimit
      omega
    have hv' : ∀ s, v' s ≤ B := upd v _ hv (by omega)
    have hv'' : ∀ s, v'' s ≤ B := upd v _ hv hbound
    have hne : v' r ≠ v' limit := by
      simp only [v', Function.update_self, Function.update_of_ne hrlimit.symm]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hlimit
      omega
    have hcall : AReach A oracle x G (some (test b), v', none)
        (some (if c then (if b then advance 2 0 else advance 3 0)
          else (if b then fail else advance 2 0)), v', none) := by
      apply AReach.step ⟨by simp [PreS, htest, hrlimit], hv'⟩
      simp only [astep, htest, if_neg hne]
      have ho : oracle j (pairEncode x (Nat.bits (v' r))) = c := by simpa [v'] using hc
      simpa only [astep, hread, vword_whole₁, ho] using
        (AReach.single (A := A) (oracle := oracle) (x := x) (G := G)
          (a := (some (read b), v', none)) ⟨by simp [PreS, hread], hv'⟩)
    have hinc : ∀ k : Fin 4, AReach A oracle x G
        (some (advance k 0), v', none) (some (advance k stride), v'', none) := by
      intro k
      have hp := arm_increments A oracle x r (advance k) stride B (hadvance k) v' hv'
        (by simp [v']; omega)
      simpa only [v', v'', Function.update_self, Function.update_idem,
        show v r + stride + stride = v r + 2 * stride by omega] using hp
    have hnext : v'' limit = v'' r + stride * tail.length := by
      simp only [v'', Function.update_self, Function.update_of_ne hrlimit.symm]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hlimit
      omega
    have honext : ∀ i < tail.length,
        oracle j (pairEncode x (Nat.bits (v'' r + stride * i))) = tail.getD i false := by
      intro i hi
      have hp := horacle (i + 2) (by simp; omega)
      simpa only [v'', Function.update_self, Nat.mul_add,
        show v r + (stride * i + stride * 2) = v r + 2 * stride + stride * i by omega,
        List.getD_cons_succ] using hp
    have hr := ih v'' hv'' hnext honext
    by_cases heq : b = c
    · cases heq
      have he : pairDecode (b :: b :: tail) = (pairDecode tail).map
          (fun ab => (b :: ab.1, ab.2)) := by cases b <;> rfl
      have hm : AReach A oracle x G (some (test b), v', none)
          (some (advance 2 0), v', none) := by cases b <;> simpa only [↓reduceIte] using hcall
      have hp := hi.trans (hm.trans (by simpa only [hend.2.2.1] using hinc 2))
      rw [he]
      cases hd : pairDecode tail with
      | none =>
        simp only [hd] at hr
        obtain ⟨t, ht, hrun⟩ := hr
        simp only [Option.map_none]
        refine ⟨t + 2, by simp; omega, ?_⟩
        simpa only [v'', Function.update_self, Function.update_idem, Nat.mul_add,
          show v r + 2 * stride + stride * t = v r + (stride * t + stride * 2) by omega]
          using hp.trans hrun
      | some ab =>
        rcases ab with ⟨a, t⟩
        simp only [hd] at hr
        simp only [Option.map_some, List.length_cons]
        have he : v r + 2 * stride + stride * (2 * a.length + 2) =
            v r + stride * (2 * (a.length + 1) + 2) := by ring
        simpa only [v'', Function.update_self, Function.update_idem, he] using hp.trans hr
    · cases b <;> cases c
      · exact False.elim (heq rfl)
      · have hp := hi.trans (hcall.trans (by simpa only [hend.2.2.2] using hinc 3))
        simpa only [pairDecode, List.length_nil, Nat.mul_zero, Nat.zero_add,
          Nat.mul_comm stride 2] using hp
      · simp only [pairDecode]
        exact ⟨1, by simp, by simpa only [Nat.mul_one] using hi.trans hcall⟩
      · exact False.elim (heq rfl)

/-! ### Shared bounded arithmetic and tail validation (B7 continuation 2 exports) -/

/-- Updating a bounded register by a bounded value preserves the common bound. -/
theorem register_update_le {m : ℕ} (v : Fin m → ℕ) (r : Fin m) (B n : ℕ)
    (hv : ∀ s, v s ≤ B) (hn : n ≤ B) : ∀ s, Function.update v r n s ≤ B := by
  intro s
  by_cases h : s = r
  · subst s; simpa using hn
  · simpa [Function.update_of_ne h] using hv s

/-- Counting a destination up to a distinct source copies its value without changing the
source. The destination may already contain any smaller value. This bounded ARM fragment
is shared by query validation, decoding, and nested-layout bookkeeping.

**Proof sketch.** Induct on the difference between source and destination. Equality exits;
otherwise increment the destination. Its value never exceeds the unchanged source. -/
theorem registerCopy_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool) (dst src : Fin m)
    (hne : dst ≠ src) (test bump done : Λ)
    (htest : A test = .jeq dst src done bump) (hbump : A bump = .inc dst test)
    (B : ℕ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v dst ≤ v src) :
    AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
      (some test, v, none) (some done, Function.update v dst (v src), none) := by
  generalize he : v src - v dst = k
  induction k generalizing v with
  | zero =>
    have eq : v dst = v src := by omega
    have vu : Function.update v dst (v src) = v := by
      rw [← eq, Function.update_eq_self]
    rw [vu]
    simpa [astep, htest, eq] using
      (AReach.single (A := A) (oracle := oracle) (x := x)
        (a := (some test, v, none)) ⟨by simp [PreS, htest, hne], hv⟩)
  | succ k ih =>
    have lt : v dst < v src := by omega
    let next := Function.update v dst (v dst + 1)
    have nv : ∀ r, next r ≤ B := register_update_le v dst B _ hv (by have := hv src; omega)
    have ns : next src = v src := Function.update_of_ne hne.symm _ _
    have nd : next dst = v dst + 1 := Function.update_self _ _ _
    have rest := ih next nv (by rw [ns, nd]; omega) (by rw [ns, nd]; omega)
    apply AReach.step ⟨by simp [PreS, htest, hne], hv⟩
    simp only [astep, htest, if_neg (Nat.ne_of_lt lt)]
    apply AReach.step ⟨by simp [PreS, hbump], hv⟩
    simpa only [astep, hbump, next, ns, Function.update_idem] using rest

/-- Moving a source into a destination with a fixed natural multiplier uses bounded
increment chains. The source is cleared. The source and final destination must fit the
same bound; this is the arithmetic fragment used by the bounded binary decoder.

**Proof sketch.** Decrement the source once and increment the destination by the multiplier,
citing the shared increment-chain argument. The weighted total is invariant, so each
intermediate value is bounded. Induct on the source value. -/
theorem registerScale_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool) (src dst : Fin m)
    (hne : src ≠ dst) (test down done : Λ) (inc : ℕ → Λ) (factor : ℕ)
    (htest : A test = .jz src done down) (hdown : A down = .dec src (inc 0))
    (hinc : ∀ i < factor, A (inc i) = .inc dst (inc (i + 1))) (hend : inc factor = test)
    (B : ℕ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (htotal : v dst + factor * v src ≤ B) :
    AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
      (some test, v, none)
      (some done, Function.update (Function.update v src 0) dst
        (v dst + factor * v src), none) := by
  generalize he : v src = k
  induction k generalizing v with
  | zero =>
    have vs : Function.update v src 0 = v := by rw [← he, Function.update_eq_self]
    simp only [Nat.mul_zero, Nat.add_zero, vs, Function.update_eq_self]
    simpa [astep, htest, he] using
      (AReach.single (A := A) (oracle := oracle) (x := x)
        (a := (some test, v, none)) ⟨by simp [PreS, htest], hv⟩)
  | succ k ih =>
    let downv := Function.update v src k
    let next := Function.update downv dst (v dst + factor)
    have dv : ∀ r, downv r ≤ B := register_update_le v src B k hv (by have := hv src; omega)
    have dd : downv dst = v dst := Function.update_of_ne hne.symm _ _
    have bound : v dst + factor ≤ B := by rw [he, Nat.mul_succ] at htotal; omega
    have nv : ∀ r, next r ≤ B := register_update_le downv dst B _ dv bound
    have ns : next src = k := by simp [next, downv, hne]
    have nd : next dst = v dst + factor := by simp [next]
    have total : next dst + factor * next src ≤ B := by
      rw [ns, nd]; rw [he, Nat.mul_succ] at htotal; omega
    have hmove := arm_increments A oracle x dst inc factor B hinc downv dv
      (by rw [dd]; exact bound)
    have rest := ih next nv total ns
    apply AReach.step ⟨by simp [PreS, htest], hv⟩
    simp only [astep, htest, he, Nat.succ_ne_zero, ↓reduceIte]
    apply AReach.step ⟨by simp [PreS, hdown], hv⟩
    simp only [astep, hdown, he, Nat.add_sub_cancel]
    have final : Function.update (Function.update next src 0) dst
        (next dst + factor * k) =
        Function.update (Function.update v src 0) dst (v dst + factor * (k + 1)) := by
      funext r
      by_cases hd : r = dst
      · subst r; simp only [Function.update_self, nd, Nat.mul_succ]; omega
      · by_cases hs : r = src
        · subst r; simp [hd]
        · simp [next, downv, Function.update_of_ne, hd, hs]
    rw [final] at rest
    simp only [hend, dd] at hmove
    exact hmove.trans rest

/-- Halving a nonzero cap removes exactly one binary digit. -/
private lemma access_width_half (n : ℕ) (hn : n ≠ 0) :
    (Nat.bits (n / 2)).length + 1 = (Nat.bits n).length := by
  have hp : 0 < (Nat.bits n).length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [bits_half, List.length_tail]
  omega

/-- A strided tail scan checks its width against a binary cap before decoding any value.
The finite-control bit remembers the last letter, with `true` accepting the empty tail.
Only the pointer and cap change; a failed width check exits without reading that letter.
Starting with last bit `true`, success says that the tail is canonical and fits the cap's
binary width. The same fragment serves bounded query tails at different physical strides.

**Proof sketch.** Test the end first. On each remaining letter, reject a zero cap;
otherwise read that letter, halve the cap, and advance the pointer by the stride.
Induction on the tail uses the fact that halving a nonzero number removes one binary digit.
The final remembered bit is the tail's last bit. -/
theorem canonicalTail_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (ptr limit cap : Fin m) (hpl : ptr ≠ limit) (hpc : ptr ≠ cap) (hcl : cap ≠ limit)
    (j : Fin d) (test : Bool → Λ) (check read fail done : Λ)
    (halve : Bool → Λ) (advance : Bool → ℕ → Λ) (stride B : ℕ) (hs : 0 < stride)
    (htest : ∀ b, A (test b) = .jeq ptr limit (if b then done else fail) check)
    (hcheck : A check = .jz cap fail read)
    (hread : A read = .call j .whole [ptr] (halve true) (halve false))
    (hhalve : ∀ b, A (halve b) = .half cap (advance b 0))
    (hadvance : ∀ b i, i < stride → A (advance b i) = .inc ptr (advance b (i + 1)))
    (hend : ∀ b, advance b stride = test b)
    (w : List Bool) (last : Bool) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v limit = v ptr + stride * w.length)
    (ho : ∀ i < w.length,
      oracle j (pairEncode x (Nat.bits (v ptr + stride * i))) = w.getD i false) :
    ∃ v', (∀ r, v' r ≤ B) ∧ v' ptr ≤ v limit ∧
      (∀ r, r ≠ ptr → r ≠ cap → v' r = v r) ∧
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some (test last), v, none)
        (some (if w.length ≤ (Nat.bits (v cap)).length then
          if w.getLastD last then done else fail else fail), v', none) := by
  induction w generalizing v last with
  | nil =>
    have eq : v ptr = v limit := by simpa using hl.symm
    refine ⟨v, hv, by omega, fun _ _ _ => rfl, ?_⟩
    simpa [astep, htest, eq] using
      (AReach.single (A := A) (oracle := oracle) (x := x)
        (a := (some (test last), v, none)) ⟨by simp [PreS, htest, hpl], hv⟩)
  | cons b w ih =>
    have room : v ptr + stride ≤ v limit := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hl
      omega
    have pne : v ptr ≠ v limit := by omega
    by_cases cz : v cap = 0
    · refine ⟨v, hv, by omega, fun _ _ _ => rfl, ?_⟩
      simp only [List.length_cons, cz, Nat.zero_bits, List.length_nil]
      apply AReach.step ⟨by simp [PreS, htest, hpl], hv⟩
      simp only [astep, htest, if_neg pne]
      simpa [astep, hcheck, cz] using
        (AReach.single (A := A) (oracle := oracle) (x := x)
          (a := (some check, v, none)) ⟨by simp [PreS, hcheck], hv⟩)
    · let halfv := Function.update v cap (v cap / 2)
      let next := Function.update halfv ptr (v ptr + stride)
      have bh : ∀ r, halfv r ≤ B := register_update_le v cap B _ hv
        ((Nat.div_le_self _ _).trans (hv cap))
      have bn : ∀ r, next r ≤ B := register_update_le halfv ptr B _ bh (room.trans (hv limit))
      have np : next ptr = v ptr + stride := by simp [next]
      have nc : next cap = v cap / 2 := by simp [next, halfv, hpc.symm]
      have nl : next limit = v limit := by simp [next, halfv, hpl.symm, hcl.symm]
      have nh : next limit = next ptr + stride * w.length := by
        rw [nl, np]; simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hl; omega
      have no : ∀ i < w.length,
          oracle j (pairEncode x (Nat.bits (next ptr + stride * i))) = w.getD i false := by
        intro i hi
        have q := ho (i + 1) (by simp; omega)
        simpa only [np, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
          Nat.add_comm stride (stride * i), List.getD_cons_succ] using q
      obtain ⟨v', bv, vp, frame, run⟩ := ih b next bn nh no
      have width : (b :: w).length ≤ (Nat.bits (v cap)).length ↔
          w.length ≤ (Nat.bits (next cap)).length := by
        rw [nc]
        have wd := access_width_half (v cap) cz
        simp only [List.length_cons]
        omega
      refine ⟨v', bv, by rwa [nl] at vp, ?_, ?_⟩
      · intro r hr hc
        rw [frame r hr hc]
        simp [next, halfv, Function.update_of_ne, hr, hc]
      · simp only [List.getLastD_cons, width]
        apply AReach.step ⟨by simp [PreS, htest, hpl], hv⟩
        simp only [astep, htest, if_neg pne]
        apply AReach.step ⟨by simp [PreS, hcheck], hv⟩
        simp only [astep, hcheck, if_neg cz]
        have bit := ho 0 (by simp)
        simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at bit
        apply AReach.step ⟨by simp [PreS, hread], hv⟩
        simp only [astep, hread, vword_whole₁, bit]
        have hb : (if b = true then halve true else halve false) = halve b := by cases b <;> rfl
        rw [hb]
        apply AReach.step ⟨by simp [PreS, hhalve], hv⟩
        simp only [astep, hhalve]
        have inc := arm_increments A oracle x ptr (advance b) stride B (hadvance b) halfv bh
          (by simp only [halfv, Function.update_of_ne hpc]; exact room.trans (hv limit))
        have ie : AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
            (some (advance b 0), halfv, none) (some (test b), next, none) := by
          simpa only [hend, halfv, Function.update_of_ne hpc] using inc
        exact ie.trans run

/-- A reverse scan decodes a previously bounded binary field. It reads only positions in
that field. The pointer, accumulator, and temporary may change; all other registers are
preserved. The caller supplies bounds for the suffix values, after its width check.

**Proof sketch.** At the boundary with `k` letters still unread, the accumulator is the
value of the suffix starting at `k`. Decrement the pointer, read letter `k-1`, copy the
accumulator into the temporary, clear the accumulator, and transfer twice the temporary
back. Add the letter and recur. The suffix-value equation bounds both the doubled value
and the final increment. Copying and scaling cite their shared ARM fragments. -/
theorem boundedDecode_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (ptr base acc tmp : Fin m)
    (hpb : ptr ≠ base) (hpa : ptr ≠ acc) (hpt : ptr ≠ tmp)
    (hba : base ≠ acc) (hbt : base ≠ tmp) (hat : acc ≠ tmp)
    (j : Fin d) (test down read done : Λ)
    (copy bump clear scale take add : Bool → Λ) (incs : Bool → ℕ → Λ)
    (htest : A test = .jeq ptr base done down)
    (hdown : A down = .dec ptr read)
    (hread : A read = .call j .whole [ptr] (copy true) (copy false))
    (hcopy : ∀ b, A (copy b) = .jeq tmp acc (clear b) (bump b))
    (hbump : ∀ b, A (bump b) = .inc tmp (copy b))
    (hclear : ∀ b, A (clear b) = .clr acc (scale b))
    (hscale : ∀ b, A (scale b) = .jz tmp (add b) (take b))
    (htake : ∀ b, A (take b) = .dec tmp (incs b 0))
    (hincs : ∀ b i, i < 2 → A (incs b i) = .inc acc (incs b (i + 1)))
    (hend : ∀ b, incs b 2 = scale b)
    (hadd : ∀ b, A (add b) = if b then .inc acc test else .jz tmp test test)
    (w : List Bool) (B : ℕ) (values : ∀ i ≤ w.length, bitsVal (w.drop i) ≤ B)
    (k : ℕ) (hk : k ≤ w.length) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (hp : v ptr = v base + k) (ha : v acc = bitsVal (w.drop k)) (ht : v tmp = 0)
    (ho : ∀ i < w.length,
      oracle j (pairEncode x (Nat.bits (v base + i))) = w.getD i false) :
    ∃ v', (∀ r, v' r ≤ B) ∧ v' ptr = v base ∧ v' acc = bitsVal w ∧ v' tmp = 0 ∧
      (∀ r, r ≠ ptr → r ≠ acc → r ≠ tmp → v' r = v r) ∧
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some test, v, none) (some done, v', none) := by
  induction k generalizing v with
  | zero =>
    have eq : v ptr = v base := by simpa using hp
    refine ⟨v, hv, eq, by simpa using ha, ht, fun _ _ _ _ => rfl, ?_⟩
    simpa [astep, htest, eq] using
      (AReach.single (A := A) (oracle := oracle) (x := x)
        (a := (some test, v, none)) ⟨by simp [PreS, htest, hpb], hv⟩)
  | succ k ih =>
    have kin : k < w.length := by omega
    let b := w.getD k false
    have val : bitsVal (w.drop k) = b.toNat + 2 * bitsVal (w.drop (k + 1)) := by
      rw [List.drop_eq_getElem_cons kin]
      simp only [bitsVal]
      congr 1
      simp [b, List.getD_eq_getElem?_getD, kin]
    have bound : 2 * v acc + b.toNat ≤ B := by
      have vb := values k (by omega)
      rw [val, ← ha] at vb
      omega
    let vd := Function.update v ptr (v base + k)
    let vc := Function.update vd tmp (v acc)
    let vz := Function.update vc acc 0
    let vs := Function.update (Function.update vz tmp 0) acc (2 * v acc)
    let vn := Function.update vs acc (bitsVal (w.drop k))
    have bd : ∀ r, vd r ≤ B := register_update_le v ptr B _ hv (by have := hv ptr; omega)
    have bc : ∀ r, vc r ≤ B := register_update_le vd tmp B _ bd (hv acc)
    have bz : ∀ r, vz r ≤ B := register_update_le vc acc B 0 bc (Nat.zero_le _)
    have bs : ∀ r, vs r ≤ B := register_update_le _ acc B _
      (register_update_le vz tmp B 0 bz (Nat.zero_le _)) (by omega)
    have bn : ∀ r, vn r ≤ B := register_update_le vs acc B _ bs (values k (by omega))
    have vb : vn base = v base := by simp [vn, vs, vz, vc, vd, hba, hbt, hpb.symm]
    have vp : vn ptr = v base + k := by simp [vn, vs, vz, vc, vd, hpa, hpt]
    have va : vn acc = bitsVal (w.drop k) := by simp [vn]
    have vt : vn tmp = 0 := by simp [vn, vs, hat.symm]
    have vf : ∀ r, r ≠ ptr → r ≠ acc → r ≠ tmp → vn r = v r := by
      intro r hr hp ht
      simp [vn, vs, vz, vc, vd, Function.update_of_ne, hr, hp, ht]
    obtain ⟨v', bv, ep, ea, et, frame, rest⟩ := ih (by omega) vn bn
      (by rw [vp, vb]) va vt (by simpa only [vb] using ho)
    refine ⟨v', bv, by simpa only [vb] using ep, ea, et, ?_, ?_⟩
    · intro r hr hp ht
      exact (frame r hr hp ht).trans (vf r hr hp ht)
    · have ne : v ptr ≠ v base := by omega
      apply AReach.step ⟨by simp [PreS, htest, hpb], hv⟩
      simp only [astep, htest, if_neg ne]
      apply AReach.step ⟨by simp [PreS, hdown], hv⟩
      have pred : v ptr - 1 = v base + k := by omega
      simp only [astep, hdown, pred]
      change AReach A oracle x _ (some read, vd, none) _
      apply AReach.step ⟨by simp [PreS, hread], bd⟩
      have bit : oracle j (pairEncode x (Nat.bits (vd ptr))) = b := by
        simpa only [vd, Function.update_self] using ho k kin
      simp only [astep, hread, vword_whole₁, bit]
      have cb : (if b = true then copy true else copy false) = copy b := by cases b <;> rfl
      rw [cb]
      have cr := registerCopy_loop A oracle x tmp acc hat.symm (copy b) (bump b) (clear b)
        (hcopy b) (hbump b) B vd bd (by simp [vd, hpt.symm, hpa.symm, ht])
      have ca : vd acc = v acc := by simp [vd, hpa.symm]
      simp only [ca] at cr
      apply cr.trans
      change AReach A oracle x _ (some (clear b), vc, none) _
      apply AReach.step ⟨by simp [PreS, hclear], bc⟩
      simp only [astep, hclear]
      change AReach A oracle x _ (some (scale b), vz, none) _
      have za : vz acc = 0 := by simp [vz]
      have zt : vz tmp = v acc := by simp [vz, vc, hat.symm]
      have sr := registerScale_loop A oracle x tmp acc hat.symm (scale b) (take b) (add b)
        (incs b) 2 (hscale b) (htake b) (hincs b) (hend b) B vz bz
        (by rw [za, zt]; omega)
      simp only [za, zt, Nat.zero_add] at sr
      apply sr.trans
      change AReach A oracle x _ (some (add b), vs, none) _
      apply AReach.step ⟨by cases b <;> simp [PreS, hadd], bs⟩
      have nb : astep A oracle x (some (add b), vs, none) = (some test, vn, none) := by
        have sv : vs acc = 2 * v acc := by simp [vs]
        have kv : bitsVal (w.drop k) = b.toNat + 2 * v acc := by rw [val, ← ha]
        cases hb : b
        · have same : vn = vs := by
            simp only [vn, kv, hb, Bool.toNat_false, Nat.zero_add, ← sv, Function.update_eq_self]
          simp [astep, hadd, same]
        · simp only [astep, hadd, ↓reduceIte]
          simp only [vn, kv, hb, Bool.toNat_true, sv, Nat.add_comm]
      rw [nb]
      exact rest

/-- A bounded strided lookup walks a segment until its running index equals the query or
its physical pointer reaches the end. The hit pointer and index are exact; a miss advances
both to the segment end. This allows one query to pass through several disjoint segments.

**Proof sketch.** Induct on the number of remaining letters. The end test handles zero;
otherwise equality hits immediately, or an index increment and one strided advance reduce
the remaining length. Pointer bounds come from the end register, and index bounds from the
supplied final index. No input bit is read by this positioning fragment. -/
theorem indexedSeek_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (ptr limit idx query : Fin m)
    (hpl : ptr ≠ limit) (hpi : ptr ≠ idx) (hpq : ptr ≠ query)
    (hli : limit ≠ idx) (_hlq : limit ≠ query) (hiq : idx ≠ query)
    (test probe bump hit miss : Λ) (advance : ℕ → Λ) (stride B : ℕ) (hs : 0 < stride)
    (htest : A test = .jeq ptr limit miss probe)
    (hprobe : A probe = .jeq idx query hit bump)
    (hbump : A bump = .inc idx (advance 0))
    (hadvance : ∀ i < stride, A (advance i) = .inc ptr (advance (i + 1)))
    (hend : advance stride = test)
    (count : ℕ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v limit = v ptr + stride * count) (hb : v idx + count ≤ B)
    (hq : v idx ≤ v query) :
    if v query < v idx + count then
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some test, v, none)
        (some hit, Function.update (Function.update v ptr
          (v ptr + stride * (v query - v idx))) idx (v query), none)
    else
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some test, v, none)
        (some miss, Function.update (Function.update v ptr (v limit)) idx (v idx + count), none) := by
  induction count generalizing v with
  | zero =>
    have eq : v ptr = v limit := by simpa using hl.symm
    have ge : ¬ v query < v idx + 0 := by omega
    have up : Function.update v ptr (v limit) = v := by rw [← eq, Function.update_eq_self]
    simp only [Nat.add_zero]
    rw [if_neg (Nat.not_lt.mpr hq), up, Function.update_eq_self]
    simpa [astep, htest, eq] using
      (AReach.single (A := A) (oracle := oracle) (x := x)
        (a := (some test, v, none)) ⟨by simp [PreS, htest, hpl], hv⟩)
  | succ count ih =>
    have room : v ptr + stride ≤ v limit := by rw [Nat.mul_succ] at hl; omega
    have ne : v ptr ≠ v limit := by omega
    by_cases eq : v idx = v query
    · have lt : v query < v idx + (count + 1) := by omega
      have endv : Function.update (Function.update v ptr
          (v ptr + stride * (v query - v idx))) idx (v query) = v := by
        simp only [← eq, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Function.update_eq_self]
      simp only [if_pos lt, endv]
      apply AReach.step ⟨by simp [PreS, htest, hpl], hv⟩
      simp only [astep, htest, if_neg ne]
      simpa [astep, hprobe, eq] using
        (AReach.single (A := A) (oracle := oracle) (x := x)
          (a := (some probe, v, none)) ⟨by simp [PreS, hprobe, hiq], hv⟩)
    · let vi := Function.update v idx (v idx + 1)
      let next := Function.update vi ptr (v ptr + stride)
      have bi : ∀ r, vi r ≤ B := register_update_le v idx B _ hv (by omega)
      have bn : ∀ r, next r ≤ B := register_update_le vi ptr B _ bi (room.trans (hv limit))
      have np : next ptr = v ptr + stride := by simp [next]
      have ni : next idx = v idx + 1 := by simp [next, vi, hpi.symm]
      have nq : next query = v query := by simp [next, vi, hpq.symm, hiq.symm]
      have nl : next limit = v limit := by simp [next, vi, hpl.symm, hli]
      have lead : AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
          (some test, v, none) (some test, next, none) := by
        apply AReach.step ⟨by simp [PreS, htest, hpl], hv⟩
        simp only [astep, htest, if_neg ne]
        apply AReach.step ⟨by simp [PreS, hprobe, hiq], hv⟩
        simp only [astep, hprobe, if_neg eq]
        apply AReach.step ⟨by simp [PreS, hbump], hv⟩
        simp only [astep, hbump]
        have run := arm_increments A oracle x ptr advance stride B hadvance vi bi
          (by simp only [vi, Function.update_of_ne hpi]; exact room.trans (hv limit))
        simpa only [hend, vi, Function.update_of_ne hpi] using run
      have rest := ih next bn (by rw [np, nl]; rw [Nat.mul_succ] at hl; omega)
        (by rw [ni]; omega) (by rw [ni, nq]; omega)
      by_cases lt : v query < v idx + (count + 1)
      · have lt' : next query < next idx + count := by rw [nq, ni]; omega
        rw [if_pos lt, if_pos lt'] at *
        have endpoint : Function.update (Function.update next ptr
            (next ptr + stride * (next query - next idx))) idx (next query) =
            Function.update (Function.update v ptr
              (v ptr + stride * (v query - v idx))) idx (v query) := by
          have diff : v query - v idx = (v query - (v idx + 1)) + 1 := by omega
          have addr : next ptr + stride * (next query - next idx) =
              v ptr + stride * (v query - v idx) := by
            rw [np, nq, ni, diff, Nat.mul_add, Nat.mul_one]; omega
          rw [addr, nq]
          funext r
          by_cases ri : r = idx
          · subst r; simp
          · by_cases rp : r = ptr
            · subst r; simp [hpi]
            · simp [next, vi, Function.update_of_ne, ri, rp]
        rw [endpoint] at rest
        exact lead.trans rest
      · have lt' : ¬ next query < next idx + count := by rw [nq, ni]; omega
        rw [if_neg lt, if_neg lt'] at *
        have endpoint : Function.update (Function.update next ptr (next limit)) idx
            (next idx + count) = Function.update (Function.update v ptr (v limit)) idx
            (v idx + (count + 1)) := by
          rw [nl, ni, Nat.add_assoc]
          funext r
          by_cases ri : r = idx
          · subst r; simp [Nat.add_comm 1 count]
          · by_cases rp : r = ptr
            · subst r; simp [hpi]
            · simp [next, vi, Function.update_of_ne, ri, rp]
        rw [endpoint] at rest
        exact lead.trans rest

/-- Continuations of the input-access decider. The mode is a parameter of the one table:
`true` asks for length, and `false` asks for the bit. -/
private inductive AccessLabel where
  | scan | second (b : Bool) | tail (eq : Bool) (last : Option Bool)
  | data (eq : Bool) | dataSecond (eq b : Bool)
  deriving DecidableEq, Fintype

/-- The decider uses register 0 for the scan position, 1 for the received reader's empty
scratch, 2 for the candidate index, and 3 for twice that index. Only the candidate's head
moves while comparing the tail; the tail itself is never copied. -/
private inductive AccessState where
  | read (l : AccessLabel) (ph : RdPh)
  | got (l : AccessLabel) (a : Option Bool)
  | inc (r : Fin 4) (l : AccessLabel) (back : Bool)
  | restore (eq : Option Bool)
  | clear (eq : Option Bool) (back : Bool)
  | bump (back : Bool)
  | answer (b : Bool)
  deriving DecidableEq, Fintype

/-- Select the scanning pointer or the data pointer. Neither aliases the reader scratch. -/
private def accessReg : AccessLabel → Fin 4
  | .data _ | .dataSecond _ _ => 3
  | _ => 0

/-- One call-free table for the two identity query languages. All input reads use the
received reader; increments, clearing and the backward head scan use received actions.
The ARM has no general-input read instruction, so it cannot express this base decider.
After the aligned scan, compare the input tail with the candidate in place, recording only
an equality bit and its final symbol. Return the candidate head, clear the scan pointer,
then inspect the candidate's doubled input cells. -/
private def accessExit : Option Bool → AccessState
  | none => .answer false
  | some eq => .read (.data eq) .eC

/-- The concrete transition table for the mode-parametrized program. -/
private def accessTr (mode : Bool) :
    AccessState → Option Bool → (Fin 4 → Option Bool) → Action 4 Bool AccessState
  | .read l ph, a, w => readTr (accessReg l) 1 (.read l) (.got l) ph a w
  | .got .scan a, _, _ => match a with
    | none => xAct 2 0 (-1) (.restore none)
    | some b => goAct (.inc 0 (.second b) false)
  | .got (.second b) a, _, _ => match a with
    | none => xAct 2 0 (-1) (.restore none)
    | some b' => if b = b' then goAct (.inc 0 .scan false)
      else if b = false then goAct (.inc 0 (.tail true none) false)
      else xAct 2 0 (-1) (.restore none)
  | .got (.tail eq last) a, _, w => match a with
    | none => xAct 2 0 (-1) (.restore (if last = some false then none
      else some (eq && decide (w 2 = none))))
    | some b => xAct 2 0 (if w 2 = none then 0 else 1)
        (.inc 0 (.tail (eq && decide (w 2 = some b)) (some b)) false)
  | .got (.data eq) a, _, _ => match a with
    | none => goAct (.answer false)
    | some b => goAct (.inc 3 (.dataSecond eq b) false)
  | .got (.dataSecond eq b) a, _, _ => match a with
    | none => goAct (.answer false)
    | some b' => if b = b' then
        if eq then goAct (.answer (mode || b)) else goAct (.bump false)
      else goAct (.answer false)
  | .inc r l false, _, w => incCAct r (.inc r l false) (.inc r l true) (w r)
  | .inc r l true, _, w => incBAct r (.inc r l true) (.read l .eC) (w r)
  | .restore eq, _, w => backAct 2 (.restore eq) (.clear eq false) (w 2)
  | .clear eq false, _, w => toEndAct 0 (.clear eq false) (.clear eq true) (w 0)
  | .clear eq true, _, w => clrEAct 0 (.clear eq true) (accessExit eq) (w 0)
  | .bump false, _, w => incCAct 2 (.bump false) (.bump true) (w 2)
  | .bump true, _, w => incBAct 2 (.bump true) (.inc 3 .scan false) (w 2)
  | .answer b, _, _ => retAct b

/-- The input-access table has no calls and starts with the aligned scan. -/
private def accessProg (mode : Bool) : RProg 4 0 AccessState :=
  ⟨⟨.read .scan .eC, accessTr mode⟩, fun _ => none⟩

/-- Boundary configurations; `q` is the streamed comparison head on the candidate. -/
private def accessCfg {y : List Bool} (st : AccessState) (i k p : ℕ) (q : ℤ := 0) :
    Cfg 4 Bool AccessState y :=
  ⟨some st, ⟨1, by omega⟩,
    fun r => FinTM.bufferTape (Nat.bits (![i, 0, k, p] r)),
    Function.update (fun _ => 0) 2 q, []⟩

/-- The common head interval, including both boundary cells. -/
private def accessSafe {y : List Bool} (c : Cfg 4 Bool AccessState y) : Prop :=
  ∀ r, -1 ≤ c.workTapePos r ∧ c.workTapePos r ≤ (Nat.bits (y.length + 1)).length

/-- Bounded paths use the existing reflexive-transitive closure and its composition. -/
private abbrev AccessPath (mode : Bool) {y : List Bool} :=
  Relation.ReflTransGen (fun c c' : Cfg 4 Bool AccessState y =>
    accessSafe c ∧ c' = rstep (accessProg mode) Dbl.o c)

/-- A bounded path has an ordinary run witness. Proof sketch: induction on the closure;
append its last single step and separate the last time from earlier times. -/
private lemma accessPath_run {mode : Bool} {y : List Bool}
    {c c' : Cfg 4 Bool AccessState y} (h : AccessPath mode c c') :
    ∃ T, rrun (accessProg mode) Dbl.o c T = c' ∧
      ∀ t < T, accessSafe (rrun (accessProg mode) Dbl.o c t) := by
  induction h with
  | refl => exact ⟨0, rfl, by omega⟩
  | @tail d e _ hstep ih =>
    obtain ⟨n, hn, hb⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · rw [rrun_succ, hn]; exact hstep.2.symm
    · intro t ht
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h | rfl
      · exact hb t h
      · rw [hn]; exact hstep.1

/-- A bounded finite run gives a path, allowing received fragments to use the common
closure without re-proving its composition law. -/
private lemma accessPath_of_run {mode : Bool} {y : List Bool}
    (c : Cfg 4 Bool AccessState y) (T : ℕ)
    (h : ∀ t < T, accessSafe (rrun (accessProg mode) Dbl.o c t)) :
    AccessPath mode c (rrun (accessProg mode) Dbl.o c T) := by
  induction T with
  | zero => exact .refl
  | succ T ih =>
    rw [rrun_succ]
    exact (ih (fun t ht => h t (by omega))).tail ⟨h T (by omega), rfl⟩

/-- A comparison boundary is bounded exactly when its one moving head is bounded. -/
private lemma accessCfg_safe {y : List Bool} (st : AccessState) (i k p : ℕ) (q : ℤ)
    (hlo : -1 ≤ q) (hhi : q ≤ (Nat.bits (y.length + 1)).length) :
    accessSafe (accessCfg (y := y) st i k p q) := by
  intro r
  by_cases h : r = 2
  · subst r; simpa [accessCfg] using And.intro hlo hhi
  · simp [accessCfg, Function.update_of_ne h]

/-- The received reader preserves all data, including the streamed candidate head.
Proof sketch: instantiate `readIn_run` on the selected pointer and register 1. Its frame
changes only those two heads; the candidate head keeps its previously established bound. -/
private lemma access_read (mode : Bool) {y : List Bool} (l : AccessLabel)
    (i k p : ℕ) (q : ℤ) (hlo : -1 ≤ q)
    (hhi : q ≤ (Nat.bits (y.length + 1)).length) :
    AccessPath mode (accessCfg (y := y) (.read l .eC) i k p q)
      (accessCfg (.got l y[![i, 0, k, p] (accessReg l)]?) i k p q) := by
  have hr : accessReg l ≠ (1 : Fin 4) := by cases l <;> simp [accessReg]
  have hr2 : accessReg l ≠ (2 : Fin 4) := by cases l <;> simp [accessReg]
  obtain ⟨T, he, hm⟩ := readIn_run (accessProg mode) Dbl.o (accessReg l) 1 hr
    (.read l) (.got l) (fun _ _ _ => rfl) (fun _ => rfl)
    (accessCfg (y := y) (.read l .eC) i k p q)
    (![i, 0, k, p] (accessReg l)) rfl (by simp [accessCfg])
    (by simp [accessCfg, Function.update_of_ne hr2]) (by simp [accessCfg]) rfl
  change rrun (accessProg mode) Dbl.o (accessCfg (.read l .eC) i k p q) T =
    accessCfg (.got l y[![i, 0, k, p] (accessReg l)]?) i k p q at he
  rw [← he]
  apply accessPath_of_run
  intro t ht
  obtain ⟨ph, ip, f, a, b, hc, ha, ha', hb, hb'⟩ := hm t ht
  change rrun (accessProg mode) Dbl.o (accessCfg (.read l .eC) i k p q) t = _ at hc
  rw [hc]
  intro r
  by_cases h1 : r = accessReg l
  · subst r; simpa using And.intro hb hb'
  · by_cases h2 : r = 1
    · subst r; simpa [Function.update_of_ne h1] using And.intro ha ha'
    · simpa [Function.update_of_ne h1, Function.update_of_ne h2] using
        accessCfg_safe (.read l .eC) i k p q hlo hhi r

/-- A frame changing one head preserves the common bound. -/
private lemma access_frame {y : List Bool} (c : Cfg 4 Bool AccessState y)
    (hc : accessSafe c) (st : AccessState) (r : Fin 4) (f : ℤ → Option Bool) (q : ℤ)
    (hq : -1 ≤ q ∧ q ≤ (Nat.bits (y.length + 1)).length) :
    accessSafe (regCfg c st r f q) := by
  intro j
  simp only [regCfg, Function.update_apply]
  split_ifs with h
  · exact hq
  · exact hc j

/-- Invoke the received increment, without re-walking its carry or return. -/
private lemma access_inc (mode : Bool) {y : List Bool} (r : Fin 4) (l : AccessLabel)
    (c : Cfg 4 Bool AccessState y) (n : ℕ) (hc : accessSafe c) (hn : n + 1 ≤ y.length + 1) :
    AccessPath mode (regCfg c (.inc r l false) r (FinTM.bufferTape (Nat.bits n)) 0)
      (regCfg c (.read l .eC) r (FinTM.bufferTape (Nat.bits (n + 1))) 0) := by
  obtain ⟨T, he, hm⟩ := inc_run (accessProg mode) Dbl.o r (.inc r l false) (.inc r l true)
    (.read l .eC) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl c n
  rw [← he]
  apply accessPath_of_run
  intro t ht
  obtain ⟨st, f, q, heq, _, hlo, hhi⟩ := hm t ht
  rw [heq]
  exact access_frame c hc st r f q ⟨hlo, hhi.trans (by exact_mod_cast length_bits_mono hn)⟩

/-- Invoke the received clear after returning the comparison head. -/
private lemma access_clear (mode : Bool) {y : List Bool} (eq : Option Bool)
    (c : Cfg 4 Bool AccessState y) (n : ℕ) (hc : accessSafe c) (hn : n ≤ y.length + 1) :
    AccessPath mode (regCfg c (.clear eq false) 0 (FinTM.bufferTape (Nat.bits n)) 0)
      (regCfg c (accessExit eq) 0 (FinTM.bufferTape []) 0) := by
  obtain ⟨T, he, hm⟩ := clr_run (accessProg mode) Dbl.o 0 (.clear eq false) (.clear eq true)
    (accessExit eq) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl c n
  rw [Nat.zero_bits] at he
  rw [← he]
  apply accessPath_of_run
  intro t ht
  obtain ⟨st, f, q, heq, _, hlo, hhi⟩ := hm t ht
  rw [heq]
  exact access_frame c hc st 0 f q ⟨hlo, hhi.trans (by exact_mod_cast length_bits_mono hn)⟩

/-- An ordinary control step, recorded in the shared bounded closure. -/
private lemma access_step (mode : Bool) {y : List Bool} (c : Cfg 4 Bool AccessState y)
    (st : AccessState) (hs : c.state = some st) (hc : accessSafe c) :
    AccessPath mode c ((accessTr mode st c.inputSymbol c.workTapeSymbols).apply c) := by
  apply Relation.ReflTransGen.single
  refine ⟨hc, ?_⟩
  rw [rstep_noncall (accessProg mode) Dbl.o c st hs rfl]
  simp only [MultiTapeTM.step, hs, accessProg]

/-- Normalize an increment on a scan or data pointer. -/
private lemma access_inc_pointer (mode : Bool) {y : List Bool} (r : Fin 4)
    (hr : r = 0 ∨ r = 3) (l : AccessLabel) (i k p : ℕ) (q : ℤ)
    (hlo : -1 ≤ q) (hhi : q ≤ (Nat.bits (y.length + 1)).length)
    (hn : ![i, 0, k, p] r + 1 ≤ y.length + 1) :
    AccessPath mode (accessCfg (y := y) (.inc r l false) i k p q)
      (accessCfg (.read l .eC) (if r = 0 then i + 1 else i) k
        (if r = 3 then p + 1 else p) q) := by
  have h := access_inc mode r l (accessCfg (y := y) (.inc r l false) i k p q)
    (![i, 0, k, p] r) (accessCfg_safe _ _ _ _ _ hlo hhi) hn
  rcases hr with rfl | rfl
  all_goals
    convert h using 1 <;>
      apply Cfg.ext <;> try rfl
    all_goals
      funext j
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [regCfg, accessCfg]

/-- Return the candidate head and clear the scan pointer. Proof sketch: `regBack_x`
returns from one cell before the comparison frontier; `clr_run` then clears register 0.
Neither fragment changes the candidate or data pointer. -/
private lemma access_return (mode : Bool) {y : List Bool} (eq : Option Bool)
    (i k p q : ℕ) (hi : i ≤ y.length + 1) (hk : k ≤ y.length + 1)
    (hq : q ≤ (Nat.bits k).length) :
    AccessPath mode (accessCfg (y := y) (.restore eq) i k p ((q : ℤ) - 1))
      (accessCfg (accessExit eq) 0 k p) := by
  let c := accessCfg (y := y) (.restore eq) i k p
  have hback := regBack_x (accessProg mode) Dbl.o c 2 (Nat.bits k)
    (by simp [c, accessCfg]) (.restore eq) (.clear eq false)
    (fun _ w => by simp only [accessProg, accessTr, backAct]) rfl
    ⟨1, by omega⟩ q ((q : ℤ) - 1) (by omega) (by omega)
  have hview (st : AccessState) (a : ℤ) : xCfg c st ⟨1, by omega⟩ 2 a =
      accessCfg st i k p a := by
    simp [xCfg, accessCfg, c]
  simp only [hview] at hback
  have h₁ : AccessPath mode (accessCfg (y := y) (.restore eq) i k p ((q : ℤ) - 1))
      (accessCfg (.clear eq false) i k p) := by
    rw [← hback.1]
    apply accessPath_of_run
    intro t ht
    obtain ⟨q', he, h1, h2⟩ := hback.2 t ht
    rw [he]
    apply accessCfg_safe _ _ _ _ _ h1
    have hb := length_bits_mono hk
    omega
  apply h₁.trans
  have hclear := access_clear mode eq (accessCfg (y := y) (.clear eq false) i k p)
    i (accessCfg_safe _ _ _ _ 0 (by omega) (by omega)) hi
  convert hclear using 1 <;> apply Cfg.ext <;> try rfl
  all_goals
    funext j
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [regCfg, accessCfg]

/-- Pure streamed tail check. `wr` is the unvisited part of the candidate; it is a
proof parameter, never stored as another word by the machine. -/
private def accessTail : List Bool → List Bool → Bool → Option Bool → Option Bool
  | [], wr, eq, last => if last = some false then none else some (eq && decide (wr = []))
  | b :: bs, wr, eq, _ =>
    accessTail bs wr.tail (eq && decide (wr.head? = some b)) (some b)

/-- The tail check enforces its final symbol and exact equality, including empty words. -/
private lemma accessTail_eq (wi wr : List Bool) (eq : Bool) (last : Option Bool) :
    accessTail wi wr eq last =
      if wi.getLast?.or last = some false then none else some (eq && decide (wr = wi)) := by
  induction wi generalizing wr eq last with
  | nil => simp [accessTail]
  | cons b wi ih =>
    rw [accessTail, ih]
    cases wi <;> cases wr <;> simp [List.getLast?_cons, Bool.and_assoc]

/-- An entire tail beginning with no previous symbol is canonical exactly when the
streamed check succeeds. -/
private lemma accessTail_canonical (wi wr : List Bool) (eq : Bool) :
    accessTail wi wr eq none = if Canon wi then some (eq && decide (wi = wr)) else none := by
  classical
  rw [accessTail_eq]
  have heq : decide (wr = wi) = decide (wi = wr) := decide_eq_decide.mpr eq_comm
  rw [heq]
  have h : wi.getLast? ≠ some false ↔ Canon wi := by
    by_cases hn : wi = []
    · subst wi; simp [Canon]
    · rw [List.getLast?_eq_some_getLast hn]
      simp only [ne_eq, Option.some.injEq]
      constructor
      · intro ha _
        exact Bool.eq_true_of_not_eq_false ha
      · intro ha
        rw [ha hn]
        decide
  by_cases hh : wi.getLast? = some false
  · have hn : ¬ Canon wi := fun hc => (h.mpr hc) hh
    simp [hh, hn]
  · simp [hh, h.mp hh]

/-- The aligned scan's mathematical result: failure, or a comparison with the canonical
index in the second field. It places no canonicality condition on the first field. -/
private noncomputable def accessCheck (y : List Bool) (k : ℕ) : Option Bool :=
  (pairDecode y).bind fun zw =>
    if Canon zw.2 then some (decide (zw.2 = Nat.bits k)) else none

/-- A genuine query passes the aligned and canonical checks, with the expected equality. -/
private lemma accessCheck_pair (z : List Bool) (r k : ℕ) :
    accessCheck (pairEncode z (Nat.bits r)) k = some (decide (r = k)) := by
  simp [accessCheck, pairDecode_pairEncode, canon_bits, bits_injective.eq_iff]

/-- Successful validation supplies the exact paired shape and a canonical tail. -/
private lemma accessCheck_some {y : List Bool} {k : ℕ} {b : Bool}
    (h : accessCheck y k = some b) :
    ∃ z r, y = pairEncode z (Nat.bits r) ∧ b = decide (r = k) := by
  classical
  unfold accessCheck at h
  cases hd : pairDecode y with
  | none => simp [hd] at h
  | some zw =>
    rcases zw with ⟨z, w⟩
    simp only [hd, Option.bind_some] at h
    split_ifs at h with hc
    · refine ⟨z, bitsVal w, ?_, ?_⟩
      · exact (eq_pairEncode_of_pairDecode _ _ _ hd).trans
          (congrArg (pairEncode z) (canon_eq_bits w hc))
      · rw [canon_eq_bits w hc] at h
        simpa only [bits_injective.eq_iff] using (Option.some.inj h).symm

/-- A control action changes no part of the boundary data. -/
private lemma access_go {y : List Bool} (st st' : AccessState) (i k p : ℕ) (q : ℤ) :
    (goAct st').apply (accessCfg (y := y) st i k p q) = accessCfg st' i k p q := by
  simp [goAct, Action.apply, accessCfg, moveInputPos_zero]

/-- Moving just the comparison head has the expected boundary form. -/
private lemma access_move {y : List Bool} (st st' : AccessState) (i k p : ℕ)
    (q : ℤ) (mv : SignType) :
    (xAct 2 0 mv st').apply (accessCfg (y := y) st i k p q) =
      accessCfg st' i k p (q + mv) := by
  have h := apply_xAct (accessCfg (y := y) st i k p) st st' ⟨1, by omega⟩ 2 q 0 mv
  simpa [xCfg, accessCfg, Function.update_idem, moveInputPos_zero] using h

/-- The candidate symbol is the current letter of its unvisited suffix. -/
private lemma access_symbol {y : List Bool} (st : AccessState) (i k p q : ℕ) :
    (accessCfg (y := y) st i k p q).workTapeSymbols 2 = ((Nat.bits k).drop q).head? := by
  simp [Cfg.workTapeSymbols, accessCfg, FinTM.bufferTape, List.head?_drop]

/-- A streamed tail finishes with its pure result, without copying or decoding its value.
Proof sketch: induction on the remaining input suffix. Each letter uses `readIn_run`,
advances the candidate head only if it sees a candidate letter, and increments the bounded
input pointer. At the right blank, check canonicality, return the head, and clear the
pointer with the received fragments. -/
private lemma access_tail_run (mode : Bool) {y : List Bool} (wi : List Bool) :
    ∀ (i k p q : ℕ) (eq : Bool) (last : Option Bool), y.drop i = wi → i ≤ y.length →
      k ≤ y.length + 1 → q ≤ (Nat.bits k).length →
      AccessPath mode (accessCfg (y := y) (.read (.tail eq last) .eC) i k p q)
        (accessCfg (accessExit (accessTail wi ((Nat.bits k).drop q) eq last)) 0 k p) := by
  induction wi with
  | nil =>
    intro i k p q eq last hy hi hk hq
    have hW := length_bits_mono hk
    have hsym : y[i]? = none := by simpa [List.head?_drop] using congrArg List.head? hy
    have hr := access_read mode (y := y) (.tail eq last) i k p q (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, hsym] at hr
    apply hr.trans
    have hs := access_step mode (accessCfg (y := y) (.got (.tail eq last) none) i k p q)
      _ rfl (accessCfg_safe _ _ _ _ _ (by omega) (by omega))
    rw [accessTr, access_symbol, access_move] at hs
    simp only [List.head?_eq_none_iff, accessTail] at hs ⊢
    exact hs.trans (access_return mode _ i k p q (by omega) hk hq)
  | cons b wi ih =>
    intro i k p q eq last hy hi hk hq
    have hlen := congrArg List.length hy
    simp only [List.length_drop, List.length_cons] at hlen
    have hi' : i + 1 ≤ y.length := by omega
    have hW := length_bits_mono hk
    have hsym : y[i]? = some b := by simpa [List.head?_drop] using congrArg List.head? hy
    let wr := (Nat.bits k).drop q
    let q' := min (q + 1) (Nat.bits k).length
    have hq' : q' ≤ (Nat.bits k).length := Nat.min_le_right _ _
    have hdrop : (Nat.bits k).drop q' = wr.tail := by
      dsimp [wr, q']
      by_cases h : q < (Nat.bits k).length
      · rw [Nat.min_eq_left (by omega), ← List.tail_drop]
      · have he : q = (Nat.bits k).length := by omega
        simp [he]
    have hmv : (q : ℤ) + ((if wr.head? = none then 0 else 1 : SignType) : ℤ) = q' := by
      dsimp [wr, q']
      by_cases h : q < (Nat.bits k).length
      · have hh : ((Nat.bits k).drop q).head? ≠ none := by simp; omega
        simp [Nat.not_le_of_lt h, Nat.min_eq_left (show q + 1 ≤ (Nat.bits k).length by omega)]
      · have he : q = (Nat.bits k).length := by omega
        simp [he]
    have hr := access_read mode (y := y) (.tail eq last) i k p q (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, hsym] at hr
    apply hr.trans
    have hs := access_step mode (accessCfg (y := y) (.got (.tail eq last) (some b)) i k p q)
      _ rfl (accessCfg_safe _ _ _ _ _ (by omega) (by omega))
    rw [accessTr, access_symbol, access_move, hmv] at hs
    apply hs.trans
    have hn := access_inc_pointer mode (y := y) 0 (Or.inl rfl)
      (.tail (eq && decide (wr.head? = some b)) (some b)) i k p q' (by omega) (by omega)
      (by simp; omega)
    simp only [↓reduceIte, Fin.isValue, show (0 : Fin 4) ≠ 3 by decide] at hn
    apply hn.trans
    have hnext : y.drop (i + 1) = wi := by rw [← List.tail_drop, hy]; rfl
    simpa only [accessTail, hdrop] using ih (i + 1) k p q'
      (eq && decide (wr.head? = some b)) (some b) hnext hi' hk hq'

/-- A format rejection returns and clears before answering, so every scan has one
normalized exit shape. -/
private lemma access_reject (mode : Bool) {y : List Bool} (st : AccessState) (i k p : ℕ)
    (hi : i ≤ y.length + 1) (hk : k ≤ y.length + 1)
    (htr : ∀ a w, accessTr mode st a w = xAct 2 0 (-1) (.restore none)) :
    AccessPath mode (accessCfg (y := y) st i k p)
      (accessCfg (.answer false) 0 k p) := by
  have hs := access_step mode (accessCfg (y := y) st i k p) st rfl
    (accessCfg_safe _ _ _ _ 0 (by omega) (by omega))
  rw [htr, access_move] at hs
  exact hs.trans (access_return mode none i k p 0 hi hk (by omega))

/-- A control-only transition between boundary configurations. -/
private lemma access_jump (mode : Bool) {y : List Bool} (st st' : AccessState)
    (i k p : ℕ) (htr : ∀ a w, accessTr mode st a w = goAct st') :
    AccessPath mode (accessCfg (y := y) st i k p) (accessCfg st' i k p) := by
  have hs := access_step mode (accessCfg (y := y) st i k p) st rfl
    (accessCfg_safe _ _ _ _ 0 (by omega) (by omega))
  rwa [htr, access_go] at hs

/-- Duplicated letters do not affect the query tail being checked. -/
private lemma accessCheck_dup (b : Bool) (wi : List Bool) (k : ℕ) :
    accessCheck (b :: b :: wi) k = accessCheck wi k := by
  classical
  cases b <;> cases h : pairDecode wi <;> simp [accessCheck, pairDecode, h]

/-- The aligned scanner validates arbitrary first fields and canonical tails.
Proof sketch: induction in steps of two letters. `00` and `11` advance; `01` enters the
streamed tail check; a short pair or `10` rejects. The position never exceeds the input
length, and no numerical value of the tail is accumulated. -/
private lemma access_scan_run (mode : Bool) {y : List Bool} (wi : List Bool) :
    ∀ (i k p : ℕ), y.drop i = wi → i ≤ y.length → k ≤ y.length + 1 →
      AccessPath mode (accessCfg (y := y) (.read .scan .eC) i k p)
        (accessCfg (accessExit (accessCheck wi k)) 0 k p) := by
  induction wi using List.twoStepInduction with
  | nil =>
    intro i k p hy hi hk
    have hs : y[i]? = none := by simpa using congrArg List.head? hy
    have hr := access_read mode (y := y) .scan i k p 0 (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, hs] at hr
    simpa [accessCheck, pairDecode, accessExit] using hr.trans
      (access_reject mode (.got .scan none) i k p (by omega) hk (fun _ _ => rfl))
  | singleton b =>
    intro i k p hy hi hk
    have hl := congrArg List.length hy
    simp only [List.length_drop, List.length_singleton] at hl
    have hs : y[i]? = some b := by simpa using congrArg List.head? hy
    have ht : y[i + 1]? = none := by
      have hh : y.drop (i + 1) = [] := by rw [← List.tail_drop, hy]; rfl
      simpa using congrArg List.head? hh
    have h₀ := access_read mode (y := y) .scan i k p 0 (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, hs] at h₀
    have h₁ := access_jump mode (y := y) (.got .scan (some b)) (.inc 0 (.second b) false)
      i k p (fun _ _ => rfl)
    have h₂ := access_inc_pointer mode (y := y) 0 (Or.inl rfl) (.second b) i k p 0
      (by omega) (by omega) (by simp; omega)
    simp at h₂
    have h₃ := access_read mode (y := y) (.second b) (i + 1) k p 0 (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, ht] at h₃
    have h₄ := access_reject mode (y := y) (.got (.second b) none) (i + 1) k p
      (by omega) hk (fun _ _ => rfl)
    simpa [accessCheck, pairDecode, accessExit] using (((h₀.trans h₁).trans h₂).trans h₃).trans h₄
  | cons_cons b b' wi ih _ =>
    intro i k p hy hi hk
    have hl := congrArg List.length hy
    simp only [List.length_drop, List.length_cons] at hl
    have hdrop₁ : y.drop (i + 1) = b' :: wi := by rw [← List.tail_drop, hy]; rfl
    have hdrop₂ : y.drop (i + 2) = wi := by
      rw [show i + 2 = (i + 1) + 1 by omega, ← List.tail_drop, hdrop₁]; rfl
    have hs : y[i]? = some b := by simpa using congrArg List.head? hy
    have ht : y[i + 1]? = some b' := by simpa using congrArg List.head? hdrop₁
    have h₀ := access_read mode (y := y) .scan i k p 0 (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, hs] at h₀
    have h₁ := access_jump mode (y := y) (.got .scan (some b)) (.inc 0 (.second b) false)
      i k p (fun _ _ => rfl)
    have h₂ := access_inc_pointer mode (y := y) 0 (Or.inl rfl) (.second b) i k p 0
      (by omega) (by omega) (by simp; omega)
    simp at h₂
    have h₃ := access_read mode (y := y) (.second b) (i + 1) k p 0 (by omega) (by omega)
    simp only [accessReg, Matrix.cons_val_zero, ht] at h₃
    apply (((h₀.trans h₁).trans h₂).trans h₃).trans
    by_cases heq : b = b'
    · subst b'
      have h₄ := access_jump mode (y := y) (.got (.second b) (some b)) (.inc 0 .scan false)
        (i + 1) k p (fun _ _ => by simp [accessTr])
      have h₅ := access_inc_pointer mode (y := y) 0 (Or.inl rfl) .scan (i + 1) k p 0
        (by omega) (by omega) (by simp; omega)
      simp only [↓reduceIte, Fin.isValue, show (0 : Fin 4) ≠ 3 by decide] at h₅
      rw [accessCheck_dup]
      exact (h₄.trans h₅).trans (ih (i + 2) k p hdrop₂ (by omega) hk)
    · cases b <;> cases b'
      · exact False.elim (heq rfl)
      · have h₄ := access_jump mode (y := y) (.got (.second false) (some true))
          (.inc 0 (.tail true none) false) (i + 1) k p (fun _ _ => rfl)
        have h₅ := access_inc_pointer mode (y := y) 0 (Or.inl rfl) (.tail true none)
          (i + 1) k p 0 (by omega) (by omega) (by simp; omega)
        simp at h₅
        apply (h₄.trans h₅).trans
        simpa [accessCheck, pairDecode, accessTail_canonical] using
          access_tail_run mode wi (i + 2) k p 0 true none hdrop₂ (by omega) hk (by omega)
      · simpa [accessCheck, pairDecode, accessExit] using
          access_reject mode (y := y) (.got (.second true) (some false)) (i + 1) k p
            (by omega) hk (fun _ _ => rfl)
      · exact False.elim (heq rfl)

/-- Advance the bounded candidate and doubled data pointer for the next round. -/
private lemma access_bump (mode : Bool) {y : List Bool} (k p : ℕ)
    (hk : k + 1 ≤ y.length + 1) (hp : p + 1 ≤ y.length + 1) :
    AccessPath mode (accessCfg (y := y) (.bump false) 0 k p)
      (accessCfg (.read .scan .eC) 0 (k + 1) (p + 1)) := by
  let c := accessCfg (y := y) (.bump false) 0 k p
  have hv (st : AccessState) (n : ℕ) :
      regCfg c st 2 (FinTM.bufferTape (Nat.bits n)) 0 = accessCfg st 0 n p := by
    apply Cfg.ext <;> try rfl
    all_goals funext j; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [regCfg, accessCfg, c]
  obtain ⟨T, he, hm⟩ := inc_run (accessProg mode) Dbl.o 2 (.bump false) (.bump true)
    (.inc 3 .scan false) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl c k
  rw [hv, hv] at he
  have h₁ : AccessPath mode c (accessCfg (.inc 3 .scan false) 0 (k + 1) p) := by
    rw [← he]
    apply accessPath_of_run
    intro t ht
    obtain ⟨st, f, q, hq, _, hlo, hhi⟩ := hm t ht
    rw [hv] at hq
    rw [hq]
    exact access_frame c (accessCfg_safe _ _ _ _ 0 (by omega) (by omega)) _ _ _ _
      ⟨hlo, hhi.trans (by exact_mod_cast length_bits_mono hk)⟩
  have h₂ := access_inc_pointer mode (y := y) 3 (Or.inr rfl) .scan 0 (k + 1) p 0
    (by omega) (by omega) (by simpa using hp)
  simpa using h₁.trans h₂

/-- The mode's answer on a genuine query. -/
private def accessValue (mode : Bool) (z : List Bool) (r : ℕ) : Bool :=
  if mode then decide (r < z.length) else z.getD r false

/-- A completed answer has exactly the one output bit; all heads are at the origin. -/
private def accessDone {y : List Bool} (b : Bool) (k p : ℕ) : Cfg 4 Bool AccessState y :=
  { accessCfg (.answer b) 0 k p with state := none, output := [b] }

/-- The final output action is bounded. -/
private lemma access_answer (mode b : Bool) {y : List Bool} (k p : ℕ) :
    AccessPath mode (accessCfg (y := y) (.answer b) 0 k p) (accessDone b k p) := by
  have hs := access_step mode (accessCfg (y := y) (.answer b) 0 k p) _ rfl
    (accessCfg_safe _ _ _ _ 0 (by omega) (by omega))
  simpa [accessTr, retAct, Action.apply, accessCfg, accessDone, moveInputPos_zero] using hs

/-- Read the candidate's two doubled cells, stopping at the separator.
Proof sketch: both cells of a genuine data pair agree by `getElem?_dbl`; the separator
has the distinct letters `false,true`. Two applications of the reader and one increment
therefore select the answer or the next-candidate branch exactly. -/
private lemma access_data_run (mode eq : Bool) (z w : List Bool) (k : ℕ) (hk : k ≤ z.length) :
    AccessPath mode
      (accessCfg (y := pairEncode z w) (.read (.data eq) .eC) 0 k (2 * k))
      (accessCfg (if h : k < z.length then
        if eq then .answer (mode || z[k]) else .bump false else .answer false)
        0 k (2 * k + 1)) := by
  have hlen := length_pairEncode z w
  have hpair (j : Bool) : (pairEncode z w)[2 * k + j.toNat]? =
      some (if h : k < z.length then z[k] else j) := by
    rw [pairEncode_eq_dbl, List.append_assoc]
    by_cases h : k < z.length
    · rw [List.getElem?_append_left (by simp only [length_dbl]; cases j <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega), getElem?_dbl _ _ h]
      simp [h]
    · have he : k = z.length := by omega
      subst k
      rw [List.getElem?_append_right (by simp)]
      cases j <;> simp
  have h₀ := access_read mode (y := pairEncode z w) (.data eq) 0 k (2 * k) 0
    (by omega) (by omega)
  simp only [accessReg, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h₀
  have hfirst := hpair false
  simp only [Bool.toNat_false, Nat.add_zero] at hfirst
  rw [hfirst] at h₀
  have h₁ := access_jump mode (y := pairEncode z w)
    (.got (.data eq) (some (if h : k < z.length then z[k] else false)))
    (.inc 3 (.dataSecond eq (if h : k < z.length then z[k] else false)) false)
    0 k (2 * k) (fun _ _ => rfl)
  have h₂ := access_inc_pointer mode (y := pairEncode z w) 3 (Or.inr rfl)
    (.dataSecond eq (if h : k < z.length then z[k] else false)) 0 k (2 * k) 0
    (by omega) (by omega) (by simp; omega)
  simp at h₂
  have h₃ := access_read mode (y := pairEncode z w)
    (.dataSecond eq (if h : k < z.length then z[k] else false)) 0 k (2 * k + 1) 0
    (by omega) (by omega)
  simp only [accessReg, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h₃
  have hsecond := hpair true
  simp only [Bool.toNat_true] at hsecond
  rw [hsecond] at h₃
  apply (((h₀.trans h₁).trans h₂).trans h₃).trans
  apply access_jump
  intro a ww
  by_cases h : k < z.length <;> cases eq <;> simp [accessTr, h]

/-- On a genuine query, successive bounded candidates reach exactly its bit or length
answer. Proof sketch: induction on the number of remaining first-field cells. The aligned
scanner either matches the queried index or advances to the next candidate. At the
separator all remaining indices are out of range, so both modes return false. -/
private lemma access_valid (mode : Bool) (z : List Bool) (r : ℕ) :
    ∀ k, k ≤ z.length → k ≤ r →
      ∃ k' p', AccessPath mode
        (accessCfg (y := pairEncode z (Nat.bits r)) (.read .scan .eC) 0 k (2 * k))
        (accessDone (accessValue mode z r) k' p') := by
  intro k
  generalize hN : z.length - k = N
  induction N using Nat.strong_induction_on generalizing k with
  | h N ih =>
    intro hk hr
    have hl := length_pairEncode z (Nat.bits r)
    have hscan := access_scan_run mode (y := pairEncode z (Nat.bits r))
      (pairEncode z (Nat.bits r)) 0 k (2 * k) (by simp) (by omega) (by omega)
    rw [accessCheck_pair] at hscan
    have hdata := access_data_run mode (decide (r = k)) z (Nat.bits r) k hk
    have hround := hscan.trans hdata
    by_cases hk' : k < z.length
    · by_cases he : r = k
      · subst r
        simp only [hk', ↓reduceDIte, decide_true, ↓reduceIte] at hround
        refine ⟨k, 2 * k + 1, ?_⟩
        have hans : accessValue mode z k = (mode || z[k]) := by
          cases mode <;> simp [accessValue, hk', List.getD_eq_getElem?_getD]
        rw [hans]
        exact hround.trans (access_answer mode _ _ _)
      · simp only [hk', ↓reduceDIte, he, decide_false, Bool.false_eq_true, ↓reduceIte] at hround
        have hbump := access_bump mode (y := pairEncode z (Nat.bits r)) k (2 * k + 1)
          (by omega) (by omega)
        obtain ⟨k', p', hnext⟩ := ih (z.length - (k + 1)) (by omega) (k + 1) rfl
          (by omega) (by omega)
        refine ⟨k', p', (hround.trans hbump).trans ?_⟩
        convert hnext using 1
    · simp only [hk', ↓reduceDIte] at hround
      have hans : accessValue mode z r = false := by
        have hrr : z.length ≤ r := by omega
        cases mode <;> simp [accessValue, Nat.not_lt.mpr hrr, List.getD_eq_getElem?_getD]
      refine ⟨k, 2 * k + 1, ?_⟩
      rw [hans]
      exact hround.trans (access_answer mode false _ _)

/-- The single mode-parametrized language decided by the access program. -/
private def accessLang (mode : Bool) : Language Bool :=
  indexLang fun z r => accessValue mode z r = true

/-- The call-free program halts correctly on every input, including malformed queries.
Proof sketch: a canonical pair uses the bounded candidate loop. All other words fail the
aligned or canonical check at the first round. The indicator identity supplies the common
answer in both cases. -/
private lemma access_run (mode : Bool) (y : List Bool) :
    ∃ k p, AccessPath mode (Cfg.init (.read .scan .eC) y)
      (accessDone (MultiTapeTM.indicator (accessLang mode : Set (List Bool)) y) k p) := by
  classical
  have hinit : Cfg.init (.read .scan .eC) y = accessCfg (y := y) (.read .scan .eC) 0 0 0 := by
    apply Cfg.ext <;> try rfl
    · funext j z; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [Cfg.init, accessCfg, Nat.zero_bits]
    · funext j; simp [accessCfg]
  rw [hinit]
  by_cases hv : ∃ z r, y = pairEncode z (Nat.bits r)
  · obtain ⟨z, r, rfl⟩ := hv
    have h := access_valid mode z r 0 (by omega) (by omega)
    have hind : MultiTapeTM.indicator (accessLang mode : Set (List Bool))
        (pairEncode z (Nat.bits r)) = accessValue mode z r := by
      rw [accessLang, indicator_indexLang_pairEncode]
      simp
    simpa [hind] using h
  · have hbad : accessCheck y 0 = none := by
      cases h : accessCheck y 0 with
      | none => rfl
      | some b =>
        obtain ⟨z, r, hy, _⟩ := accessCheck_some h
        exact False.elim (hv ⟨z, r, hy⟩)
    have hscan := access_scan_run mode (y := y) y 0 0 0 (by simp) (by omega) (by omega)
    rw [hbad] at hscan
    have hind : MultiTapeTM.indicator (accessLang mode : Set (List Bool)) y = false := by
      rw [indicator_eq_decide]
      simp only [decide_eq_false_iff_not]
      rintro ⟨z, r, hy, _⟩
      exact hv ⟨z, r, hy⟩
    refine ⟨0, 0, ?_⟩
    rw [hind]
    exact hscan.trans (access_answer mode false 0 0)

/-- Compiling the common access program gives both logarithmic-space query deciders.
Proof sketch: the bounded path gives the run and all pre-halt head bounds. The final
answer leaves every head at zero. Compile with the empty bank; its four head intervals
have `4(W+2)` cells. The received logarithmic polynomial bound absorbs `W = |bits(|y|+1)|`
and the eight boundary cells, including the empty-input case. -/
private lemma access_mem (mode : Bool) : accessLang mode ∈ LOGSPACE := by
  classical
  obtain ⟨C, hC⟩ := log_poly_bound 1 1 0
  refine ⟨4 * C + 8, compileFinTM (accessProg mode) (.read .scan .eC) Dbl.nilTM
    (fun _ => ()), fun y => ?_⟩
  obtain ⟨k, p, hp⟩ := access_run mode y
  obtain ⟨N, hN, hb⟩ := accessPath_run hp
  let W := (Nat.bits (y.length + 1)).length
  have hbox : ∀ t ≤ N, ∀ r, (-1 : ℤ) ≤
      (rrun (accessProg mode) Dbl.o (Cfg.init (.read .scan .eC) y) t).workTapePos r ∧
      (rrun (accessProg mode) Dbl.o (Cfg.init (.read .scan .eC) y) t).workTapePos r ≤ W := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | rfl
    · exact hb t h
    · rw [hN]
      intro j
      simp [accessDone, accessCfg]
  obtain ⟨T, hT, hsp⟩ := compile_space (accessProg mode) (.read .scan .eC) Dbl.nilTM
    (fun _ => ()) Dbl.o (fun _ => -1) (fun _ => (W : ℤ)) 0 N
    [MultiTapeTM.indicator (accessLang mode : Set (List Bool)) y]
    (by simp only [hN, accessDone]) (by simp only [hN, accessDone]) hbox
    (fun _ _ _ _ _ hcs => by simp [accessProg] at hcs)
  refine ⟨T, hT, hsp.trans ?_⟩
  have hsize : ((W : ℤ) - -1 + 1).toNat = W + 2 := by omega
  simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    zero_mul, add_zero]
  have hw := length_bits_le_log (y.length + 1)
  have hc := hC y.length
  simp only [one_mul, pow_one, add_zero] at hc
  unfold logSpace
  dsimp [W]
  have hdist : (4 * C + 8) * (Nat.log 2 y.length + 1) =
      4 * (C * (Nat.log 2 y.length + 1)) + 8 * (Nat.log 2 y.length + 1) := by ring
  omega

end LogProg

/-- **Input random access is logspace** (phase P4.4b; proved): the identity is
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
  refine ⟨⟨1, 1, fun x => by simp⟩, ?_, ?_⟩
  · simpa [LogProg.accessLang, LogProg.accessValue] using LogProg.access_mem false
  · simpa [LogProg.accessLang, LogProg.accessValue] using LogProg.access_mem true

/-- `Complexity.inputBitLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputBitLang_mem : inputBitLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.1

/-- `Complexity.inputLenLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputLenLang_mem : inputLenLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.2

end Complexity
