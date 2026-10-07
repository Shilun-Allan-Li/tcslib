/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEvalMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The circuit-value machine: the whole run

The setup phase of the machine `BoolCircuit.CircuitEval.evalTM` (reading the number of
inputs `n` of the described circuit onto the mark tape, copying the first `n` input bits
onto the value tape, rewinding), the rejection of malformed strings, and the assembly
with the main pass of `CircuitEvalMachine.lean` into the timed computation of the
algorithm's verdict on every input string.

## Main definitions

* `BoolCircuit.CircuitEval.cfS`, `BoolCircuit.CircuitEval.cfC` — the setup and copy
  configurations.

## Main results

* `BoolCircuit.CircuitEval.evalTM_computes` — on every input `z` the machine halts within
  `12 · (|z| + 1)²` steps with output `[verdict exact z]`.

## Length

At about 600 lines this file slightly exceeds the 600-line target: it is the single
timed run of one machine (setup, rejection paths, assembly), whose lemmas share the
private setup configurations and would not split usefully.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the multi-tape machine.)
-/

namespace BoolCircuit

namespace CircuitEval

open Turing Internal

/-! ## Setup: reading the number of inputs and copying the input -/

/-- The setup scan over a description bit: count leading `1`s in phase `n0`, switch to
`sep` at the first `0`. -/
private def scanF : Ph × ℕ → Bool → Ph × ℕ
  | (.n0, r), true => (.n0, r + 1)
  | (.n0, r), false => (.sep, r)
  | p, _ => p

/-- The setup configuration: phase `φ`, value tape blank, `1ʳ` on the mark tape with
the heads at cell `r`. -/
private def cfS (z : List Bool) (φ : Ph) (r i : ℕ) (hi : i ≤ z.length) : Cfg 2 Bool St z :=
  cf z (some (.rd1 φ)) (ip z i hi) (FinTM.bufferTape []) (FinTM.bufferTape (List.replicate r true))
    r []

/-- Configurations at equal input positions are equal. -/
private theorem cfS_congr {z : List Bool} (φ : Ph) (r : ℕ) {i i' : ℕ} (hi : i ≤ z.length)
    (hi' : i' ≤ z.length) (h : i = i') : cfS z φ r i hi = cfS z φ r i' hi' := by
  subst h; rfl

/-- Writing a `1` at the end of the unary mark word. -/
private theorem wr_replicate (r : ℕ) :
    wr (FinTM.bufferTape (List.replicate r true)) (r : ℤ) (some (some true)) =
      FinTM.bufferTape (List.replicate (r + 1) true) := by
  simp only [wr]
  rw [List.replicate_succ', FinTM.bufferTape_append, List.length_replicate]

/-- The setup scan over doubled description bits.

**Proof sketch.** Induction on `w`. Each doubled bit is one `lstep`: in `n0` a `1` writes a
mark under the heads and moves right (`wr_replicate`) and a `0` switches to `sep`; in `sep`
nothing happens. -/
private theorem setup_scan (exact : Bool) {z : List Bool} :
    ∀ (w : List Bool) (φ : Ph) (r : ℕ) (pre rest : List Bool), (φ = .n0 ∨ φ = .sep) →
      z = pre ++ dbl w ++ rest → ∀ (hi : pre.length ≤ z.length)
        (hi' : pre.length + 2 * w.length ≤ z.length),
      (evalTM exact).tm.runFrom (cfS z φ r pre.length hi) (2 * w.length) =
        cfS z (w.foldl scanF (φ, r)).1 (w.foldl scanF (φ, r)).2 (pre.length + 2 * w.length)
          hi' := by
  intro w
  induction w with
  | nil =>
    intro φ r pre rest hφ hz hi hi'
    simp only [List.length_nil, Nat.mul_zero, MultiTapeTM.runFrom_zero, List.foldl_nil]
    rfl
  | cons b w ih =>
    intro φ r pre rest hφ hz hi hi'
    have hi2 : pre.length + 2 ≤ z.length := by simp at hi'; omega
    have hl := lstep exact (z := z) φ pre.length hi2 b b (by rw [hz]; simp)
      (by rw [hz]; simp) (some b) (by simp [pairSym]) (FinTM.bufferTape [])
      (FinTM.bufferTape (List.replicate r true)) r
    have hz' : z = (pre ++ [b, b]) ++ dbl w ++ rest := by rw [hz]; simp
    have hstep : (evalTM exact).tm.runFrom (cfS z φ r pre.length hi) 2 =
        cfS z (scanF (φ, r) b).1 (scanF (φ, r) b).2 (pre.length + 2) hi2 := by
      unfold cfS
      rw [hl]
      rcases hφ with rfl | rfl <;> cases b
      · simp [lact, LA.go, scanF, wr]
      · simp only [lact, scanF]
        rw [wr_replicate]
        simp [wr, SignType.cast]
      · simp [lact, LA.go, scanF, wr]
      · simp [lact, LA.go, scanF, wr]
    have hφ' : (scanF (φ, r) b).1 = .n0 ∨ (scanF (φ, r) b).1 = .sep := by
      rcases hφ with rfl | rfl <;> cases b <;> simp [scanF]
    have htime : 2 * (b :: w).length = 2 + 2 * w.length := by simp; ring
    have hi3 : (pre ++ [b, b]).length + 2 * w.length ≤ z.length := by simp at hi' ⊢; omega
    rw [cfS_congr _ _ hi' hi3 (by simp; ring)]
    conv_lhs => rw [htime, MultiTapeTM.runFrom_add, hstep,
      cfS_congr _ _ hi2 (by rw [hz]; simp) (by simp : pre.length + 2 = (pre ++ [b, b]).length)]
    rw [ih _ _ (pre ++ [b, b]) rest hφ' hz' (by rw [hz]; simp) hi3]
    rfl

/-- The setup scan from `n0` ends in `sep` with the leading unary number if the string
contains a `0`, and in `n0` otherwise. -/
private theorem scanF_n0 (w : List Bool) (r : ℕ) :
    w.foldl scanF (.n0, r) =
      if false ∈ w then (.sep, r + leadOnes w) else (.n0, r + w.length) := by
  have hsep : ∀ (w : List Bool) (r : ℕ), w.foldl scanF (.sep, r) = (.sep, r) := by
    intro w
    induction w with
    | nil => intro r; rfl
    | cons b w ih => intro r; cases b <;> exact ih r
  induction w generalizing r with
  | nil => simp
  | cons b w ih =>
    cases b with
    | false => simp [scanF, hsep, leadOnes]
    | true =>
      simp only [List.foldl_cons, scanF, ih, List.mem_cons, Bool.false_eq_true, false_or]
      have hl : leadOnes (true :: w) = leadOnes w + 1 := by simp [leadOnes]
      split_ifs <;> simp [hl] <;> ring

/-- The cells `h, …, n - 1` marked. -/
private def onesFrom (h n : ℕ) : ℤ → Option Bool :=
  fun c => if (h : ℤ) ≤ c ∧ c < n then some true else none

/-- The copy configuration: `h` input bits copied, marks `h, …, n - 1` left. -/
private def cfC (z : List Bool) (i₀ n h : ℕ) (x : List Bool) (hi : i₀ + h ≤ z.length) :
    Cfg 2 Bool St z :=
  cf z (some .copy) (ip z (i₀ + h) hi) (FinTM.bufferTape (x.take h)) (onesFrom h n) h []

/-- Copy configurations at equal positions are equal. -/
private theorem cfC_congr {z : List Bool} (i₀ n : ℕ) (x : List Bool) {h h' : ℕ}
    (hi : i₀ + h ≤ z.length) (hi' : i₀ + h' ≤ z.length) (e : h = h') :
    cfC z i₀ n h x hi = cfC z i₀ n h' x hi' := by
  subst e; rfl

/-- The copy loop: one input bit per step, while marks remain and input remains.

**Proof sketch.** Induction on `r`. In state `copy`, with a mark under the heads and input bit
`x[h]`, one step writes `x[h]` on the value tape (`FinTM.bufferTape_append`), erases the
mark, and moves the input head and both work heads right. -/
private theorem copy_run (exact : Bool) {z : List Bool} (code x : List Bool)
    (hz : z = dbl code ++ ([false, true] ++ x)) (n : ℕ) :
    ∀ (r h : ℕ), h + r ≤ n → h + r ≤ x.length →
      ∀ (hi : 2 * code.length + 2 + h ≤ z.length)
        (hi' : 2 * code.length + 2 + (h + r) ≤ z.length),
      (evalTM exact).tm.runFrom (cfC z (2 * code.length + 2) n h x hi) r =
        cfC z (2 * code.length + 2) n (h + r) x hi' := by
  intro r
  induction r with
  | zero => intro h _ _ hi hi'; rfl
  | succ r ih =>
    intro h hn hx hi hi'
    have hhx : h < x.length := by omega
    have hhn : h < n := by omega
    have hzx : z[2 * code.length + 2 + h]? = some x[h] := by
      rw [hz, List.getElem?_append_right (by simp; omega), length_dbl,
        show 2 * code.length + 2 + h - 2 * code.length = h + 2 by omega]
      simp [List.getElem?_eq_getElem hhx]
    have hi1 : 2 * code.length + 2 + (h + 1) ≤ z.length := by omega
    have hstep : (evalTM exact).tm.step (cfC z (2 * code.length + 2) n h x hi) =
        cfC z (2 * code.length + 2) n (h + 1) x hi1 := by
      unfold cfC
      rw [step_cf exact .copy _ _ _ _ [] .pos
        ⟨some (some x[h]), some none, .pos, none, some .copy⟩
        (by
          rw [FinTM.inputSymbol_at _ (2 * code.length + 2 + h) hi rfl, hzx]
          simp [tr, tp, onesFrom]
          omega)]
      simp only [wr, List.nil_append, Option.toList_none]
      congr 1
      · apply Fin.ext
        simp only [ip]
        rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
        simp only
        omega
      · rw [List.take_succ, List.getElem?_eq_getElem hhx, Option.toList_some,
          FinTM.bufferTape_append, List.length_take, Nat.min_eq_left hhx.le]
      · funext c
        simp only [onesFrom, Function.update_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ih (h + 1) (by omega) (by omega) hi1
      (by omega)]
    exact cfC_congr _ _ _ _ _ (by omega)

/-! ## The whole run -/

/-- The machine starts in the setup configuration. -/
private theorem init_eq (exact : Bool) (z : List Bool) :
    (evalTM exact).tm.initCfg z = cfS z .n0 0 0 (Nat.zero_le _) := by
  simp only [MultiTapeTM.initCfg, Cfg.init, cfS, cf, List.replicate_zero, FinTM.bufferTape_nil]
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  simp [tp]

/-- A rejecting transition halts with output `0`. -/
theorem step_rej (exact : Bool) {z : List Bool} (q : St) (p : Fin (z.length + 2))
    (vt mt : ℤ → Option Bool) (j : ℤ) (im : SignType)
    (h : tr exact q (cf z (some q) p vt mt j []).inputSymbol (fun i => tp vt mt i j) =
      LA.toAct im .rej) :
    ((evalTM exact).tm.runFrom (cf z (some q) p vt mt j []) 1).state = none ∧
    ((evalTM exact).tm.runFrom (cf z (some q) p vt mt j []) 1).output = [false] := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
    step_cf exact q p vt mt j [] im .rej h]
  simp [cf, LA.rej]

/-- Reading the first bit of a pair. -/
theorem step_rd1 (exact : Bool) {z : List Bool} (φ : Ph) (i : ℕ) (hi : i + 1 ≤ z.length)
    (b : Bool) (hb : z[i]? = some b) (vt mt : ℤ → Option Bool) (j : ℤ) :
    (evalTM exact).tm.step (cf z (some (.rd1 φ)) (ip z i (by omega)) vt mt j []) =
      cf z (some (.rd2 φ b)) (ip z (i + 1) hi) vt mt j [] := by
  rw [step_cf exact (.rd1 φ) _ _ _ _ [] .pos (.go (.rd2 φ b))
    (by rw [FinTM.inputSymbol_at _ _ (by omega) rfl, hb]; rfl)]
  simp only [LA.go, wr, SignType.coe_zero, add_zero, Option.toList_none, List.append_nil]
  congr 1
  apply Fin.ext
  simp only [ip]
  rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]

/-- **Malformed strings are rejected** within `2|w| + 2` steps.

**Proof sketch.** `setup_scan` runs over the doubled prefix in `2|w|` steps; then the
malformed tail is read — the right blank in `rd1`, the right blank in `rd2`, or the pair
`10`, which `pairSym` rejects — and the machine rejects within two steps (`step_rej`). -/
theorem bad_run (exact : Bool) (z w tail : List Bool) (hz : z = dbl w ++ tail)
    (ht : tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) :
    ∃ t ≤ 2 * w.length + 2,
      ((evalTM exact).tm.runFrom ((evalTM exact).tm.initCfg z) t).state = none ∧
      ((evalTM exact).tm.runFrom ((evalTM exact).tm.initCfg z) t).output = [false] := by
  have hw : 2 * w.length ≤ z.length := by rw [hz]; simp
  have hscan := setup_scan exact w .n0 0 [] tail (Or.inl rfl) (by simpa using hz)
    (Nat.zero_le _) (by simpa using hw)
  simp only [List.length_nil, Nat.zero_add] at hscan
  rw [init_eq]
  set φ := (w.foldl scanF (.n0, 0)).1
  set r := (w.foldl scanF (.n0, 0)).2
  rcases ht with rfl | ⟨b, rfl⟩ | ⟨rest, rfl⟩
  · -- the input ends: `rd1` reads the right blank
    have hsym : z[2 * w.length]? = none := by rw [hz]; simp
    have hr := step_rej exact (z := z) (.rd1 φ) (ip z (2 * w.length) hw) (FinTM.bufferTape [])
      (FinTM.bufferTape (List.replicate r true)) r 0
      (by rw [FinTM.inputSymbol_at _ _ hw rfl, hsym]; rfl)
    refine ⟨2 * w.length + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hscan]
    exact hr
  · -- a lone bit: `rd2` reads the right blank
    have hb : z[2 * w.length]? = some b := by rw [hz]; simp
    have hb' : z[2 * w.length + 1]? = none := by rw [hz]; simp
    have hw1 : 2 * w.length + 1 ≤ z.length := by rw [hz]; simp
    have h1 := step_rd1 exact (z := z) φ (2 * w.length) hw1 b hb (FinTM.bufferTape [])
      (FinTM.bufferTape (List.replicate r true)) r
    have hr := step_rej exact (z := z) (.rd2 φ b) (ip z (2 * w.length + 1) hw1)
      (FinTM.bufferTape []) (FinTM.bufferTape (List.replicate r true)) r 0
      (by rw [FinTM.inputSymbol_at _ _ hw1 rfl, hb']; rfl)
    refine ⟨2 * w.length + 1 + 1, by omega, ?_⟩
    rw [show 2 * w.length + 1 + 1 = 2 * w.length + (1 + 1) by ring, MultiTapeTM.runFrom_add,
      hscan, MultiTapeTM.runFrom_succ_eq_step]
    unfold cfS
    rw [h1]
    exact hr
  · -- the malformed aligned pair `10`
    have hw1 : 2 * w.length + 1 ≤ z.length := by rw [hz]; simp
    have h1 := step_rd1 exact (z := z) φ (2 * w.length) hw1 true (by rw [hz]; simp)
      (FinTM.bufferTape []) (FinTM.bufferTape (List.replicate r true)) r
    have hb' : z[2 * w.length + 1]? = some false := by rw [hz]; simp
    have hr := step_rej exact (z := z) (.rd2 φ true) (ip z (2 * w.length + 1) hw1)
      (FinTM.bufferTape []) (FinTM.bufferTape (List.replicate r true)) r 0
      (by rw [FinTM.inputSymbol_at _ _ hw1 rfl, hb']; rfl)
    refine ⟨2 * w.length + 1 + 1, by omega, ?_⟩
    rw [show 2 * w.length + 1 + 1 = 2 * w.length + (1 + 1) by ring, MultiTapeTM.runFrom_add,
      hscan, MultiTapeTM.runFrom_succ_eq_step]
    unfold cfS
    rw [h1]
    exact hr



/-- The unary mark word is the marks `0, …, n - 1`. -/
private theorem onesFrom_zero (n : ℕ) :
    onesFrom 0 n = FinTM.bufferTape (List.replicate n true) := by
  funext c
  simp only [onesFrom, FinTM.bufferTape, Nat.cast_zero]
  by_cases h0 : 0 ≤ c
  · rw [if_pos h0, List.getElem?_replicate]
    by_cases h1 : c < n
    · rw [if_pos ⟨h0, h1⟩, if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_neg h0]

/-- No marks left. -/
private theorem onesFrom_self (n : ℕ) : onesFrom n n = tapeM [] := by
  funext c
  simp only [onesFrom, tapeM, List.not_mem_nil, and_false, if_false]
  rw [if_neg (by omega)]

/-- **Strings that are pairs are decided** within `12 · (|z| + 1)²` steps: the setup and
the main pass.

**Proof sketch.** `setup_scan` reads `dbl code` in `2|code|` steps, ending (`scanF_n0`) in
phase `sep` with `1ⁿ` on the mark tape, `n = leadOnes code`, if `code` contains a `0`, and
in `n0` otherwise, where the separator rejects. In `sep` the separator starts the
mark-tape rewind (`rew`, `n + 1` steps), and `copy_run` copies `min(n, |x|)` input bits.
If `|x| < n` the input runs out under a mark and the machine rejects; if `exact` and
`|x| > n` it rejects at the first unmarked cell; otherwise it rewinds the value tape
(`rew`) and the input (`FinTM.timed_rewind`), reaching the configuration of the abstract
state `(skipN, x.take n, [], 0)` at the start of the input, and `main_run` finishes with
`absRun`, which is the verdict. The setup costs at most `2|code| + 4n + |z| + 9` steps and
the main pass at most `(|code| + 1)(2(n + |code|) + 4)`, both within `12 (|z| + 1)²`
since `n ≤ |x|`. -/
theorem good_run (exact : Bool) (code x z : List Bool)
    (hz : z = dbl code ++ ([false, true] ++ x)) :
    ∃ t ≤ 12 * (z.length + 1) ^ 2,
      ((evalTM exact).tm.runFrom ((evalTM exact).tm.initCfg z) t).state = none ∧
      ((evalTM exact).tm.runFrom ((evalTM exact).tm.initCfg z) t).output =
        [verdict exact z] := by
  have hzlen : z.length = 2 * code.length + 2 + x.length := by rw [hz]; simp; ring
  have hverd : verdict exact z = if false ∈ code ∧ leadOnes code ≤ x.length ∧
      (exact = false ∨ leadOnes code = x.length)
      then absRun ⟨.skipN, x.take (leadOnes code), [], 0⟩ code else false := by
    rw [hz, ← List.append_assoc, ← pairEncode_eq_dbl]
    simp only [verdict, pairDecode_pairEncode]
  have hw : 2 * code.length ≤ z.length := by omega
  have hscan := setup_scan exact code .n0 0 [] ([false, true] ++ x) (Or.inl rfl)
    (by simpa using hz) (Nat.zero_le _) (by simpa using hw)
  simp only [List.length_nil, Nat.zero_add] at hscan
  rw [init_eq]
  have hi2 : 2 * code.length + 2 ≤ z.length := by omega
  have hb : z[2 * code.length]? = some false := by rw [hz]; simp
  have hb' : z[2 * code.length + 1]? = some true := by rw [hz]; simp
  by_cases hf : false ∈ code
  · have hfold : code.foldl scanF (.n0, 0) = (.sep, leadOnes code) := by
      rw [scanF_n0, if_pos hf, Nat.zero_add]
    simp only [hfold] at hscan
    have hnc : leadOnes code ≤ code.length := (List.takeWhile_prefix _).length_le
    set n := leadOnes code with hn
    -- the separator ends the scan and starts the mark-tape rewind
    have hl := lstep exact (z := z) .sep (2 * code.length) hi2 false true hb hb' none rfl
      (FinTM.bufferTape []) (FinTM.bufferTape (List.replicate n true)) n
    simp only [lact, wr, Option.toList_none] at hl
    have hrew := rew exact (z := z) .rewM 1 .copy (fun _ _ => rfl)
      (ip z (2 * code.length + 2) hi2) (FinTM.bufferTape [])
      (FinTM.bufferTape (List.replicate n true)) [] n
      (by intro c hc; simp [tp, hc])
      (by simp [tp])
    have hc0 : cf z (some .copy) (ip z (2 * code.length + 2) hi2) (FinTM.bufferTape [])
        (FinTM.bufferTape (List.replicate n true)) 0 [] =
        cfC z (2 * code.length + 2) n 0 x (by omega) := by
      unfold cfC
      rw [onesFrom_zero]
      rfl
    have hsetup1 : (evalTM exact).tm.runFrom (cfS z .n0 0 0 (Nat.zero_le _))
        (2 * code.length + 2 + (n + 1)) = cfC z (2 * code.length + 2) n 0 x (by omega) := by
      rw [MultiTapeTM.runFrom_add _ (2 * code.length + 2) (n + 1),
        MultiTapeTM.runFrom_add _ (2 * code.length) 2, hscan]
      unfold cfS
      rw [hl, ← hc0, ← hrew]
      congr 2
    by_cases hnx : n ≤ x.length
    · have hcopy := copy_run exact code x hz n n 0 (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.zero_add] at hcopy
      have hin : (cfC z (2 * code.length + 2) n n x (by omega)).inputSymbol = x[n]? := by
        rw [FinTM.inputSymbol_at _ (2 * code.length + 2 + n) (by omega) rfl, hz,
          List.getElem?_append_right (by simp; omega), length_dbl,
          show 2 * code.length + 2 + n - 2 * code.length = n + 2 by omega]
        simp
      have hB : (evalTM exact).tm.runFrom (cfS z .n0 0 0 (Nat.zero_le _))
          (2 * code.length + 2 + (n + 1) + n) = cfC z (2 * code.length + 2) n n x (by omega) := by
        rw [MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1)) n, hsetup1, hcopy]
      by_cases hex : exact = true ∧ n < x.length
      · -- `exact` and the input is longer: reject
        obtain ⟨he, hlt⟩ := hex
        have hr := step_rej exact (z := z) .copy (ip z (2 * code.length + 2 + n) (by omega))
          (FinTM.bufferTape (x.take n)) (onesFrom n n) n 0
          (by
            change tr exact .copy (cfC z (2 * code.length + 2) n n x (by omega)).inputSymbol _ = _
            rw [hin, List.getElem?_eq_getElem hlt]
            subst he
            simp [tr, tp, onesFrom])
        refine ⟨2 * code.length + 2 + (n + 1) + n + 1, by nlinarith, ?_⟩
        have hv : verdict exact z = false := by
          rw [hverd, if_neg]; rintro ⟨-, -, h | h⟩
          · rw [he] at h; exact absurd h (by simp)
          · omega
        rw [hv, MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1) + n) 1, hB]
        exact hr
      · -- rewind the value tape and the input, then run the main pass
        have hstep : (evalTM exact).tm.step (cfC z (2 * code.length + 2) n n x (by omega)) =
            cf z (some (.rewV none)) (ip z (2 * code.length + 2 + n) (by omega))
              (FinTM.bufferTape (x.take n)) (onesFrom n n) ((n : ℤ) - 1) [] := by
          unfold cfC
          rw [step_cf exact .copy _ _ _ _ [] 0 ⟨none, none, .neg, none, some (.rewV none)⟩
            (by
              change tr exact .copy (cfC z (2 * code.length + 2) n n x (by omega)).inputSymbol
                _ = _
              rw [hin]
              have : ¬(exact && x[n]?.isSome) = true := by
                intro h
                simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
                obtain ⟨he, a, ha⟩ := h
                exact hex ⟨he, by
                  by_contra hc
                  rw [List.getElem?_eq_none (by omega)] at ha
                  exact absurd ha (by simp)⟩
              simp [tr, tp, onesFrom, this])]
          simp only [wr, moveInputPos_zero, Option.toList_none, List.append_nil]
          congr 1
        have hrewV := rew exact (z := z) (.rewV none) 0 .rewI0 (fun _ _ => rfl)
          (ip z (2 * code.length + 2 + n) (by omega)) (FinTM.bufferTape (x.take n))
          (onesFrom n n) [] n
          (by
            intro c hc
            simp [tp, hc, List.getElem?_eq_getElem (by omega : c < x.length)])
          (by simp [tp])
        obtain ⟨r, hr, hrun⟩ := FinTM.timed_rewind (evalTM exact).tm .rewI0 .rewI
          (some (.rd1 .skipN)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
          (cf z (some .rewI0) (ip z (2 * code.length + 2 + n) (by omega))
            (FinTM.bufferTape (x.take n)) (onesFrom n n) 0 []) rfl
        have hstart : {cf z (some .rewI0) (ip z (2 * code.length + 2 + n) (by omega))
            (FinTM.bufferTape (x.take n)) (onesFrom n n) 0 [] with
              state := some (.rd1 .skipN), inputPos := 1} =
            cfA z ⟨.skipN, x.take n, [], 0⟩ 0 (by simp) := by
          rw [cfA, onesFrom_self]
          rfl
        obtain ⟨t, ht, hhalt, hout⟩ := main_run exact (z := z) x code
          ⟨.skipN, x.take n, [], 0⟩ []
          (by simpa using hz) (Nat.zero_le _) ⟨by simp, by simp, rfl, fun _ => rfl⟩
          (n + code.length) (by simp)
        have hv : verdict exact z = absRun ⟨.skipN, x.take n, [], 0⟩ code := by
          rw [hverd, if_pos]
          refine ⟨hf, hnx, ?_⟩
          by_cases he : exact = true
          · right; by_contra hc; exact hex ⟨he, by omega⟩
          · left; simpa using he
        have hrb : r ≤ 2 * code.length + 2 + n + 3 := by
          simp only [cf, ip] at hr; omega
        refine ⟨2 * code.length + 2 + (n + 1) + n + 1 + (n + 1) + r + t, ?_, ?_⟩
        · have hB : n + code.length ≤ z.length := by omega
          have h1 : (code.length + 1) * (2 * (n + code.length) + 4) ≤
              (z.length + 1) * (2 * z.length + 4) := by
            apply Nat.mul_le_mul <;> omega
          nlinarith
        · rw [hv]
          simp only [List.length_nil] at hhalt hout
          have h1step : (evalTM exact).tm.runFrom
              (cfC z (2 * code.length + 2) n n x (by omega)) 1 =
              cf z (some (.rewV none)) (ip z (2 * code.length + 2 + n) (by omega))
                (FinTM.bufferTape (x.take n)) (onesFrom n n) ((n : ℤ) - 1) [] := by
            rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, hstep]
          have hC : (evalTM exact).tm.runFrom (cfS z .n0 0 0 (Nat.zero_le _))
              (2 * code.length + 2 + (n + 1) + n + 1 + (n + 1) + r) =
              cfA z ⟨.skipN, x.take n, [], 0⟩ 0 (by simp) := by
            rw [MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1) + n + 1 + (n + 1)) r,
              MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1) + n + 1) (n + 1),
              MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1) + n) 1, hB, h1step,
              hrewV, hrun, hstart]
          rw [MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1) + n + 1 + (n + 1) + r) t,
            hC]
          exact ⟨hhalt, hout⟩
    · -- the input is shorter than the number of inputs: the copy runs out
      have hcopy := copy_run exact code x hz n x.length 0 (by omega) (by omega) (by omega)
        (by omega)
      simp only [Nat.zero_add] at hcopy
      have hr := step_rej exact (z := z) .copy (ip z (2 * code.length + 2 + x.length) (by omega))
        (FinTM.bufferTape (x.take x.length)) (onesFrom x.length n) x.length 0
        (by
          change tr exact .copy (cfC z (2 * code.length + 2) n x.length x (by omega)).inputSymbol
            _ = _
          rw [FinTM.inputSymbol_at _ (2 * code.length + 2 + x.length) (by omega) rfl,
            List.getElem?_eq_none (by omega)]
          simp [tr, tp, onesFrom]
          omega)
      refine ⟨2 * code.length + 2 + (n + 1) + x.length + 1, by nlinarith, ?_⟩
      have hv : verdict exact z = false := by
        rw [hverd, if_neg]; rintro ⟨-, h, -⟩; omega
      rw [hv, MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1) + x.length) 1,
        MultiTapeTM.runFrom_add _ (2 * code.length + 2 + (n + 1)) x.length, hsetup1, hcopy]
      exact hr
  · -- no terminated number of inputs: reject at the separator
    have hfold : code.foldl scanF (.n0, 0) = (.n0, code.length) := by
      rw [scanF_n0, if_neg hf, Nat.zero_add]
    simp only [hfold] at hscan
    have hl := lstep exact (z := z) .n0 (2 * code.length) hi2 false true hb hb' none rfl
      (FinTM.bufferTape []) (FinTM.bufferTape (List.replicate code.length true)) code.length
    have hv : verdict exact z = false := by
      rw [hverd, if_neg]; rintro ⟨h, -⟩; exact hf h
    refine ⟨2 * code.length + 2, by nlinarith, ?_⟩
    rw [hv, MultiTapeTM.runFrom_add _ (2 * code.length) 2, hscan]
    unfold cfS
    rw [hl]
    simp [lact, LA.rej, cf]

/-- **The machine computes the verdict** on every input string `z`, within
`12 · (|z| + 1)²` steps.

**Proof sketch.** If `z` is not a pair, the setup scan reaches a malformed pair or the
end of the input and rejects. Otherwise `z = pairEncode code x`: the setup scan reads
the leading unary `n` onto the mark tape (rejecting at the separator if `code` has no
`0`), rewinds it, copies the first `n` bits of `x` to the value tape (rejecting if `x`
is shorter, or longer when `exact`), and rewinds the value tape and the input; this is
the configuration of the abstract state `(skipN, x.take n, [], 0)`, from which
`main_run` finishes with `absRun`. Setup costs `O(|z|)`, the main pass
`(|code| + 1)(2(n + |code|) + 4) ≤ (|z| + 1)(2|z| + 4)`. -/
theorem evalTM_computes (exact : Bool) (z : List Bool) :
    (evalTM exact).ComputesInTime z [verdict exact z] (12 * (z.length + 1) ^ 2) := by
  have key : ∃ t ≤ 12 * (z.length + 1) ^ 2,
      ((evalTM exact).tm.runFrom ((evalTM exact).tm.initCfg z) t).state = none ∧
      ((evalTM exact).tm.runFrom ((evalTM exact).tm.initCfg z) t).output =
        [verdict exact z] := by
    cases hd : pairDecode z with
    | none =>
      obtain ⟨w, tail, hw, ht⟩ := pairDecode_eq_none z hd
      obtain ⟨t, ht', h1, h2⟩ := bad_run exact z w tail hw ht
      have hv : verdict exact z = false := by simp [verdict, hd]
      refine ⟨t, ?_, h1, by rw [h2, hv]⟩
      have : w.length ≤ z.length := by rw [hw]; simp; omega
      nlinarith
    | some p =>
      obtain ⟨code, x⟩ := p
      exact good_run exact code x z
        (by rw [eq_pairEncode_of_pairDecode z code x hd, pairEncode_eq_dbl, List.append_assoc])
  obtain ⟨t, ht, h1, h2⟩ := key
  refine (FinTM.computesInTime_iff _ _ _ _).mpr ?_
  have he := (evalTM exact).tm.runFrom_add ((evalTM exact).tm.initCfg z) t
    (12 * (z.length + 1) ^ 2 - t)
  rw [Nat.add_sub_of_le ht, MultiTapeTM.runFrom_of_halt _ h1] at he
  rw [he]
  exact ⟨h1, h2⟩

end CircuitEval

end BoolCircuit
