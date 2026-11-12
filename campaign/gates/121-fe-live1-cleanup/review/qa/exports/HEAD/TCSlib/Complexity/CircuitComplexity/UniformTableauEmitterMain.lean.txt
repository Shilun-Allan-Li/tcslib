/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterSteps

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tableau emitter: the whole run

The emitter program reads its input `1ⁿ 0 1ᵀ 0 z` (`Complexity.UTab.goes_rN`,
`Complexity.UTab.goes_rT`, `Complexity.UTab.goes_rZ`), prints the prefix gates, the tableau
(`Complexity.UTab.goes_layers`) and the output vertex, and halts: on such an input with
`T ≥ 1` its output is the description `DAGCircuit.encode` of the uniform tableau circuit
`Complexity.cfgTab M n z T` (`Complexity.UTab.tabEmit_eq`).  On every input it halts within
`C (|w| + 1)³` steps, so its string function is polynomial-time computable
(`Complexity.UTab.polyTimeComputable_tabEmit`) — [AB09, Remark 6.7], polynomial-time half.

## Main definitions

* `Complexity.UTab.tabEmit M` — the emitter's string function.

## Main results

* `Complexity.UTab.tabEmit_eq` — `tabEmit M (1ⁿ 0 1ᵀ 0 z) = (cfgTab M n z T).encode` for `T ≥ 1`.
* `Complexity.UTab.polyTimeComputable_tabEmit` — the emitter is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.2, Remark 6.7.)
-/

namespace Complexity

namespace UTab

open Turing BoolCircuit CounterProg

variable (M : FinTM Bool)

/-! ## Reading the input -/

/-- The `n`-reading loop: each `1` is counted into `NC` and printed. -/
theorem goes_rN (w pre rest : List Bool) : ∀ (a : ℕ) (e : ER),
    w = pre ++ (List.replicate a true ++ rest) →
    Goes (prog M) w .rN e.f pre.length (some .rN) { e with nc := e.nc + a }.f (pre.length + a)
      (List.replicate a true) (3 * a) := by
  intro a
  induction a generalizing pre with
  | zero => intro e _; exact (goes_refl _ _ _).congr rfl (by congr 1) rfl rfl rfl le_rfl
  | succ a ih =>
    intro e hw
    have hx : w[pre.length]? = some true := by simp [hw, List.replicate_succ]
    have h1 := goes_rd_true (P := prog M) (x := w) (ρ := e.f) (l := .rN) rfl hx
    have h2 := goes_incR (P := prog M) (x := w) (e := e) (p := pre.length + 1) (l := .nInc)
      (l' := .nOne) (r := rNC) rfl
    have h3 := goes_out (P := prog M) (x := w) (ρ := ({ e with nc := e.nc + 1 } : ER).f)
      (p := pre.length + 1) (l := .nOne) (l' := .rN) (b := true) rfl
    have h4 := ih (pre ++ [true]) { e with nc := e.nc + 1 } (by simp [hw, List.replicate_succ])
    simp only [List.length_append, List.length_singleton] at h4
    refine (((h1.trans h2).trans h3).trans h4).congr rfl ?_ rfl (by omega) ?_ (by omega)
    · congr 1; ext <;> simp; omega
    · simp [List.replicate_succ]

/-- The `T`-reading loop: each `1` is counted into `T`. -/
theorem goes_rT (w pre rest : List Bool) : ∀ (b : ℕ) (e : ER),
    w = pre ++ (List.replicate b true ++ rest) →
    Goes (prog M) w .rT e.f pre.length (some .rT) { e with t := e.t + b }.f (pre.length + b)
      [] (2 * b) := by
  intro b
  induction b generalizing pre with
  | zero => intro e _; exact (goes_refl _ _ _).congr rfl (by congr 1) rfl rfl rfl le_rfl
  | succ b ih =>
    intro e hw
    have hx : w[pre.length]? = some true := by simp [hw, List.replicate_succ]
    have h1 := goes_rd_true (P := prog M) (x := w) (ρ := e.f) (l := .rT) rfl hx
    have h2 := goes_incR (P := prog M) (x := w) (e := e) (p := pre.length + 1) (l := .tInc)
      (l' := .rT) (r := rT) rfl
    have h4 := ih (pre ++ [true]) { e with t := e.t + 1 } (by simp [hw, List.replicate_succ])
    simp only [List.length_append, List.length_singleton] at h4
    refine ((h1.trans h2).trans h4).congr rfl ?_ rfl (by omega) (by simp) (by omega)
    congr 1; ext <;> simp; omega

/-- The hard-wired-bits loop: each bit `b` is counted into `Z` and its constant gate printed.

**Proof sketch.** Induction on `z`: reading `b` branches to the template `zg b`
(`goes_tp`), which prints `b`'s constant gate, then `Z` is incremented. -/
theorem goes_rZ (w pre rest : List Bool) : ∀ (z : List Bool) (e : ER),
    w = pre ++ (z ++ rest) →
    Goes (prog M) w .rZ e.f pre.length (some .rZ) { e with z := e.z + z.length }.f
      (pre.length + z.length) (z.flatMap fun b => gbits [constGate b]) (z.length * (Lmax M +
          3)) := by
  intro z
  induction z generalizing pre with
  | nil => intro e _; exact (goes_refl _ _ _).congr rfl (by congr 1) rfl rfl rfl (by simp)
  | cons b z ih =>
    intro e hw
    have hx : w[pre.length]? = some b := by simp [hw]
    have h1 : Goes (prog M) w .rZ e.f pre.length (some (tpL (.zg b))) e.f (pre.length +
        1) [] 1 := by
      cases b
      · exact goes_rd_false (P := prog M) (x := w) (l := .rZ) rfl hx
      · exact goes_rd_true (P := prog M) (x := w) (l := .rZ) rfl hx
    have h2 := goes_tp M w (.zg b) e.f (pre.length + 1)
    have h3 := goes_incR (P := prog M) (x := w) (e := e) (p := pre.length + 1) (l := .zInc)
      (l' := .rZ) (r := rZ) rfl
    have h4 := ih (pre ++ [b]) { e with z := e.z + 1 } (by simp [hw])
    simp only [List.length_append, List.length_singleton] at h4
    have hlen := length_tmpl_le M (.zg b)
    refine (((h1.trans h2).trans h3).trans h4).congr rfl ?_ rfl (by simp; omega) ?_ ?_
    · congr 1; ext <;> simp; omega
    · simp [tmpl, flatMap_exec_bitsOps]
    · simp only [List.length_cons]; nlinarith

/-- The emitter on the empty-input tail: halts. -/
theorem goes_stop (w : List Bool) (ρ : Fin 11 → ℕ) (p : ℕ) :
    Goes (prog M) w .stop ρ p none ρ p [] 1 := goes_halt rfl

/-! ## The expected output -/

/-- The instruction gates of a program given as a map over consecutive indices. -/
theorem tabProgGates_range' {κ : Type} [Fintype κ] (m w : ℕ) (F : κ → List Bool → List Bool)
    (n : ℕ) (z : List Bool) (f : ℕ → GInstr κ) : ∀ L a,
    tabProgGates m w F n z a ((List.range' a L).map f) =
      (List.range' a L).flatMap fun i => tabInstrGates m w F n z i (f i) := by
  intro L
  induction L with
  | zero => intro a; rfl
  | succ L ih => intro a; simp [range'_succ_left, tabProgGates, ih]

/-- The output vertex of the uniform tableau circuit, as printed by the final template. -/
theorem cfgTab_output (n : ℕ) (z : List Bool) (T : ℕ) :
    (cfgTab M n z T).output =
      ((SSrc.cur (k := M.k) (snapWidth M)).toLinE M).val (lstart M n z T (T + 1) 0).f := by
  have hlt : snapIdx M (z.length + n) T T < (cfgProg M (tabLayout (z.length + n)) T).length := by
    rw [length_cfgProg, length_tabLayout]; exact snapIdx_lt_succ M _ T T
  simp only [cfgTab, tabCircuit, if_pos (And.intro hlt (show snapWidth M < cfgWidth M by
    unfold cfgWidth; omega))]
  simp only [SSrc.toLinE, LinE.val, List.map_cons, List.map_replicate, List.sum_cons,
    List.sum_replicate_nat, ER.f_nc, ER.f_z, ER.f_i, lstart, tabBase]
  have : snapIdx M (z.length + n) T T + 1 = (T + 1) * Str M n z T := by
    simp only [snapIdx, Str, cfgStride, Nat.succ_mul]; omega
  rw [this]; ring

/-- **The description of the uniform tableau circuit**, in the order the emitter prints it. -/
theorem cfgTab_encode (n : ℕ) (z : List Bool) (T : ℕ) :
    (cfgTab M n z T).encode = List.replicate n true ++ false ::
      (gbits [constGate false, constGate true] ++ (z.flatMap fun b => gbits [constGate b]) ++
        gbits (List.replicate (Wd M) (constGate false)) ++
        (List.range ((T + 1) * Str M n z T)).flatMap (ibits M n z T) ++
        false :: (List.replicate (((SSrc.cur (k := M.k) (snapWidth M)).toLinE M).val
          (lstart M n z T (T + 1) 0).f) true ++ [false])) := by
  rw [DAGCircuit.encode, encodeList_eq_gbits, ← cfgTab_output, encodeNat, encodeNat]
  simp only [cfgTab, tabCircuit, gbits_append, tabPre]
  rw [cfgProg, show List.range ((T + 1) * cfgStride M (tabLayout (z.length + n)).length T) =
    List.range' 0 ((T + 1) * Str M n z T) by simp [List.range_eq_range', Str],
    tabProgGates_range']
  simp [gbits, List.flatMap_map, List.range_eq_range', List.append_assoc]
  rw [List.flatMap_assoc]; rfl

/-! ## The whole run -/

/-- The bits printed while reading the input `1ⁿ 0 1ᵀ 0 z`: `1ⁿ 0`, then the constant gates,
the hard-wired gates and the padding gates. -/
noncomputable def prefixBits (n : ℕ) (z : List Bool) : List Bool :=
  List.replicate n true ++ false :: (gbits [constGate false, constGate true] ++
    (z.flatMap fun b => gbits [constGate b]) ++ gbits (List.replicate (Wd M) (constGate false)))

/-- The step bound of the reading phase. -/
noncomputable def prefixBound (n : ℕ) (z : List Bool) (T : ℕ) : ℕ :=
  3 * n + 2 * T + z.length * (Lmax M + 3) + 2 * (Lmax M + 1) + 6

/-- **Reading the input** `1ⁿ 0 1ᵀ 0 z`: the emitter counts `n`, `T` and `|z|`, prints the
prefix of the description, and reaches the tableau with the registers of its first step.

**Proof sketch.** The reading loops `goes_rN`, `goes_rT`, `goes_rZ`, and the constant and
padding templates. -/
theorem goes_prefix (n T : ℕ) (z : List Bool) :
    Goes (prog M) (List.replicate n true ++ false :: (List.replicate T true ++ false :: z))
      .rN ER.zero.f 0 (some (.lay true)) (lstart M n z T 0 0).f (n + 1 + T + 1 + z.length)
      (prefixBits M n z) (prefixBound M n z T) := by
  set w := List.replicate n true ++ false :: (List.replicate T true ++ false :: z) with hw
  have hg : ∀ (a : ℕ) (b : Bool) (r : List Bool) (i : ℕ),
      (List.replicate a b ++ r)[a + i]? = r[i]? := by
    intro a b r i; rw [List.getElem?_append_right (by simp)]; simp
  have hx1 : w[n]? = some false := by simp [hw]
  have hx2 : w[n + 1 + T]? = some false := by
    rw [hw, show n + 1 + T = n + (T + 1) by omega, hg, List.getElem?_cons_succ]
    simp
  have hx3 : w[n + 1 + T + 1 + z.length]? = none := by
    rw [hw, show n + 1 + T + 1 + z.length = n + ((T + (z.length + 1)) + 1) by omega, hg,
      List.getElem?_cons_succ, hg, List.getElem?_cons_succ]
    simp
  let e1 : ER := { ER.zero with nc := n }
  let e2 : ER := { e1 with t := T }
  have h1 : Goes (prog M) w .rN ER.zero.f 0 (some .rN) e1.f n (List.replicate n true) (3 * n) := by
    have := goes_rN M w [] (false :: (List.replicate T true ++ false :: z)) n ER.zero (by simp [hw])
    exact this.congr rfl (by congr 1; ext <;> simp [e1, ER.zero]) rfl (by simp) rfl le_rfl
  have h2 := goes_rd_false (P := prog M) (x := w) (l := .rN) (p := n) (ρ := e1.f) rfl hx1
  have h3 := goes_out (P := prog M) (x := w) (l := .nOut0) (l' := .rT) (b := false) (p := n + 1)
    (ρ := e1.f) rfl
  have h4 : Goes (prog M) w .rT e1.f (n + 1) (some .rT) e2.f (n + 1 + T) [] (2 * T) := by
    have := goes_rT M w (List.replicate n true ++ [false]) (false :: z) T e1 (by simp [hw])
    exact this.congr (by simp) (by congr 1; ext <;> simp [e1, e2, ER.zero]) (by simp) (by simp) rfl
      le_rfl
  have h5 := goes_rd_false (P := prog M) (x := w) (l := .rT) (p := n + 1 + T) (ρ := e2.f) rfl hx2
  have h6 := goes_tp M w .pre e2.f (n + 1 + T + 1)
  have h7 : Goes (prog M) w .rZ e2.f (n + 1 + T + 1) (some .rZ) (lstart M n z T 0 0).f
      (n + 1 + T + 1 + z.length) (z.flatMap fun b => gbits [constGate b])
      (z.length * (Lmax M + 3)) := by
    have := goes_rZ M w (List.replicate n true ++ [false] ++ List.replicate T true ++ [false]) []
      z e2 (by simp [hw])
    exact this.congr (by simp) (by congr 1; ext <;> simp [e1, e2, ER.zero, lstart])
      (by simp; omega) (by simp; omega) rfl le_rfl
  have h8 := goes_rd_end (P := prog M) (x := w) (l := .rZ) (p := n + 1 + T + 1 + z.length)
    (ρ := (lstart M n z T 0 0).f) rfl hx3
  have h9 := goes_tp M w .dum (lstart M n z T 0 0).f (n + 1 + T + 1 + z.length)
  have hall := (((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans
    h8).trans h9
  refine hall.congr rfl rfl rfl rfl ?_ ?_
  · simp [prefixBits, tmpl, flatMap_exec_bitsOps, List.append_assoc]
  · have := length_tmpl_le M .pre
    have := length_tmpl_le M .dum
    simp only [prefixBound]
    omega

/-- The step bound of the emitter on the input `1ⁿ 0 1ᵀ 0 z`. -/
noncomputable def runBound (n : ℕ) (z : List Bool) (T : ℕ) : ℕ :=
  prefixBound M n z T + (T + 1) * (layerBound M n z T + 7 * T + 10) + Lmax M + 2

/-- **The emitter on a well-formed input** `1ⁿ 0 1ᵀ 0 z` with `T ≥ 1` halts after printing the
description of `cfgTab M n z T`.

**Proof sketch.** The reading phase (`goes_prefix`); the tableau (`goes_layers`); the final
template prints the list terminator and the output vertex (`cfgTab_output`); this is the
description (`cfgTab_encode`). -/
theorem goes_emit (n T : ℕ) (z : List Bool) (hT : 1 ≤ T) :
    ∃ ρ p, Goes (prog M) (List.replicate n true ++ false :: (List.replicate T true ++ false :: z))
      .rN ER.zero.f 0 none ρ p (cfgTab M n z T).encode (runBound M n z T) := by
  set w := List.replicate n true ++ false :: (List.replicate T true ++ false :: z) with hw
  have h1 := goes_prefix M n T z
  have h2 := goes_layers M w (n := n) (z := z) hT (n + 1 + T + 1 + z.length)
  have h3 := goes_tp M w .fin (lstart M n z T (T + 1) 0).f (n + 1 + T + 1 + z.length)
  have h4 := goes_stop M w (lstart M n z T (T + 1) 0).f (n + 1 + T + 1 + z.length)
  refine ⟨_, _, (((h1.trans h2).trans h3).trans h4).congr rfl rfl rfl rfl ?_ ?_⟩
  · rw [cfgTab_encode]
    simp [prefixBits, tmpl, flatMap_exec_linOps, MOp.exec, List.append_assoc]
  · have := length_tmpl_le M .fin
    simp only [runBound]
    omega

/-! ## Every input -/

/-- The constant of the emitter's cubic running time. -/
noncomputable def emitC : ℕ := 60 * (M.k + 1) * (Lmax M + 30)

/-- **The running time on a well-formed input is cubic**: at most `emitC · X³` steps, `X` one
more than the input length.

**Proof sketch.** With `X = n + T + |z| + 3` and `K = Lmax + 30`: one step of the tableau costs
at most `32 (k + 1) K X²` (its `S ≤ (2k + 1) X` instructions of constant cost and the
copies), there are `T + 1 ≤ X` steps, and reading the input costs at most `5 K X`. -/
theorem runBound_le (n : ℕ) (z : List Bool) (T : ℕ) :
    runBound M n z T ≤ emitC M * (n + T + z.length + 3) ^ 3 := by
  set X := n + T + z.length + 3 with hX
  set K := Lmax M + 30 with hK
  set Y := (M.k + 1) * K * X ^ 2 with hY
  have hX1 : 1 ≤ X := by omega
  have hK1 : 1 ≤ K := by omega
  have hkK : K ≤ (M.k + 1) * K := Nat.le_mul_of_pos_left K (by omega)
  have hXX : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have hKX : K * X ≤ Y := by
    calc K * X ≤ (M.k + 1) * K * X := Nat.mul_le_mul_right X hkK
      _ ≤ (M.k + 1) * K * X ^ 2 := Nat.mul_le_mul_left _ hXX
  have hS : Str M n z T ≤ (2 * M.k + 1) * X := by
    simp only [Str, cfgStride]; nlinarith
  have hlay : layerBound M n z T ≤ 32 * Y := by
    simp only [layerBound, Ki]
    have h1 : M.k * ((2 * T + 3) * (Lmax M + 20)) ≤ 3 * Y := by
      have : (2 * T + 3) * (Lmax M + 20) ≤ 3 * X * K := by nlinarith
      calc M.k * ((2 * T + 3) * (Lmax M + 20)) ≤ (M.k + 1) * (3 * X * K) :=
            Nat.mul_le_mul (by omega) this
        _ = 3 * ((M.k + 1) * K * X) := by ring
        _ ≤ 3 * Y := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ hXX)
    have h2 : (z.length + n + 2) * (Lmax M + 20) ≤ Y := by
      calc (z.length + n + 2) * (Lmax M + 20) ≤ X * K := Nat.mul_le_mul (by omega) (by omega)
        _ = K * X := by ring
        _ ≤ Y := hKX
    have h3 : 9 * ((T + 1) * Str M n z T) ≤ 27 * Y := by
      have h : (T + 1) * Str M n z T ≤ X * ((2 * M.k + 1) * X) := Nat.mul_le_mul (by omega) hS
      have h' : X * ((2 * M.k + 1) * X) ≤ 3 * Y := by
        calc X * ((2 * M.k + 1) * X) = (2 * M.k + 1) * X ^ 2 := by ring
          _ ≤ 3 * ((M.k + 1) * 1 * X ^ 2) := by nlinarith
          _ ≤ 3 * Y := by
            apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ hK1
      omega
    have h4 : Lmax M + 3 + 6 ≤ Y := by
      have : K ≤ K * X := Nat.le_mul_of_pos_right K (by omega)
      omega
    omega
  have hT1 : T + 1 ≤ X := by omega
  have h7 : 7 * T + 10 ≤ 17 * Y := by
    have : X ≤ K * X := Nat.le_mul_of_pos_left X (by omega)
    omega
  have hmain : (T + 1) * (layerBound M n z T + 7 * T + 10) ≤ X * (49 * Y) :=
    Nat.mul_le_mul hT1 (by omega)
  have hrest : prefixBound M n z T + Lmax M + 2 ≤ 5 * (K * X) := by
    simp only [prefixBound]; nlinarith
  have hfin : X * (49 * Y) + 5 * (K * X) ≤ emitC M * X ^ 3 := by
    have e1 : X * (49 * Y) = 49 * ((M.k + 1) * K * X ^ 3) := by rw [hY]; ring
    have e2 : K * X ≤ (M.k + 1) * K * X ^ 3 := by
      calc K * X ≤ (M.k + 1) * K * X := Nat.mul_le_mul_right X hkK
        _ ≤ (M.k + 1) * K * X ^ 3 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) X)
    have e3 : emitC M * X ^ 3 = 60 * ((M.k + 1) * K * X ^ 3) := by simp only [emitC, hK]; ring
    omega
  simp only [runBound]
  omega

/-- Every input is a block of `1`s, or a block of `1`s followed by `0` and a rest. -/
theorem classify (w : List Bool) :
    (∃ a, w = List.replicate a true) ∨ ∃ a r, w = List.replicate a true ++ false :: r := by
  induction w with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons b w ih =>
    cases b
    · exact Or.inr ⟨0, w, rfl⟩
    · rcases ih with ⟨a, rfl⟩ | ⟨a, r, rfl⟩
      · exact Or.inl ⟨a + 1, rfl⟩
      · exact Or.inr ⟨a + 1, r, rfl⟩

/-- **The emitter halts on every input** within `emitC · (|w| + 1)³` steps.

**Proof sketch.** By `classify` (twice), the input is `1ᵃ` (the `n`-loop meets the end of the
input and halts), `1ᵃ 0 1ᵇ` (the `T`-loop meets the end and halts), `1ⁿ 0 1⁰ 0 z` (the
reading phase, then the test `T = 0` halts), or `1ⁿ 0 1ᵀ 0 z` with `T ≥ 1` (`goes_emit`). -/
theorem goes_any (w : List Bool) :
    ∃ ρ p e B, B ≤ emitC M * (w.length + 1) ^ 3 ∧
      Goes (prog M) w .rN ER.zero.f 0 none ρ p e B := by
  have hpow : ∀ L : ℕ, 3 * L + 10 ≤ emitC M * (L + 1) ^ 3 := by
    intro L
    have h1 : 60 ≤ emitC M := by
      simp only [emitC]; nlinarith [Nat.zero_le (M.k * (Lmax M + 30)), Nat.zero_le (Lmax M)]
    have h2 : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    nlinarith
  rcases classify w with ⟨a, rfl⟩ | ⟨a, r, rfl⟩
  · -- `1ᵃ`
    have h1 := goes_rN M (List.replicate a true) [] [] a ER.zero (by simp)
    have h2 := goes_rd_end (P := prog M) (x := List.replicate a true) (l := .rN)
      (p := ([] : List Bool).length + a) (ρ := ({ ER.zero with nc := ER.zero.nc + a } :
          ER).f) rfl (by simp)
    have h3 := goes_stop M (List.replicate a true) ({ ER.zero with nc := ER.zero.nc + a } : ER).f
      (([] : List Bool).length + a)
    refine ⟨_, _, _, _, ?_, ((h1.trans h2).trans h3)⟩
    have := hpow a; simp; omega
  · rcases classify r with ⟨b, rfl⟩ | ⟨b, z, rfl⟩
    · -- `1ᵃ 0 1ᵇ`
      have h1 := goes_rN M (List.replicate a true ++ false :: List.replicate b true) []
        (false :: List.replicate b true) a ER.zero (by simp)
      have h2 := goes_rd_false (P := prog M) (x := List.replicate a true ++ false ::
        List.replicate b true) (l := .rN) (p := ([] : List Bool).length + a)
        (ρ := ({ ER.zero with nc := ER.zero.nc + a } : ER).f) rfl (by simp)
      have h3 := goes_out (P := prog M) (x := List.replicate a true ++ false ::
        List.replicate b true) (l := .nOut0) (l' := .rT) (b := false) (p := ([] : List
            Bool).length + a + 1)
        (ρ := ({ ER.zero with nc := ER.zero.nc + a } : ER).f) rfl
      have h4 := goes_rT M (List.replicate a true ++ false :: List.replicate b true)
        (List.replicate a true ++ [false]) [] b { ER.zero with nc := ER.zero.nc + a } (by simp)
      simp only [List.length_append, List.length_replicate, List.length_singleton] at h4
      have h5 := goes_rd_end (P := prog M) (x := List.replicate a true ++ false ::
        List.replicate b true) (l := .rT) (p := a + 1 + b)
        (ρ := ({ ({ ER.zero with nc := ER.zero.nc + a } : ER) with t := ER.zero.t + b } : ER).f)
        rfl (by
          rw [show a + 1 + b = a + (b + 1) by omega, List.getElem?_append_right (by simp)]
          simp)
      have h6 := goes_stop M (List.replicate a true ++ false :: List.replicate b true)
        ({ ({ ER.zero with nc := ER.zero.nc + a } : ER) with t := ER.zero.t + b } : ER).f
        (a + 1 + b)
      refine ⟨_, _, _, _, ?_, (((((h1.trans h2).trans h3).trans
        (h4.congr rfl rfl (by simp) rfl rfl le_rfl)).trans h5).trans h6)⟩
      have := hpow (a + 1 + b)
      simp only [List.length_append, List.length_replicate, List.length_cons]
      rw [show a + (b + 1) + 1 = a + 1 + b + 1 by omega]
      omega
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · -- `T = 0`
        have h1 := goes_prefix M a 0 z
        have h2 := goes_jz_zero (P := prog M) (x := List.replicate a true ++ false ::
          (List.replicate 0 true ++ false :: z)) (l := .lay true) (l0 := .stop)
          (l1 := cellStart true 0) (r := rT) (ρ := (lstart M a z 0 0 0).f)
          (p := a + 1 + 0 + 1 + z.length) rfl (by simp [lstart])
        have h3 := goes_stop M (List.replicate a true ++ false ::
          (List.replicate 0 true ++ false :: z)) (lstart M a z 0 0 0).f (a + 1 + 0 + 1 + z.length)
        refine ⟨_, _, _, _, ?_, ((h1.trans h2).trans h3)⟩
        have h := runBound_le M a z 0
        simp only [runBound] at h
        have : (a + 0 + z.length + 3) ^ 3 ≤
            ((List.replicate a true ++ false :: (List.replicate 0 true ++ false :: z)).length +
                1) ^ 3 :=
          Nat.pow_le_pow_left (by simp; omega) 3
        have := Nat.mul_le_mul_left (emitC M) this
        omega
      · -- the well-formed case
        obtain ⟨ρ, p, h⟩ := goes_emit M a b z hb
        refine ⟨ρ, p, _, _, ?_, h⟩
        have h1 := runBound_le M a z b
        have : (a + b + z.length + 3) ^ 3 ≤
            ((List.replicate a true ++ false :: (List.replicate b true ++ false :: z)).length +
                1) ^ 3 :=
          Nat.pow_le_pow_left (by simp; omega) 3
        have := Nat.mul_le_mul_left (emitC M) this
        omega

/-- **The emitter's string function**: the output of the emitter program after
`emitC · (|w| + 1)³` steps (by then it has halted, `goes_any`). -/
noncomputable def tabEmit (w : List Bool) : List Bool :=
  (run (prog M) w (init .rN) (emitC M * (w.length + 1) ^ 3)).out

/-- A halting run within the budget determines the state at the budget. -/
theorem run_budget {w : List Bool} {ρ : Fin 11 → ℕ} {p : ℕ} {e : List Bool} {B C : ℕ}
    (h : Goes (prog M) w .rN ER.zero.f 0 none ρ p e B) (hB : B ≤ C) :
    run (prog M) w (init .rN) C = ⟨none, ρ, p, e⟩ := by
  obtain ⟨t, ht, hrun⟩ := h []
  have hinit : (init .rN : St 11 (Lb M.k (Lmax M))) = ⟨some .rN, ER.zero.f, 0, []⟩ := by
    simp [init, ER.zero_f]
  rw [hinit, show C = t + (C - t) by omega, run_add, hrun, run_of_halted _ _ _ rfl]
  simp

/-- **[AB09, Remark 6.7], polynomial-time half: the emitter is polynomial-time
computable.** -/
theorem polyTimeComputable_tabEmit : PolyTimeComputable (tabEmit M) := by
  refine CounterProg.polyTimeComputable (prog M) .rN (tabEmit M) (emitC M) 3 fun w => ?_
  obtain ⟨ρ, p, e, B, hB, h⟩ := goes_any M w
  refine ⟨emitC M * (w.length + 1) ^ 3, le_rfl, ?_, rfl⟩
  rw [run_budget M h hB]

/-- **The emitter prints the uniform tableau circuit**: on `1ⁿ 0 1ᵀ 0 z` with `T ≥ 1` its output
is the description of `Complexity.cfgTab M n z T`. -/
theorem tabEmit_eq (n T : ℕ) (z : List Bool) (hT : 1 ≤ T) :
    tabEmit M (List.replicate n true ++ false :: (List.replicate T true ++ false :: z)) =
      (cfgTab M n z T).encode := by
  obtain ⟨ρ, p, h⟩ := goes_emit M n T z hT
  have hb := runBound_le M n z T
  have : (n + T + z.length + 3) ^ 3 ≤
      ((List.replicate n true ++ false :: (List.replicate T true ++ false :: z)).length + 1) ^ 3 :=
    Nat.pow_le_pow_left (by simp; omega) 3
  have := Nat.mul_le_mul_left (emitC M) this
  rw [tabEmit, run_budget M h (by omega)]

end UTab

end Complexity
