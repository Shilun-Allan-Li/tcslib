/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfigCircuit
import TCSlib.Complexity.CircuitComplexity.UniformTableauCircuit
import TCSlib.Complexity.ClassNP.CounterProgPolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The uniform configuration-tableau circuit

The circuit printed by the polynomial-time machine of [AB09, Remark 6.7]: the regular
compilation `BoolCircuit.tabCircuit` of the configuration-tableau program
`Complexity.cfgProg` of a machine `M` (`PSubsetPPolyConfig.lean`), on a virtual input
`z ++ x` whose prefix `z` is hard-wired and whose suffix `x` is the circuit's input
(`Complexity.cfgTab M n z T`).  It decides whether `M` emits `1` within `T` steps on `z ++ x`
(`Complexity.cfgTab_eval`).

The second half of the file is the bridge to the emitting machine: *symbolic sources*
(`Complexity.UTab.SSrc`), describing each source of an instruction relative to the
emitter's registers (the current instruction, the same cell one step earlier, the layer's
first instruction, …), with their meaning as a source (`Complexity.UTab.SSrc.toBitSrc`)
and as a printed vertex (`Complexity.UTab.SSrc.toLinE`); `Complexity.UTab.tabSrc_toBitSrc`
says the two agree.

## Main definitions

* `Complexity.tabLayout N` — the layout reading the virtual input positions `0, …, N − 1`.
* `Complexity.cfgTab M n z T` — the uniform tableau circuit.
* `Complexity.UTab.SSrc` — symbolic sources.

## Main results

* `Complexity.cfgTab_eval` — the circuit outputs `1` iff some step `s < T` of `M` on
  `z ++ x` emits `1`.
* `Complexity.cfgTab_isFaninTwo`, `Complexity.cfgTab_size`.
* `Complexity.UTab.tabSrc_toBitSrc` — a symbolic source is printed as the vertex of the
  source it denotes.

## Divergences from [AB09]

* `cfgTab` is the non-oblivious configuration tableau, of size `O(T (T + |z| + n))`
  (`Complexity.cfgTab_size`) — not the book's `O(T)`-size oblivious circuit of Thm 6.6; see
  also `UniformTableauCircuit.lean` and `UniformTableau.lean`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6; §6.2, Remark 6.7.)
-/

namespace Complexity

open Turing BoolCircuit

/-! ## The circuit -/

/-- The layout of a virtual input of length `N`: position `p` reads input `p`. -/
def tabLayout (N : ℕ) : List BitSrc := (List.range N).map BitSrc.input

/-- The layout of a virtual input of length `N` has `N` entries. -/
@[simp] theorem length_tabLayout (N : ℕ) : (tabLayout N).length = N := by simp [tabLayout]

/-- The layout reads valid inputs. -/
theorem tabLayout_valid (N w : ℕ) : ∀ s ∈ tabLayout N, s.Valid N w 0 := by
  intro s hs
  simp only [tabLayout, List.mem_map, List.mem_range] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  exact hk

/-- The layout evaluates to the virtual input. -/
theorem tabLayout_eval (v : List Bool) : (tabLayout v.length).map (BitSrc.eval v []) = v := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [tabLayout, BitSrc.eval, List.getElem?_eq_getElem h2]

variable (M : FinTM Bool)

/-- **The uniform configuration-tableau circuit** of `M` on `n` inputs with hard-wired prefix
`z`, for `T` steps: the regular compilation (`BoolCircuit.tabCircuit`) of the
configuration-tableau program on the virtual input `z ++ x` of length `|z| + n`, with output
the acceptance accumulator of the last snapshot. -/
noncomputable def cfgTab (n : ℕ) (z : List Bool) (T : ℕ) : DAGCircuit n :=
  tabCircuit (cfgArity M) (cfgWidth M) (cfgF M) n z (cfgProg M (tabLayout (z.length + n)) T)
    (snapIdx M (z.length + n) T T) (snapWidth M)

/-- **Correctness of the uniform tableau circuit**: on input `x` it outputs `1` iff some step
`s < T` of `M` on the virtual input `z ++ x` emits `1`.

**Proof sketch.** The program is well formed with `cfgArity M` sources per instruction
(`Complexity.cfgProg_wf`), so the circuit computes its blocks (`BoolCircuit.tabCircuit_eval`);
every block is the true block (`Complexity.cfgProg_blocks`), and the output is the
accumulator bit of the last snapshot. -/
theorem cfgTab_eval (n : ℕ) (z : List Bool) (T : ℕ) (x : Fin n → Bool) :
    (cfgTab M n z T).eval x =
      decide (∃ s < T, emitted M (snapshotAt M (z ++ List.ofFn x) s) = some true) := by
  have hℓ := tabLayout_valid (z.length + n) (cfgWidth M)
  have hwf := cfgProg_wf (T := T) hℓ
  have hlt : snapIdx M (z.length + n) T T <
      (cfgProg M (tabLayout (z.length + n)) T).length := by
    rw [length_cfgProg, length_tabLayout]; exact snapIdx_lt_succ M _ T T
  have hlen : (z ++ List.ofFn x).length = z.length + n := by simp
  rw [cfgTab, tabCircuit_eval _ _ _ _ _ _ hwf.1 hwf.2 hlt (by unfold cfgWidth; omega)]
  have hb := cfgProg_blocks (T := T) hℓ (z ++ List.ofFn x) _ hlt
  have hs := cfgExp_snapIdx M (tabLayout (z.length + n)) T
    ((tabLayout (z.length + n)).map (BitSrc.eval (z ++ List.ofFn x) [])) T
  simp only [length_tabLayout] at hs
  rw [hb, hs, ← hlen, tabLayout_eval, snapExp, List.getD_append_right _ _ _ _ (by simp)]
  simp [tableauAccepted]

/-- The uniform tableau circuit has fan-in two. -/
theorem cfgTab_isFaninTwo (n : ℕ) (z : List Bool) (T : ℕ) : (cfgTab M n z T).IsFaninTwo :=
  tabCircuit_isFaninTwo _ _ _ _ _ _ _ _

/-- The size of the uniform tableau circuit: `n + 2 + |z| + W ((T + 1) · stride + 1)`, `W` a
constant of `M` and `stride = k (2T + 1) + |z| + n + 3`. -/
theorem cfgTab_size (n : ℕ) (z : List Bool) (T : ℕ) :
    (cfgTab M n z T).size = n + 2 + z.length + tabW (cfgArity M) (cfgWidth M) (cfgF M) *
      ((T + 1) * (M.k * (2 * T + 1) + (z.length + n) + 3) + 1) := by
  rw [cfgTab, tabCircuit_size, length_cfgProg, length_tabLayout]
  rfl

/-! ## Symbolic sources -/

namespace UTab

/-- The emitter's registers: the number `n` of circuit inputs, the length `|z|` of the
hard-wired prefix, the step budget `T`, the current instruction `I`, the same instruction one
step earlier `Q = I − stride`, the layer's first instruction `LB`, the layer counter, the
inner loop counter, the position counters in the hard-wired and free parts of the input,
and a scratch register. -/
abbrev rNC : Fin 11 := 0
/-- The register `|z|`, the number of hard-wired bits. -/
abbrev rZ : Fin 11 := 1
/-- The register `T`, the step budget. -/
abbrev rT : Fin 11 := 2
/-- The register `I`, the current instruction. -/
abbrev rI : Fin 11 := 3
/-- The register `Q`, the current cell one step earlier. -/
abbrev rQ : Fin 11 := 4
/-- The register `LB`, the first instruction of the current step. -/
abbrev rLB : Fin 11 := 5
/-- The register `LT`, the step-loop counter. -/
abbrev rLT : Fin 11 := 6
/-- The register `LL`, the inner loop counter. -/
abbrev rLL : Fin 11 := 7
/-- The register `PA`, the position in the hard-wired part of the input. -/
abbrev rPA : Fin 11 := 8
/-- The register `PB`, the position in the free part of the input. -/
abbrev rPB : Fin 11 := 9
/-- The register `TMP`, scratch. -/
abbrev rTMP : Fin 11 := 10

/-- A source of an instruction described relative to the emitter's registers: a constant;
the current position of the hard-wired or of the free part of the input; bit `j` of the
block of a neighbour one step earlier (`prv d j`, the instruction `Q + d − 1`), of the
previous instruction (`cur j`), of the previous snapshot (`psn j`, instruction `LB − 1`), or
of the last cell of work tape `τ` in the current step (`cend τ j`). -/
inductive SSrc (k : ℕ) where
  | cst (b : Bool)
  | zin
  | uin
  | prv (d : Fin 3) (j : ℕ)
  | cur (j : ℕ)
  | psn (j : ℕ)
  | cend (τ : Fin k) (j : ℕ)

variable {k : ℕ}

/-- The source a symbolic source denotes, for register values `ρ`. -/
def SSrc.toBitSrc (ρ : Fin 11 → ℕ) : SSrc k → BitSrc
  | .cst b => .const b
  | .zin => .input (ρ rPA)
  | .uin => .input (ρ rZ + ρ rPB)
  | .prv d j => .block (ρ rQ + d - 1) j
  | .cur j => .block (ρ rI - 1) j
  | .psn j => .block (ρ rLB - 1) j
  | .cend τ j => .block (ρ rLB + (τ + 1) * (2 * ρ rT + 1) - 1) j

/-- The side conditions under which a symbolic source's printed vertex is right: the
denoted instruction index does not underflow, and a hard-wired position is in range. -/
def SSrc.Ok (ρ : Fin 11 → ℕ) : SSrc k → Prop
  | .zin => ρ rPA < ρ rZ
  | .prv d _ => 1 ≤ ρ rQ + d
  | .cur _ => 1 ≤ ρ rI
  | .psn _ => 1 ≤ ρ rLB
  | _ => True

/-- The linear expression printing the vertex of a symbolic source in the circuit
`cfgTab M`: constants are `n + b`, hard-wired bits `n + 2 + p`, free inputs `p`, and bit `j`
of instruction `i'` is `n + 2 + |z| + W (i' + 1) + m + G + j`. -/
noncomputable def SSrc.toLinE (M : FinTM Bool) : SSrc M.k → CounterProg.LinE 11
  | .cst b => ([rNC], if b then 1 else 0)
  | .zin => ([rNC, rPA], 2)
  | .uin => ([rPB], 0)
  | .prv d j => (rNC :: rZ :: List.replicate (tabW (cfgArity M) (cfgWidth M) (cfgF M)) rQ,
      2 + tabW (cfgArity M) (cfgWidth M) (cfgF M) * d + cfgArity M +
        tabG (cfgArity M) (cfgWidth M) (cfgF M) + j)
  | .cur j => (rNC :: rZ :: List.replicate (tabW (cfgArity M) (cfgWidth M) (cfgF M)) rI,
      2 + cfgArity M + tabG (cfgArity M) (cfgWidth M) (cfgF M) + j)
  | .psn j => (rNC :: rZ :: List.replicate (tabW (cfgArity M) (cfgWidth M) (cfgF M)) rLB,
      2 + cfgArity M + tabG (cfgArity M) (cfgWidth M) (cfgF M) + j)
  | .cend τ j => (rNC :: rZ :: (List.replicate (tabW (cfgArity M) (cfgWidth M) (cfgF M)) rLB ++
      List.replicate (2 * tabW (cfgArity M) (cfgWidth M) (cfgF M) * (τ + 1)) rT),
      2 + tabW (cfgArity M) (cfgWidth M) (cfgF M) * (τ + 1) + cfgArity M +
        tabG (cfgArity M) (cfgWidth M) (cfgF M) + j)

/-- **A symbolic source is printed as the vertex of the source it denotes** in the uniform
tableau circuit, when the registers hold `n` and `|z|`, the side conditions hold and the
denoted source is valid for instruction `i`.

**Proof sketch.** Case analysis on the symbolic source: validity selects the main branch
of `tabSrc`, and the block vertex `n + 2 + |z| + W (i' + 1) + m + G + j` is the linear
expression once the side condition rules out underflow of `i'`. -/
theorem tabSrc_toBitSrc {n : ℕ} {z : List Bool} {i : ℕ} {ρ : Fin 11 → ℕ} (hn : ρ rNC = n)
    (hz : ρ rZ = z.length) (s : SSrc M.k) (hok : s.Ok ρ)
    (hv : (s.toBitSrc ρ).Valid (z.length + n) (cfgWidth M) i) :
    tabSrc (cfgArity M) (cfgWidth M) (cfgF M) n z i (s.toBitSrc ρ) = (s.toLinE M).val ρ := by
  unfold tabSrc; rw [if_pos hv]
  cases s with
  | cst b => cases b <;> simp [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, hn]
  | zin =>
    simp only [SSrc.Ok] at hok
    simp only [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, ← hz, if_pos hok]
    simp [hn]; omega
  | uin =>
    simp only [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, ← hz]
    simp
  | prv d j =>
    simp only [SSrc.Ok] at hok
    simp only [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, tabBase, List.map_cons,
      List.map_replicate, List.sum_cons, List.sum_replicate_nat, hn, hz]
    rw [show ρ rQ + d - 1 + 1 = ρ rQ + d by omega, Nat.mul_add]; ring
  | cur j =>
    simp only [SSrc.Ok] at hok
    simp only [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, tabBase, List.map_cons,
      List.map_replicate, List.sum_cons, List.sum_replicate_nat, hn, hz]
    rw [show ρ rI - 1 + 1 = ρ rI by omega]; ring
  | psn j =>
    simp only [SSrc.Ok] at hok
    simp only [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, tabBase, List.map_cons,
      List.map_replicate, List.sum_cons, List.sum_replicate_nat, hn, hz]
    rw [show ρ rLB - 1 + 1 = ρ rLB by omega]; ring
  | cend τ j =>
    simp only [SSrc.toBitSrc, SSrc.toLinE, CounterProg.LinE.val, tabBase, List.map_cons,
      List.map_append, List.map_replicate, List.sum_cons, List.sum_append, List.sum_replicate,
      hn, hz]
    rw [show ρ rLB + (τ + 1) * (2 * ρ rT + 1) - 1 + 1 = ρ rLB + (τ + 1) * (2 * ρ rT + 1) by
      have : 0 < (τ + 1) * (2 * ρ rT + 1) := Nat.mul_pos (by omega) (by omega)
      omega]
    ring

/-! ## The symbolic sources of the tableau instructions -/

/-- A neighbour one step earlier if `ok`, else the constant `0`. -/
def nbS (ok : Bool) (d : Fin 3) (j : ℕ) : SSrc k := if ok then .prv d j else .cst false

/-- The previous instruction if `ok`, else the constant `0`. -/
def chS (ok : Bool) (j : ℕ) : SSrc k := if ok then .cur j else .cst false

/-- The previous snapshot's bits (constants at the first step). -/
def psnS (W : ℕ) (t0 : Bool) : List (SSrc k) :=
  (List.range W).map fun j => if t0 then .cst false else .psn j

/-- Pad a symbolic source list with constants to `m` entries. -/
def padS (m : ℕ) (l : List (SSrc k)) : List (SSrc k) := l ++ List.replicate (m - l.length) (.cst
    false)

/-- The symbolic sources of a work cell, mirroring `Complexity.cellSrcs`: flags "first step",
"not the leftmost cell", "the origin", "not the rightmost cell". -/
def cellS (W : ℕ) (t0 rlo rT rhi : Bool) : List (SSrc k) :=
  [.cst t0, .cst rT, nbS (!t0 && rlo) 0 0, nbS (!t0 && rlo) 0 1, nbS (!t0 && rlo) 0 2,
    nbS (!t0) 1 0, nbS (!t0) 1 1, nbS (!t0) 1 2,
    nbS (!t0 && rhi) 2 0, nbS (!t0 && rhi) 2 1, nbS (!t0 && rhi) 2 2,
    chS rlo 3, chS rlo 4] ++ psnS W t0

/-- The layout source of an input position: none, the hard-wired part, or the free part. -/
def layS : Fin 3 → SSrc k
  | 0 => .cst false
  | 1 => .zin
  | 2 => .uin

/-- The symbolic sources of an input position, mirroring `Complexity.inpSrcs`: flags "first
step", "position `0`", "position `1`", "the right end". -/
def inpS (W : ℕ) (t0 p0 p1 pN1 : Bool) (lay : Fin 3) : List (SSrc k) :=
  [.cst t0, .cst p1, .cst p0, .cst pN1, .cst (!p0 && !pN1), layS lay,
    nbS (!t0 && !p0) 0 0, nbS (!t0) 1 0, nbS (!t0 && !pN1) 2 0, chS (!p0) 1, chS (!p0) 2] ++
    psnS W t0

/-- The symbolic sources of a snapshot, mirroring `Complexity.snapSrcs`. -/
def snapS (W : ℕ) (t0 : Bool) : List (SSrc k) :=
  [.cst t0, if t0 then .cst false else .psn W, .cur 1, .cur 2] ++
    (List.finRange k).flatMap (fun τ => [.cend τ 3, .cend τ 4]) ++ psnS W t0

/-- Padding commutes with denotation. -/
theorem padS_toBitSrc (m : ℕ) (l : List (SSrc k)) (ρ : Fin 11 → ℕ) :
    (padS m l).map (SSrc.toBitSrc ρ) =
      l.map (SSrc.toBitSrc ρ) ++ List.replicate (m - (l.map (SSrc.toBitSrc ρ)).length)
        (.const false) := by
  simp [padS, List.map_replicate, SSrc.toBitSrc]

variable (M : FinTM Bool)

/-- The previous-snapshot sources, symbolically: at a step `t ≥ 1` the previous snapshot is
instruction `LB − 1`. -/
theorem psnS_toBitSrc {N T t : ℕ} (ℓ : List BitSrc) (hℓ : ℓ.length = N) {ρ : Fin 11 → ℕ}
    (hLB : ρ rLB = t * cfgStride M N T) :
    (psnS (k := M.k) (snapWidth M) (decide (t = 0))).map (SSrc.toBitSrc ρ) =
      prevSnapSrcs M ℓ T t := by
  apply List.ext_getElem (by simp [psnS, prevSnapSrcs])
  intro j h1 h2
  simp only [psnS, prevSnapSrcs, List.getElem_map, List.getElem_range]
  by_cases ht : t = 0
  · simp [ht, SSrc.toBitSrc]
  · simp only [ht, decide_false, Bool.false_eq_true, if_false, SSrc.toBitSrc, hLB, hℓ]
    congr 1
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [snapIdx, cfgStride, Nat.add_sub_cancel, Nat.succ_mul]
    omega

/-- **The symbolic sources of a work cell denote its sources** (`Complexity.cellSrcs`), when
the registers point at the cell (`I`), the same cell one step earlier (`Q`), and the
layer's start (`LB`).

**Proof sketch.** Case split on the first step and the leftmost/rightmost cell; each
neighbour block index `cellIdx (t − 1) τ (r ± 1)` is `Q ± 1`, the left block is `I − 1`
and the previous snapshot is `LB − 1` (`psnS_toBitSrc`). -/
theorem cellS_toBitSrc {N T t r : ℕ} {τ : Fin M.k} (ℓ : List BitSrc) (hℓ : ℓ.length = N)
    {ρ : Fin 11 → ℕ} (hI : ρ rI = cellIdx M N T t τ r)
    (hQ : t ≠ 0 → ρ rQ = cellIdx M N T (t - 1) τ r) (hLB : ρ rLB = t * cfgStride M N T) :
    (cellS (k := M.k) (snapWidth M) (decide (t = 0)) (decide (1 ≤ r)) (decide (r = T))
      (decide (r + 1 < 2 * T + 1))).map (SSrc.toBitSrc ρ) = cellSrcs M ℓ T t τ r := by
  rw [cellS, List.map_append, psnS_toBitSrc M ℓ hℓ hLB, cellSrcs]
  congr 1
  subst hℓ
  simp only [cellIdx] at hI hQ
  by_cases ht : t = 0
  · subst ht
    by_cases hr0 : r = 0
    · subst hr0
      simp [nbS, nbSrc, chS, chSrc, SSrc.toBitSrc]
    · simp [nbS, nbSrc, chS, chSrc, SSrc.toBitSrc, hr0, show 1 ≤ r by omega, hI, cellIdx]
      omega
  · have hQ' := hQ ht
    rcases Nat.lt_or_ge r (2 * T) with hrT | hrT
    · by_cases hr0 : r = 0
      · subst hr0
        simp [nbS, nbSrc, chS, chSrc, SSrc.toBitSrc, ht, hQ', cellIdx, hrT]
      · simp [nbS, nbSrc, chS, chSrc, SSrc.toBitSrc, ht, hr0, show 1 ≤ r by omega, hQ', hI,
          cellIdx, hrT]
        repeat' constructor
        all_goals omega
    · have hrT' : ¬ r < 2 * T := by omega
      by_cases hr0 : r = 0
      · subst hr0
        simp [nbS, nbSrc, chS, chSrc, SSrc.toBitSrc, ht, hQ', cellIdx, hrT']
      · simp [nbS, nbSrc, chS, chSrc, SSrc.toBitSrc, ht, hr0, show 1 ≤ r by omega, hQ', hI,
          cellIdx, hrT']
        repeat' constructor
        all_goals omega

/-- **The symbolic sources of an input position denote its sources** (`Complexity.inpSrcs`),
given the layout source of the position.

**Proof sketch.** As for `cellS_toBitSrc`, with a case split on the first step, position
`0` and the right end: `inpIdx (t − 1) (p ± 1) = Q ± 1`, `inpIdx t (p − 1) = I − 1`. -/
theorem inpS_toBitSrc {N T t p : ℕ} (ℓ : List BitSrc) (hℓ : ℓ.length = N) (hp : p < N + 2)
    {ρ : Fin 11 → ℕ} (hI : ρ rI = inpIdx M N T t p) (hQ : t ≠ 0 → ρ rQ = inpIdx M N T (t - 1) p)
    (hLB : ρ rLB = t * cfgStride M N T) (lay : Fin 3)
    (hlay : (layS (k := M.k) lay).toBitSrc ρ =
      if 1 ≤ p ∧ p ≤ N then ℓ.getD (p - 1) (.const false) else .const false) :
    (inpS (k := M.k) (snapWidth M) (decide (t = 0)) (decide (p = 0)) (decide (p = 1))
      (decide (p = N + 1)) lay).map (SSrc.toBitSrc ρ) = inpSrcs M ℓ T t p := by
  rw [inpS, List.map_append, psnS_toBitSrc M ℓ hℓ hLB, inpSrcs]
  congr 1
  subst hℓ
  simp only [inpIdx] at hI hQ
  have hmid : (!decide (p = 0) && !decide (p = ℓ.length + 1)) =
      decide (1 ≤ p ∧ p ≤ ℓ.length) := by
    by_cases h1 : p = 0 <;> by_cases h2 : p = ℓ.length + 1 <;> simp [h1, h2]; omega
  simp only [List.map_cons, List.map_nil, hmid, hlay]
  by_cases ht : t = 0
  · subst ht
    by_cases hp0 : p = 0
    · subst hp0
      simp [nbS, ihSrc, chS, ichSrc, SSrc.toBitSrc]
    · simp [nbS, ihSrc, chS, ichSrc, SSrc.toBitSrc, hp0, hI, inpIdx]
      omega
  · have hQ' := hQ ht
    by_cases hp0 : p = 0
    · subst hp0
      simp [nbS, ihSrc, chS, ichSrc, SSrc.toBitSrc, ht, hQ', inpIdx]
    · by_cases hpN : p = ℓ.length + 1
      · simp [nbS, ihSrc, chS, ichSrc, SSrc.toBitSrc, ht, hpN, hQ', inpIdx]
        omega
      · simp [nbS, ihSrc, chS, ichSrc, SSrc.toBitSrc, ht, hp0, hpN, hQ', hI, inpIdx,
          show 1 ≤ p by omega, show p ≤ ℓ.length by omega]
        repeat' constructor
        all_goals omega

/-- **The symbolic sources of a snapshot denote its sources** (`Complexity.snapSrcs`):
under a register assignment `ρ` whose index, time-bound and layer-base registers hold the
snapshot index, `T` and `t · cfgStride`, denoting each symbolic source of step `t`'s
snapshot gives exactly the concrete source list `snapSrcs M ℓ T t`.

**Proof sketch.** Both lists are concatenations of the same three pieces, so compare them
piecewise. The trailing previous-snapshot piece is the separate lemma for `psnS`. In the
head, the step-zero flag and the previous-snapshot pointer are checked separately for
`t = 0` and `t = t' + 1`, unfolding the index arithmetic of the snapshot layout. For the
per-tape head-cell bits, the register expression for tape `τ`'s cell evaluates to the
cell index at position `2T`, which is linear arithmetic on the layout strides. -/
theorem snapS_toBitSrc {N T t : ℕ} (ℓ : List BitSrc) (hℓ : ℓ.length = N) {ρ : Fin 11 → ℕ}
    (hI : ρ rI = snapIdx M N T t) (hT : ρ rT = T) (hLB : ρ rLB = t * cfgStride M N T) :
    (snapS (k := M.k) (snapWidth M) (decide (t = 0))).map (SSrc.toBitSrc ρ) =
      snapSrcs M ℓ T t := by
  rw [snapS, List.map_append, List.map_append, psnS_toBitSrc M ℓ hℓ hLB, snapSrcs]
  subst hℓ
  congr 2
  · simp only [snapIdx] at hI
    by_cases ht : t = 0
    · subst ht
      simp [SSrc.toBitSrc, hI, inpIdx]
      omega
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      simp [SSrc.toBitSrc, hI, hLB, inpIdx, snapIdx, cfgStride, Nat.succ_mul]
      omega
  · rw [List.map_flatMap]
    apply List.flatMap_congr
    intro τ _
    have h : ρ rLB + (↑τ + 1) * (2 * ρ rT + 1) - 1 = cellIdx M ℓ.length T t τ (2 * T) := by
      rw [hLB, hT, cellIdx, Nat.add_mul, Nat.one_mul]; omega
    simp [SSrc.toBitSrc, h]

end UTab

end Complexity
