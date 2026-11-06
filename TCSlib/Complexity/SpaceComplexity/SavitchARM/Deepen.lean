/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Window
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Savitch's search by iterative deepening

Savitch's register machine (`Complexity.LogProg.SavitchARM.A`) decides membership by midpoint
reachability over the configuration codes at a radius `s` that bounds the decider's space. When
the space bound `sp` is not computable, the radius is found by **iterative deepening**
([Sip13, §8.1, proof of Theorem 8.5]): this file builds one register machine `D` that, at
`s = 1, 2, …`, runs Savitch's search twice as a block of its own table
(`Complexity.LogProg.Ins.embed`):

* the **edge block** asks whether a configuration with a work head on the window's edge `±s` is
  reachable; if so, the space bound exceeds `s`, and `D` tries `s + 1`;
* otherwise the **accept block** asks whether an accepting configuration is reachable at radius
  `s`, which is membership (window exactness, `Complexity.LogProg.SavitchARM.mem_iff_reach_of_noEdge`).

The loop stops by `s = sp |x| + 1` (`Complexity.LogProg.SavitchARM.noEdge_of_lt`). The code
width is `w = (codeK N + 1) · (s + ℓ + 1)`, where `ℓ` exceeds the binary length of `|x|` by one
(`D` computes it by halving `|x|`), so every register stays below `2 ^ (W · W)` for the largest
width `W`, which is `O(sp |x| + logSpace |x| + 1)`. This is the hypothesis of
`Complexity.LogProg.arm_decides_SPACE`, and with it Savitch's theorem for every space bound
`S ≥ logSpace` ([AB09, Theorem 4.14]; `Complexity.savitch_of_logSpace_le`).

## Main definitions

* `Complexity.LogProg.SavitchARM.DeepenContract` — a register machine with logspace deciders
  that answers membership with registers of `O((sp |x| + logSpace |x| + 1)²)` digits.

## Main results

* `Complexity.LogProg.SavitchARM.deepen_contract` — the deepening machine meets the contract.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
* [Sav70] W. J. Savitch, *Relationships between nondeterministic and
  deterministic tape complexities*, JCSS 4(2), 1970. (Cited through [AB09].)
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning,
  2013. (§8.1, the proof of Theorem 8.5: the space bound found by trying `1, 2, …`.)
-/

namespace Complexity.LogProg.SavitchARM

open Turing Codec

/-- **The deepening machine's contract** for `L` and the space bound `sp`: some register machine
`D`, with logspace deciders `As` as its oracle, halts on every input `x` from the label `l₀` and
the zero register file with the answer `x ∈ L`, along a run whose every register has at most
`C · (sp |x| + logSpace |x| + 1)²` binary digits. It is the hypothesis of
`Complexity.LogProg.arm_decides_SPACE`. -/
def DeepenContract (L : Language Bool) (sp : ℕ → ℕ) : Prop :=
  ∃ (m d : ℕ) (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (D : ARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool), (∀ j, As j ∈ LOGSPACE) ∧ ∃ C : ℕ, ∀ x : List Bool,
      AHalt D (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => PreS D x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤
          C * (sp x.length + logSpace x.length + 1) ^ 2)
        (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)

/-! ## The machine

`D` has 25 registers. Registers `0 … 17` hold the search block (`dpρ`: the block's register `r`
is `D`'s register `r`); `D`'s own registers are `18` (`T`, the sum `s + ℓ + 1`), `19` (`W`, the
width), `20` (`C`, a shift counter), `21` (`N`, the input length), `22` (`ℓ`), `23` (`s`) and
`24` (`Z`, the loops' scratch register, always `0` between loops). -/

/-- The labels of the deepening machine for `c` copies of the width step: the two search blocks
(`eb`, `ab`), the setup (`scan` … `sOne`), the block preparation for block `f` (`cb` … `zM`;
`f = false` the edge block, `f = true` the accept block), the next radius (`nxt`) and the
answer (`fin`). -/
private inductive DpLb (c : ℕ) where
  | eb (l : Lb 0)
  | ab (l : Lb 0)
  | scan
  | incN
  | lInc
  | hz
  | hh
  | hi
  | sOne
  | cb (f : Bool) (i : Fin 21)
  | cS (f : Bool) (j : Fin 7)
  | cL (f : Bool) (j : Fin 7)
  | tInc (f : Bool)
  | cT (f : Bool) (i : Fin c) (j : Fin 7)
  | bS (f : Bool) (j : Fin 7)
  | zW (f : Bool)
  | bW (f : Bool) (j : Fin 7)
  | zK (f : Bool)
  | kOne (f : Bool)
  | cC (f : Bool) (j : Fin 7)
  | sh (f : Bool) (j : Fin 9)
  | zU (f : Bool)
  | zV (f : Bool)
  | zM (f : Bool)
  | nxt
  | fin (b : Bool)
  deriving DecidableEq, Fintype

/-- The block's registers inside `D`. -/
private def dpρ : Fin 18 → Fin 25 := Fin.castLE (by omega)

private theorem dpρ_inj : Function.Injective dpρ := Fin.castLE_injective _

private theorem dpρ_ne (r : Fin 18) {r' : Fin 25} (h : 18 ≤ r'.val) : dpρ r ≠ r' := fun e => by
  have h1 : (dpρ r).val = r.val := rfl
  have := r.isLt
  rw [e] at h1
  omega

/-- A copy loop of `D`: `b += a` through the scratch register `24`, exiting at `ex`. -/
private def dpCopyI {c : ℕ} (a b : Fin 25) (ex : DpLb c) (k : Fin 7 → DpLb c) :
    Fin 7 → Ins 25 5 (DpLb c) :=
  ![.jz a (k 4) (k 1), .dec a (k 2), .inc b (k 3), .inc 24 (k 0), .jz 24 ex (k 5),
    .dec 24 (k 6), .inc a (k 4)]

/-- The shift loop of `D`: the block's `rK` times `2 ^ C`, through the scratch register. -/
private def dpShlI {c : ℕ} (ex : DpLb c) (k : Fin 9 → DpLb c) : Fin 9 → Ins 25 5 (DpLb c) :=
  ![.jz 20 ex (k 1), .dec 20 (k 2), .jz (dpρ rK) (k 6) (k 3), .dec (dpρ rK) (k 4), .inc 24 (k 5),
    .inc 24 (k 2), .jz 24 (k 0) (k 7), .dec 24 (k 8), .inc (dpρ rK) (k 6)]

/-- The successor of the `i`-th register clear. -/
private def dpCbEx {c : ℕ} (f : Bool) (i : Fin 21) : DpLb c :=
  if h : i.val + 1 < 21 then .cb f ⟨i.val + 1, h⟩ else .cS f 0

/-- The successor of the `i`-th width copy. -/
private def dpCtEx {c : ℕ} (f : Bool) (i : Fin c) : DpLb c :=
  if h : i.val + 1 < c then .cT f ⟨i.val + 1, h⟩ 0 else .bS f 0

/-- The first width copy. -/
private def dpCt0 {c : ℕ} (f : Bool) : DpLb c :=
  if h : 0 < c then .cT f ⟨0, h⟩ 0 else .bS f 0

/-- The entry of block `f`. -/
private def dpIn {c : ℕ} : Bool → DpLb c
  | false => .eb .OU
  | true => .ab .OU

/-- The edge block's exits: an edge code is reachable (`true`, next radius) or not (`false`,
prepare the accept block). -/
private def dpkE {c : ℕ} : Bool → DpLb c
  | true => .nxt
  | false => .cb true 0

/-- The edge block's rerouting: decider `2` of the search reads the edge language. -/
private def dpσE : Fin 4 → Fin 5 := ![0, 1, 4, 3]

/-- The accept block's rerouting: the identity on `0 … 3`. -/
private def dpσA : Fin 4 → Fin 5 := ![0, 1, 2, 3]

/-- **The deepening machine** with `c` copies of the width step. -/
private def dpD (c : ℕ) : ARM 25 5 (DpLb c)
  | .eb l => (A 0 l).embed dpρ dpσE .eb dpkE 24
  | .ab l => (A 0 l).embed dpρ dpσA .ab .fin 24
  | .scan => .call 0 .whole [21] .incN .lInc
  | .incN => .inc 21 .scan
  | .lInc => .inc 22 .hz
  | .hz => .jz 21 .sOne .hh
  | .hh => .half 21 .hi
  | .hi => .inc 22 .hz
  | .sOne => .inc 23 (.cb false 0)
  | .cb f i => .clr ⟨i.val, by omega⟩ (dpCbEx f i)
  | .cS f j => dpCopyI 23 18 (.cL f 0) (.cS f) j
  | .cL f j => dpCopyI 22 18 (.tInc f) (.cL f) j
  | .tInc f => .inc 18 (dpCt0 f)
  | .cT f i j => dpCopyI 18 19 (dpCtEx f i) (.cT f i) j
  | .bS f j => dpCopyI 23 (dpρ rs) (.zW f) (.bS f) j
  | .zW f => .clr (dpρ rw) (.bW f 0)
  | .bW f j => dpCopyI 19 (dpρ rw) (.zK f) (.bW f) j
  | .zK f => .clr (dpρ rK) (.kOne f)
  | .kOne f => .inc (dpρ rK) (.cC f 0)
  | .cC f j => dpCopyI 19 20 (.sh f 0) (.cC f) j
  | .sh f j => dpShlI (.zU f) (.sh f) j
  | .zU f => .clr (dpρ rU) (.zV f)
  | .zV f => .clr (dpρ rV) (.zM f)
  | .zM f => .clr (dpρ rM) (dpIn f)
  | .nxt => .inc 23 (.cb false 0)
  | .fin b => .ret b

/-! ## The deciders and the oracle bridges -/

/-- The deciders of the deepening machine. -/
private def dpAs (N : FinNDTM Bool) : Fin 5 → Language Bool :=
  ![inputLenLang, initLang N, acceptLang N, stepLang N, edgeLang N]

/-- Their answers. -/
private noncomputable def dpOrc (N : FinNDTM Bool) : Fin 5 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (dpAs N j : Set (List Bool)) V

private theorem dp_mem (N : FinNDTM Bool) (j : Fin 5) (V : List Bool) :
    dpOrc N j V = true ↔ V ∈ dpAs N j := by
  rw [dpOrc, indicator_eq_decide]
  exact ⟨fun h => @of_decide_eq_true _ (Classical.dec _) h,
    fun h => @decide_eq_true _ (Classical.dec _) h⟩

private theorem dp_rel (N : FinNDTM Bool) (σ : Fin 4 → Fin 5) (hσ : σ 3 = 3) (x : List Bool)
    (s : ℕ) : Rel (dpOrc N ∘ σ) x s = StepRel N x s := by
  funext u v
  apply propext
  rw [rel_iff_orc, stepRel_iff_mem, Function.comp_apply, hσ, dp_mem]
  rfl

private theorem dp_initO (N : FinNDTM Bool) (σ : Fin 4 → Fin 5) (hσ : σ 1 = 1) (x : List Bool)
    (s u : ℕ) : InitO (dpOrc N ∘ σ) x s u ↔
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N := by
  rw [initO_iff_orc, Function.comp_apply, hσ, dp_mem]
  rfl

private theorem dp_accO (N : FinNDTM Bool) (σ : Fin 4 → Fin 5) (j : Fin 5) (hσ : σ 2 = j)
    (x : List Bool) (s v : ℕ) : AccO (dpOrc N ∘ σ) x s v ↔
      pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ dpAs N j := by
  rw [accO_iff_orc, Function.comp_apply, hσ, dp_mem]

/-! ## Single steps of `D`'s own instructions -/

section Steps

variable {c : ℕ} {o : Fin 5 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- `D`'s own increments, clears and answers meet the syntactic preconditions. -/
private theorem dp_pre {l : DpLb c} {v : Fin 25 → ℕ}
    (h : (∃ r l', dpD c l = .inc r l') ∨ (∃ r l', dpD c l = .clr r l') ∨
      (∃ b, dpD c l = .ret b)) : PreS (dpD c) x (some l, v, none) := by
  rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;>
    exact preS_of_ins (by intros; simp_all) (by intros; simp_all) (by intros; simp_all)
      (by intros; simp_all) (by intros; simp_all)

private theorem dp_inc {l l' : DpLb c} {r : Fin 25} (h : dpD c l = .inc r l') {v : Fin 25 → ℕ}
    (hv : ∀ s, v s ≤ B) : AReach (dpD c) o x (GuardLe (dpD c) x B) (some l, v, none)
      (some l', Function.update v r (v r + 1), none) :=
  AReach.step ⟨dp_pre (Or.inl ⟨r, l', h⟩), hv⟩ (by rw [astep_inc h]; exact AReach.refl _)

private theorem dp_clr {l l' : DpLb c} {r : Fin 25} (h : dpD c l = .clr r l') {v : Fin 25 → ℕ}
    (hv : ∀ s, v s ≤ B) : AReach (dpD c) o x (GuardLe (dpD c) x B) (some l, v, none)
      (some l', Function.update v r 0, none) :=
  AReach.step ⟨dp_pre (Or.inr (Or.inl ⟨r, l', h⟩)), hv⟩ (by rw [astep_clr h]; exact AReach.refl _)

end Steps

/-! ## The register file

Between loops `D`'s register file is `dpSt b o`: the block's registers `b` and `D`'s own
registers `o` (`o i` is register `18 + i`). -/

/-- `D`'s register file from its block part and its own part. -/
private def dpSt (b : Fin 18 → ℕ) (o : Fin 7 → ℕ) : Fin 25 → ℕ :=
  fun r => if h : r.val < 18 then b ⟨r.val, h⟩ else o ⟨r.val - 18, by omega⟩

private theorem dpSt_ρ (b : Fin 18 → ℕ) (o : Fin 7 → ℕ) (r : Fin 18) :
    dpSt b o (dpρ r) = b r := by
  simp only [dpSt]
  rw [dif_pos (show (dpρ r).val < 18 from r.isLt)]
  rfl

private theorem dpSt_own (b : Fin 18 → ℕ) (o : Fin 7 → ℕ) (r : Fin 25) (i : Fin 7)
    (h : r.val = 18 + i.val) : dpSt b o r = o i := by
  simp only [dpSt]
  rw [dif_neg (by omega)]
  exact congrArg o (Fin.ext (by dsimp only; omega))

private theorem dpSt_upd_ρ (b : Fin 18 → ℕ) (o : Fin 7 → ℕ) (r : Fin 18) (a : ℕ) :
    Function.update (dpSt b o) (dpρ r) a = dpSt (Function.update b r a) o := by
  funext r'
  simp only [dpSt, Function.update_apply]
  by_cases h : r'.val < 18
  · rw [dif_pos h, dif_pos h]
    have e : (r' = dpρ r) ↔ ((⟨r'.val, h⟩ : Fin 18) = r) := by
      rw [Fin.ext_iff, Fin.ext_iff]
      rfl
    simp only [e]
  · rw [dif_neg h, dif_neg h, if_neg]
    intro e
    exact h (by rw [e]; exact r.isLt)

private theorem dpSt_upd_own (b : Fin 18 → ℕ) (o : Fin 7 → ℕ) (r : Fin 25) (i : Fin 7)
    (h : r.val = 18 + i.val) (a : ℕ) :
    Function.update (dpSt b o) r a = dpSt b (Function.update o i a) := by
  funext r'
  simp only [dpSt, Function.update_apply]
  by_cases h' : r'.val < 18
  · rw [dif_pos h', dif_pos h', if_neg]
    intro e
    rw [e] at h'
    omega
  · rw [dif_neg h', dif_neg h']
    have e : (r' = r) ↔ ((⟨r'.val - 18, by omega⟩ : Fin 7) = i) := by
      rw [Fin.ext_iff, Fin.ext_iff]
      dsimp only
      omega
    simp only [e]

private theorem dpSt_bd {B : ℕ} {b : Fin 18 → ℕ} {o : Fin 7 → ℕ} (hb : ∀ r, b r ≤ B)
    (ho : ∀ i, o i ≤ B) : ∀ r, dpSt b o r ≤ B := fun r => by
  simp only [dpSt]
  split_ifs
  exacts [hb _, ho _]

/-- After a block's run, every register is at most `B`: the block's by the block's bound, the
others unchanged. -/
private theorem dp_bd_blk {B M : ℕ} {v₂ v' : Fin 25 → ℕ}
    (f1 : ∀ r', (∀ r, dpρ r ≠ r') → v₂ r' = v' r') (f2 : ∀ r, v₂ (dpρ r) ≤ M) (hM : M ≤ B)
    (hv : ∀ r, v' r ≤ B) : ∀ r, v₂ r ≤ B := fun r' => by
  by_cases h : r'.val < 18
  · have e : r' = dpρ ⟨r'.val, h⟩ := rfl
    rw [e]
    exact (f2 _).trans hM
  · rw [f1 r' (fun r e => h (by rw [← e]; exact r.isLt))]
    exact hv r'

/-! ## `D`'s loops -/

section Loops

variable {c : ℕ} {o : Fin 5 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- A copy loop of `D` (`copy_run`). -/
private theorem dp_copy {src dst : Fin 25} {ex : DpLb c} {k : Fin 7 → DpLb c}
    (hk : ∀ j, dpD c (k j) = dpCopyI src dst ex k j) (h1 : src ≠ dst) (h2 : src ≠ 24)
    (h3 : dst ≠ 24) {v : Fin 25 → ℕ} (hZ : v 24 = 0) (hv : ∀ s, v s ≤ B)
    (hb : v dst + v src ≤ B) :
    AReach (dpD c) o x (GuardLe (dpD c) x B) (some (k 0), v, none)
      (some ex, Function.update v dst (v dst + v src), none) :=
  copy_run h1 h2 h3 (hk 0) (hk 1) (hk 2) (hk 3) (hk 4) (hk 5) (hk 6) v hZ hv hb

/-- The shift loop of `D` (`shl_run`). -/
private theorem dp_shl {ex : DpLb c} {k : Fin 9 → DpLb c} (hk : ∀ j, dpD c (k j) = dpShlI ex k j)
    {v : Fin 25 → ℕ} (hZ : v 24 = 0) (hv : ∀ s, v s ≤ B) (hb : v (dpρ rK) * 2 ^ v 20 ≤ B) :
    AReach (dpD c) o x (GuardLe (dpD c) x B) (some (k 0), v, none)
      (some ex, Function.update (Function.update v 20 0) (dpρ rK) (v (dpρ rK) * 2 ^ v 20),
        none) :=
  shl_run (dpρ_ne rK (by decide)).symm (by decide) (dpρ_ne rK (by decide)) (hk 0) (hk 1) (hk 2)
    (hk 3) (hk 4) (hk 5) (hk 6) (hk 7) (hk 8) _ v rfl hZ hv hb

/-- **The register clears**: from the `i`-th clear, registers `i … 20` become `0`.

**Proof sketch.** Induction on the number of clears left; each clears one register. -/
private theorem dp_cb_run (f : Bool) : ∀ j i (hi : i < 21), i + j = 20 → ∀ v : Fin 25 → ℕ,
    (∀ r, v r ≤ B) → AReach (dpD c) o x (GuardLe (dpD c) x B) (some (.cb f ⟨i, hi⟩), v, none)
      (some (.cS f 0), fun r => if i ≤ r.val ∧ r.val < 21 then 0 else v r, none) := by
  intro j
  induction j with
  | zero =>
    intro i hi hij v hv
    have r1 := dp_clr (c := c) (o := o) (x := x) (l := .cb f ⟨i, hi⟩) rfl hv
    rw [show dpCbEx (c := c) f ⟨i, hi⟩ = .cS f 0 from dif_neg (by show ¬ i + 1 < 21; omega)]
      at r1
    refine reach_of_eq r1 ?_
    congr 2
    funext r
    simp only [Function.update_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | omega
  | succ j ih =>
    intro i hi hij v hv
    have r1 := dp_clr (c := c) (o := o) (x := x) (l := .cb f ⟨i, hi⟩) rfl hv
    rw [show dpCbEx (c := c) f ⟨i, hi⟩ = .cb f ⟨i + 1, by omega⟩ from
      dif_pos (by show i + 1 < 21; omega)] at r1
    refine r1.trans (reach_of_eq (ih (i + 1) (by omega) (by omega) _
      (register_update_le _ _ _ _ hv (Nat.zero_le _))) ?_)
    congr 2
    funext r
    simp only [Function.update_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | omega

/-- **The width copies**: from the `i`-th of the `c` copies, `W` gains `(c - i) · T`.

**Proof sketch.** Induction on the number of copies left; each is one `copy_run`. -/
private theorem dp_cT_run (f : Bool) : ∀ j i (hi : i < c), i + j + 1 = c → ∀ v : Fin 25 → ℕ,
    v 24 = 0 → (∀ r, v r ≤ B) → v 19 + (j + 1) * v 18 ≤ B →
    AReach (dpD c) o x (GuardLe (dpD c) x B) (some (.cT f ⟨i, hi⟩ 0), v, none)
      (some (.bS f 0), Function.update v 19 (v 19 + (j + 1) * v 18), none) := by
  intro j
  induction j with
  | zero =>
    intro i hi hij v hZ hv hb
    have r1 := dp_copy (o := o) (x := x) (k := DpLb.cT f ⟨i, hi⟩) (src := 18) (dst := 19)
      (fun _ => rfl) (by decide) (by decide) (by decide) hZ hv (by omega)
    rw [show dpCtEx f ⟨i, hi⟩ = .bS f 0 from dif_neg (by show ¬ i + 1 < c; omega)] at r1
    exact reach_of_eq r1 (by rw [zero_add, one_mul])
  | succ j ih =>
    intro i hi hij v hZ hv hb
    have r1 := dp_copy (o := o) (x := x) (k := DpLb.cT f ⟨i, hi⟩) (src := 18) (dst := 19)
      (fun _ => rfl) (by decide) (by decide) (by decide) hZ hv (by nlinarith)
    rw [show dpCtEx f ⟨i, hi⟩ = .cT f ⟨i + 1, by omega⟩ 0 from
      dif_pos (by show i + 1 < c; omega)] at r1
    have e18 : Function.update v 19 (v 19 + v 18) 18 = v 18 :=
      Function.update_of_ne (by decide) _ _
    refine r1.trans (reach_of_eq (ih (i + 1) (by omega) (by omega) _
      (by rw [Function.update_of_ne (by decide)]; exact hZ) (register_update_le _ _ _ _ hv (by nlinarith))
      (by rw [e18, Function.update_self]; nlinarith)) ?_)
    rw [e18, Function.update_self, Function.update_idem]
    congr 3
    ring

/-- The binary length against `logSpace`: `logSpace n ≤ 1 + |bits n| ≤ logSpace n + 1`, and
`n < 2 ^ |bits n|`. -/
private theorem dp_bits_logSpace (n : ℕ) : logSpace n ≤ 1 + (Nat.bits n).length ∧
    (Nat.bits n).length ≤ logSpace n ∧ n < 2 ^ (Nat.bits n).length := by
  have h2 : (Nat.bits n).length ≤ logSpace n :=
    (length_bits_le_log n).trans_eq (logSpace_eq n).symm
  rw [Nat.size_eq_bits_len] at h2 ⊢
  exact ⟨by have := logSpace_le_size_succ n; omega, h2, Nat.lt_size_self n⟩

end Loops

/-! ## The block preparation -/

/-- **The block preparation** at radius `s`: from `cb f 0`, `D` reaches block `f`'s entry
with the block's registers `setSt`'s and `outerSt`'s chain at radius `s` and width
`w = c · (s + ℓ + 1)`, and its own `ℓ`, `s` and scratch registers unchanged.

**Proof sketch.** Clear registers `0 … 20` (`dp_cb_run`); `T := s + ℓ + 1` (two copies and an
increment); `W := c · T` (`dp_cT_run`); then write the block's `rs := s`, `rw := w`,
`rK := 2 ^ w` (an increment and `shl_run`), `rU`, `rV`, `rM := 0`, each after clearing it, in
that order. Every value is at most `2 ^ w`. -/
private theorem dp_prep {c : ℕ} {o : Fin 5 → List Bool → Bool} {x : List Bool} {B : ℕ}
    (hc : 1 ≤ c) (f : Bool) {s ℓ : ℕ} (hB : 2 ^ (c * (s + ℓ + 1)) ≤ B) {v : Fin 25 → ℕ}
    (hL : v 22 = ℓ) (hS : v 23 = s) (hZ : v 24 = 0) (hv : ∀ r, v r ≤ B) :
    ∃ v', AReach (dpD c) o x (GuardLe (dpD c) x B) (some (.cb f 0), v, none)
        (some (dpIn f), v', none) ∧
      (∀ r, v' (dpρ r) = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (fun _ => 0) rs s) rw (c * (s + ℓ + 1))) rK
          (2 ^ (c * (s + ℓ + 1)))) rU 0) rV 0) rM 0 r) ∧
      v' 22 = ℓ ∧ v' 23 = s ∧ v' 24 = 0 ∧ ∀ r, v' r ≤ B := by
  have hw1 : s + ℓ + 1 ≤ c * (s + ℓ + 1) := Nat.le_mul_of_pos_left _ hc
  have hw2 : c * (s + ℓ + 1) < 2 ^ (c * (s + ℓ + 1)) := Nat.lt_two_pow_self
  generalize hw : c * (s + ℓ + 1) = w at hw1 hw2 hB
  have hwB : w ≤ B := by omega
  -- the clears
  have r1 := dp_cb_run (c := c) (o := o) (x := x) (B := B) f 20 0 (by omega) rfl v hv
  set o1 : Fin 7 → ℕ := fun i => if i.val < 3 then 0 else v ⟨18 + i.val, by omega⟩ with ho1
  have e1 : (fun r : Fin 25 => if 0 ≤ r.val ∧ r.val < 21 then 0 else v r) =
      dpSt (fun _ => 0) o1 := by
    funext r
    simp only [dpSt, ho1]
    by_cases h1 : r.val < 18
    · rw [dif_pos h1, if_pos ⟨Nat.zero_le _, by omega⟩]
    · rw [dif_neg h1]
      by_cases h2 : r.val < 21
      · rw [if_pos ⟨Nat.zero_le _, h2⟩, if_pos (show r.val - 18 < 3 by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (show ¬ r.val - 18 < 3 by omega)]
        exact congrArg v (Fin.ext (show r.val = 18 + (r.val - 18) by omega))
  rw [e1] at r1
  have o1L : o1 4 = ℓ := hL
  have o1S : o1 5 = s := hS
  have o1Z : o1 6 = 0 := hZ
  have o1b : ∀ i, o1 i ≤ B := fun i => by
    simp only [ho1]
    split_ifs
    exacts [Nat.zero_le _, hv _]
  have b0 : ∀ r : Fin 18, (fun _ => 0 : Fin 18 → ℕ) r ≤ B := fun _ => Nat.zero_le _
  -- `T := s`
  have r2 := dp_copy (c := c) (o := o) (x := x) (k := DpLb.cS f) (src := 23) (dst := 18) (fun _ => rfl)
    (by decide) (by decide) (by decide) (v := dpSt (fun _ => 0) o1)
    (by rw [dpSt_own _ _ 24 6 rfl]; exact o1Z) (dpSt_bd b0 o1b)
    (by rw [dpSt_own _ _ 18 0 rfl, dpSt_own _ _ 23 5 rfl, o1S]; exact (show (0 : ℕ) + s ≤ B by omega))
  rw [dpSt_own _ _ 18 0 rfl, dpSt_own _ _ 23 5 rfl, o1S, dpSt_upd_own _ _ 18 0 rfl,
    show o1 0 + s = s from by simp [ho1]] at r2
  -- `T := s + ℓ`
  set o2 := Function.update o1 0 s with ho2
  have o2b : ∀ i, o2 i ≤ B := register_update_le _ _ _ _ o1b (by omega)
  have r3 := dp_copy (c := c) (o := o) (x := x) (k := DpLb.cL f) (src := 22) (dst := 18) (fun _ => rfl)
    (by decide) (by decide) (by decide) (v := dpSt (fun _ => 0) o2)
    (by rw [dpSt_own _ _ 24 6 rfl, ho2, Function.update_of_ne (by decide)]; exact o1Z)
    (dpSt_bd b0 o2b)
    (by rw [dpSt_own _ _ 18 0 rfl, dpSt_own _ _ 22 4 rfl, ho2, Function.update_self,
      Function.update_of_ne (by decide), o1L]; omega)
  rw [dpSt_own _ _ 18 0 rfl, dpSt_own _ _ 22 4 rfl, dpSt_upd_own _ _ 18 0 rfl, ho2,
    Function.update_self, Function.update_of_ne (show (4 : Fin 7) ≠ 0 by decide), o1L,
    Function.update_idem] at r3
  -- `T := s + ℓ + 1`
  set o3 := Function.update o1 0 (s + ℓ) with ho3
  have o3b : ∀ i, o3 i ≤ B := register_update_le _ _ _ _ o1b (by omega)
  have r4 := dp_inc (c := c) (o := o) (x := x) (l := .tInc f) rfl (dpSt_bd b0 o3b)
  rw [dpSt_own _ _ 18 0 rfl, dpSt_upd_own _ _ 18 0 rfl, ho3, Function.update_self,
    Function.update_idem, show dpCt0 (c := c) f = .cT f ⟨0, hc⟩ 0 from dif_pos hc] at r4
  -- `W := c · T`
  set o4 := Function.update o1 0 (s + ℓ + 1) with ho4
  have o4b : ∀ i, o4 i ≤ B := register_update_le _ _ _ _ o1b (by omega)
  have o4T : o4 0 = s + ℓ + 1 := Function.update_self _ _ _
  have o4W : o4 1 = 0 := by rw [ho4, Function.update_of_ne (by decide)]; rfl
  have r5 := dp_cT_run (c := c) (o := o) (x := x) (B := B) f (c - 1) 0 hc (by omega)
    (dpSt (fun _ => 0) o4)
    (by rw [dpSt_own _ _ 24 6 rfl, ho4, Function.update_of_ne (by decide)]; exact o1Z)
    (dpSt_bd b0 o4b)
    (by rw [dpSt_own _ _ 18 0 rfl, dpSt_own _ _ 19 1 rfl, o4T, o4W,
      Nat.sub_add_cancel hc, hw]; omega)
  rw [dpSt_own _ _ 18 0 rfl, dpSt_own _ _ 19 1 rfl, o4T, o4W, Nat.sub_add_cancel hc, hw,
    zero_add, dpSt_upd_own _ _ 19 1 rfl] at r5
  -- the block's `rs := s`
  set o5 := Function.update o4 1 w with ho5
  have o5b : ∀ i, o5 i ≤ B := register_update_le _ _ _ _ o4b hwB
  have o5S : o5 5 = s := by
    rw [ho5, ho4, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact o1S
  have o5W : o5 1 = w := Function.update_self _ _ _
  have o5C : o5 2 = 0 := by
    rw [ho5, ho4, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    rfl
  have o5Z : o5 6 = 0 := by
    rw [ho5, ho4, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact o1Z
  have Z5 : ∀ b : Fin 18 → ℕ, dpSt b o5 24 = 0 := fun b => by
    rw [dpSt_own _ _ 24 6 rfl]; exact o5Z
  have r6 := dp_copy (c := c) (o := o) (x := x) (k := DpLb.bS f) (src := 23) (dst := dpρ rs)
    (fun _ => rfl) (dpρ_ne rs (by decide)).symm (by decide) (dpρ_ne rs (by decide)) (Z5 _)
    (dpSt_bd b0 o5b) (by rw [dpSt_ρ, dpSt_own _ _ 23 5 rfl, o5S]; show 0 + s ≤ B; omega)
  rw [dpSt_ρ, dpSt_own _ _ 23 5 rfl, o5S, dpSt_upd_ρ] at r6
  simp only [zero_add] at r6
  -- the block's `rw := w`
  set b1 : Fin 18 → ℕ := Function.update (fun _ => 0) rs s with hb1
  have b1b : ∀ r, b1 r ≤ B := register_update_le _ _ _ _ b0 (by omega)
  have r7 := dp_clr (c := c) (o := o) (x := x) (l := .zW f) rfl (dpSt_bd b1b o5b)
  rw [dpSt_upd_ρ] at r7
  have r8 := dp_copy (c := c) (o := o) (x := x) (k := DpLb.bW f) (src := 19) (dst := dpρ rw)
    (fun _ => rfl) (dpρ_ne rw (by decide)).symm (by decide) (dpρ_ne rw (by decide)) (Z5 _)
    (dpSt_bd (register_update_le _ rw _ _ b1b (Nat.zero_le _)) o5b)
    (by rw [dpSt_ρ, dpSt_own _ _ 19 1 rfl, o5W, Function.update_self]; omega)
  rw [dpSt_ρ, dpSt_own _ _ 19 1 rfl, o5W, Function.update_self, zero_add, dpSt_upd_ρ,
    Function.update_idem] at r8
  -- the block's `rK := 1`
  set b2 := Function.update b1 rw w with hb2
  have b2b : ∀ r, b2 r ≤ B := register_update_le _ _ _ _ b1b hwB
  have r9 := dp_clr (c := c) (o := o) (x := x) (l := .zK f) rfl (dpSt_bd b2b o5b)
  rw [dpSt_upd_ρ] at r9
  have r10 := dp_inc (c := c) (o := o) (x := x) (l := .kOne f) rfl
    (dpSt_bd (register_update_le _ rK _ _ b2b (Nat.zero_le _)) o5b)
  rw [dpSt_ρ, Function.update_self, zero_add, dpSt_upd_ρ, Function.update_idem] at r10
  -- `C := w`
  set b3 := Function.update b2 rK 1 with hb3
  have b3b : ∀ r, b3 r ≤ B := register_update_le _ _ _ _ b2b (by omega)
  have r11 := dp_copy (c := c) (o := o) (x := x) (k := DpLb.cC f) (src := 19) (dst := 20) (fun _ => rfl)
    (by decide) (by decide) (by decide) (Z5 _) (dpSt_bd b3b o5b)
    (by rw [dpSt_own _ _ 20 2 rfl, dpSt_own _ _ 19 1 rfl, o5W, o5C]; omega)
  rw [dpSt_own _ _ 20 2 rfl, dpSt_own _ _ 19 1 rfl, o5W, o5C, zero_add,
    dpSt_upd_own _ _ 20 2 rfl] at r11
  -- the block's `rK := 2 ^ w`
  set o6 := Function.update o5 2 w with ho6
  have o6b : ∀ i, o6 i ≤ B := register_update_le _ _ _ _ o5b hwB
  have r12 := dp_shl (c := c) (o := o) (x := x) (k := DpLb.sh f) (ex := .zU f) (fun _ => rfl)
    (v := dpSt b3 o6)
    (by rw [dpSt_own _ _ 24 6 rfl, ho6, Function.update_of_ne (by decide)]; exact o5Z)
    (dpSt_bd b3b o6b)
    (by rw [dpSt_ρ, dpSt_own _ _ 20 2 rfl, ho6, Function.update_self, hb3,
      Function.update_self, one_mul]; exact hB)
  rw [dpSt_ρ, dpSt_own _ _ 20 2 rfl, ho6, Function.update_self, hb3, Function.update_self,
    one_mul, dpSt_upd_own _ _ 20 2 rfl, dpSt_upd_ρ, Function.update_idem,
    Function.update_idem] at r12
  -- the block's `rU`, `rV`, `rM := 0`
  set b4 := Function.update b2 rK (2 ^ w) with hb4
  set o7 := Function.update o5 2 0 with ho7
  have b4b : ∀ r, b4 r ≤ B := register_update_le _ _ _ _ b2b hB
  have o7b : ∀ i, o7 i ≤ B := register_update_le _ _ _ _ o5b (Nat.zero_le _)
  have r13 := dp_clr (c := c) (o := o) (x := x) (l := .zU f) rfl (dpSt_bd b4b o7b)
  rw [dpSt_upd_ρ] at r13
  have r14 := dp_clr (c := c) (o := o) (x := x) (l := .zV f) rfl
    (dpSt_bd (register_update_le _ rU _ _ b4b (Nat.zero_le _)) o7b)
  rw [dpSt_upd_ρ] at r14
  have r15 := dp_clr (c := c) (o := o) (x := x) (l := .zM f) rfl
    (dpSt_bd (register_update_le _ rV _ _ (register_update_le _ rU _ _ b4b (Nat.zero_le _)) (Nat.zero_le _)) o7b)
  rw [dpSt_upd_ρ] at r15
  refine ⟨_, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans (r8.trans
    (r9.trans (r10.trans (r11.trans (r12.trans (r13.trans (r14.trans r15))))))))))))),
    fun r => dpSt_ρ _ _ r, ?_, ?_, ?_, dpSt_bd (register_update_le _ rM _ _ (register_update_le _ rV _ _ (register_update_le _ rU _ _ b4b (Nat.zero_le _))
      (Nat.zero_le _)) (Nat.zero_le _)) o7b⟩
  · rw [dpSt_own _ _ 22 4 rfl, ho7, ho5, ho4, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact o1L
  · rw [dpSt_own _ _ 23 5 rfl, ho7, Function.update_of_ne (by decide)]
    exact o5S
  · rw [dpSt_own _ _ 24 6 rfl, ho7, Function.update_of_ne (by decide)]
    exact o5Z

/-! ## The blocks -/

open Classical in
/-- **A block's fit**: entered at the outer search with the entry registers, the embedded
search exits through `k b`, where `b` says whether some initial code reaches some code of the
language `La` (decider `j`, through `σ 2 = j`) by midpoint reachability at radius `s` and
level `w`.

**Proof sketch.** The entry registers are
`(outerSt s w 0 0 0).toV` (`setSt_toV`, `outerSt_toV`), so one `AHalt.embed_guardLe` of
`outerU_run` (with `A_noVal`) runs the block to its exit; its answer is converted to the codec's
terms through `dp_rel`, `dp_initO` and `dp_accO` and `decide_eq_decide`. -/
private theorem dp_fit (N : FinNDTM Bool) {c : ℕ} (x : List Bool) (s w : ℕ) (hsw : s ≤ w)
    {σ : Fin 4 → Fin 5} (j : Fin 5) (La : Language Bool) (hj : dpAs N j = La) (h1 : σ 1 = 1)
    (h2 : σ 2 = j) (h3 : σ 3 = 3) {ι : Lb 0 → DpLb c} {k : Bool → DpLb c}
    (hD : ∀ l, dpD c (ι l) = (A 0 l).embed dpρ σ ι k 24) {B : ℕ} (hBB : 2 ^ (w * w) ≤ B)
    {v' : Fin 25 → ℕ} (he : ∀ r', v' r' ≤ B)
    (hv : ∀ r, v' (dpρ r) = Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (fun _ => 0) rs s) rw w) rK (2 ^ w))
        rU 0) rV 0) rM 0 r) :
    ∃ v₂', (∀ r', (∀ r, dpρ r ≠ r') → v₂' r' = v' r') ∧ (∀ r, v₂' (dpρ r) ≤ 2 ^ (w * w)) ∧
      AReach (dpD c) (dpOrc N) x (GuardLe (dpD c) x B) (some (ι .OU), v', none)
        (some (k (decide (∃ u < 2 ^ w, pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈
            initLang N ∧ ∃ v < 2 ^ w, pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈
              La ∧ Reach (2 ^ w) (StepRel N x s) w u v))), v₂', none) := by
  have hR : RegExt dpρ v' _ v' := ⟨hv, fun _ _ => rfl⟩
  rw [← setSt_toV, ← outerSt_toV] at hR
  have hrun := outerU_run (E := 0) (orc := dpOrc N ∘ σ) (x := x) hsw (2 ^ w) 0 0
    (by omega) (Nat.zero_le _)
  obtain ⟨v₂', e1, e2, e3⟩ := AHalt.embed_guardLe dpρ_inj hD (A_noVal 0) hBB he hrun hR
  have hiff : (∃ u', 0 ≤ u' ∧ u' < 2 ^ w ∧ InitO (dpOrc N ∘ σ) x s u' ∧
      ∃ v < 2 ^ w, AccO (dpOrc N ∘ σ) x s v ∧
        Reach (2 ^ w) (Rel (dpOrc N ∘ σ) x s) w u' v) ↔
      (∃ u < 2 ^ w, pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N ∧
        ∃ v < 2 ^ w, pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ La ∧
          Reach (2 ^ w) (StepRel N x s) w u v) := by
    rw [dp_rel N σ h3, ← hj]
    constructor
    · rintro ⟨u, -, hu, hi, v, hv, he, hr⟩
      exact ⟨u, hu, (dp_initO N σ h1 x s u).mp hi, v, hv, (dp_accO N σ j h2 x s v).mp he, hr⟩
    · rintro ⟨u, hu, hi, v, hv, he, hr⟩
      exact ⟨u, Nat.zero_le _, hu, (dp_initO N σ h1 x s u).mpr hi, v, hv,
        (dp_accO N σ j h2 x s v).mpr he, hr⟩
  rw [decide_eq_decide.mpr hiff] at e3
  exact ⟨v₂', e1, e2, e3⟩

/-! ## The deepening loop -/

section Loop

variable {c : ℕ} {B : ℕ}

open Classical in
/-- **A block at radius `s`**: from `cb f 0`, `D` prepares block `f` (`dp_prep`) and runs it
(`dp_fit`) to its exit `k b`, where `b` is the block's answer at radius `s` and width
`w = c · (s + ℓ + 1)`; `ℓ`, `s` and the scratch register are unchanged.

**Proof sketch.** `dp_prep` reaches the block's entry with the entry registers; `dp_fit` runs
the block; `D`'s own registers are off `ρ`'s range, so the block leaves them (`dpρ_ne`), and
every register stays at most `B` (`dp_bd_blk`). -/
private theorem dp_block (N : FinNDTM Bool) (hc : 1 ≤ c) (x : List Bool) {s ℓ : ℕ}
    (hBB : 2 ^ (c * (s + ℓ + 1) * (c * (s + ℓ + 1))) ≤ B) (f : Bool) {σ : Fin 4 → Fin 5}
    (j : Fin 5) (La : Language Bool) (hj : dpAs N j = La) (h1 : σ 1 = 1) (h2 : σ 2 = j)
    (h3 : σ 3 = 3) {ι : Lb 0 → DpLb c} {k : Bool → DpLb c}
    (hD : ∀ l, dpD c (ι l) = (A 0 l).embed dpρ σ ι k 24) (hι : dpIn (c := c) f = ι .OU)
    {v : Fin 25 → ℕ} (hL : v 22 = ℓ) (hS : v 23 = s) (hZ : v 24 = 0) (hv : ∀ r, v r ≤ B) :
    ∃ v₂, AReach (dpD c) (dpOrc N) x (GuardLe (dpD c) x B) (some (.cb f 0), v, none)
        (some (k (decide (∃ u < 2 ^ (c * (s + ℓ + 1)),
          pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N ∧
          ∃ v < 2 ^ (c * (s + ℓ + 1)), pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ La ∧
            Reach (2 ^ (c * (s + ℓ + 1))) (StepRel N x s) (c * (s + ℓ + 1)) u v))), v₂, none) ∧
      v₂ 22 = ℓ ∧ v₂ 23 = s ∧ v₂ 24 = 0 ∧ ∀ r, v₂ r ≤ B := by
  have hsw : s ≤ c * (s + ℓ + 1) := le_trans (by omega) (Nat.le_mul_of_pos_left _ hc)
  have hB : 2 ^ (c * (s + ℓ + 1)) ≤ B := (size_facts _).2.trans hBB
  obtain ⟨v', r1, e1, e2, e3, e4, e5⟩ := dp_prep (o := dpOrc N) (x := x) hc f hB hL hS hZ hv
  obtain ⟨v₂, f1, f2, r2⟩ := dp_fit N x s _ hsw j La hj h1 h2 h3 hD hBB e5 e1
  rw [hι] at r1
  exact ⟨v₂, r1.trans r2, (f1 22 fun r => dpρ_ne r (by decide)).trans e2,
    (f1 23 fun r => dpρ_ne r (by decide)).trans e3, (f1 24 fun r => dpρ_ne r (by decide)).trans e4,
    dp_bd_blk f1 f2 hBB e5⟩

open Classical in
/-- **The edge step** at radius `s`: `D` prepares and runs the edge block, which exits through
`dpkE b` with `b = false` exactly when no edge code is reachable (`NoEdge`). -/
private theorem dp_edge (N : FinNDTM Bool) (hc : 1 ≤ c) (x : List Bool) {s ℓ : ℕ}
    (hBB : 2 ^ (c * (s + ℓ + 1) * (c * (s + ℓ + 1))) ≤ B) {v : Fin 25 → ℕ} (hL : v 22 = ℓ)
    (hS : v 23 = s) (hZ : v 24 = 0) (hv : ∀ r, v r ≤ B) :
    ∃ b v₂, AReach (dpD c) (dpOrc N) x (GuardLe (dpD c) x B) (some (.cb false 0), v, none)
        (some (dpkE b), v₂, none) ∧ (b = false ↔ NoEdge N x s (c * (s + ℓ + 1))) ∧
      v₂ 22 = ℓ ∧ v₂ 23 = s ∧ v₂ 24 = 0 ∧ ∀ r, v₂ r ≤ B := by
  obtain ⟨v₂, r, e1, e2, e3, e4⟩ := dp_block N hc x hBB false 4 (edgeLang N) rfl (σ := dpσE) rfl
    rfl rfl (ι := DpLb.eb) (k := dpkE) (fun _ => rfl) rfl hL hS hZ hv
  exact ⟨_, v₂, r, by rw [decide_eq_false_iff_not, noEdge_iff], e1, e2, e3, e4⟩

open Classical in
/-- **The accept step** at radius `s`, when no edge code is reachable: `D` prepares and runs
the accept block, whose exit bit is membership (`mem_iff_reach_of_noEdge`), and answers it. -/
private theorem dp_acc (N : FinNDTM Bool) {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) (hc : 1 ≤ c) (x : List Bool) {s ℓ : ℕ}
    (hBB : 2 ^ (c * (s + ℓ + 1) * (c * (s + ℓ + 1))) ≤ B)
    (hw : codeK N * (s + logSpace x.length + 1) ≤ c * (s + ℓ + 1))
    (hne : NoEdge N x s (c * (s + ℓ + 1))) {v : Fin 25 → ℕ} (hL : v 22 = ℓ)
    (hS : v 23 = s) (hZ : v 24 = 0) (hv : ∀ r, v r ≤ B) :
    AHalt (dpD c) (dpOrc N) x (GuardLe (dpD c) x B) (some (.cb true 0), v, none)
      (decide (x ∈ L)) := by
  obtain ⟨v₂, r, -, -, -, e4⟩ := dp_block N hc x hBB true 2 (acceptLang N) rfl (σ := dpσA) rfl
    rfl rfl (ι := DpLb.ab) (k := DpLb.fin) (fun _ => rfl) rfl hL hS hZ hv
  rw [(@decide_eq_decide _ _ _ (Classical.propDecidable _)).mpr
    (mem_iff_reach_of_noEdge h x s _ hw hne).symm] at r
  exact r.halt (AHalt.ret rfl ⟨dp_pre (Or.inr (Or.inr ⟨_, rfl⟩)), e4⟩)

end Loop

/-- The largest code width of the run on `x`, at radius `sp |x| + 1`. -/
private def dpW (N : FinNDTM Bool) (sp : ℕ → ℕ) (x : List Bool) : ℕ :=
  (codeK N + 1) * (sp x.length + 1 + (1 + (Nat.bits x.length).length) + 1)

open Classical in
/-- **The deepening loop**: from the body at any radius `1 ≤ s ≤ sp |x| + 1`, `D` answers
`x ∈ L`.

**Proof sketch.** Induction on `sp |x| + 1 - s`. The edge step (`dp_edge`) exits with `false`
exactly when no edge code is reachable; then the accept step (`dp_acc`) answers membership.
At `s = sp |x| + 1` the bit is `false` (`noEdge_of_lt`). Below, a `true` bit forces
`s ≤ sp |x|` (again `noEdge_of_lt`), and `D` increments `s` and repeats the body. The widths
are at most `dpW N sp x`, so every register stays at most `2 ^ (dpW · dpW)`. -/
private theorem dp_body {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) (x : List Bool) :
    ∀ k s (v : Fin 25 → ℕ), sp x.length + 1 - s = k → 1 ≤ s → s ≤ sp x.length + 1 →
      v 22 = 1 + (Nat.bits x.length).length → v 23 = s → v 24 = 0 →
      (∀ r, v r ≤ 2 ^ (dpW N sp x * dpW N sp x)) →
      AHalt (dpD (codeK N + 1)) (dpOrc N) x
        (GuardLe (dpD (codeK N + 1)) x (2 ^ (dpW N sp x * dpW N sp x)))
        (some (.cb false 0), v, none) (decide (x ∈ L)) := by
  have hc : 1 ≤ codeK N + 1 := by omega
  have hl := dp_bits_logSpace x.length
  have hWs : ∀ s, s ≤ sp x.length + 1 →
      (codeK N + 1) * (s + (1 + (Nat.bits x.length).length) + 1) ≤ dpW N sp x := fun s hs =>
    Nat.mul_le_mul_left _ (by omega)
  have hBB : ∀ s, s ≤ sp x.length + 1 →
      2 ^ ((codeK N + 1) * (s + (1 + (Nat.bits x.length).length) + 1) *
        ((codeK N + 1) * (s + (1 + (Nat.bits x.length).length) + 1))) ≤ 2 ^ (dpW N sp x * dpW N sp x) :=
    fun s hs => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (hWs s hs) (hWs s hs))
  have hw : ∀ s, codeK N * (s + logSpace x.length + 1) ≤
      (codeK N + 1) * (s + (1 + (Nat.bits x.length).length) + 1) := fun s =>
    Nat.mul_le_mul (by omega) (by omega)
  intro k
  induction k with
  | zero =>
    intro s v hk hs1 hs2 hL hS hZ hv
    obtain ⟨b, v₂, r, hb, e1, e2, e3, e4⟩ := dp_edge N hc x (hBB s hs2) hL hS hZ hv
    obtain rfl : b = false := hb.mpr (noEdge_of_lt h x s _ (by omega))
    exact r.halt (dp_acc N h hc x (hBB s hs2) (hw s) (hb.mp rfl) e1 e2 e3 e4)
  | succ k ih =>
    intro s v hk hs1 hs2 hL hS hZ hv
    obtain ⟨b, v₂, r, hb, e1, e2, e3, e4⟩ := dp_edge N hc x (hBB s hs2) hL hS hZ hv
    cases b with
    | false => exact r.halt (dp_acc N h hc x (hBB s hs2) (hw s) (hb.mp rfl) e1 e2 e3 e4)
    | true =>
      have hs : s ≤ sp x.length := by
        by_contra hlt
        exact Bool.noConfusion (hb.mpr (noEdge_of_lt h x s _ (by omega)))
      have hsB : s + 1 ≤ 2 ^ (dpW N sp x * dpW N sp x) := by
        have h1 := hWs (s + 1) (by omega)
        have h2 : dpW N sp x < 2 ^ dpW N sp x := Nat.lt_two_pow_self
        have h3 : 2 ^ dpW N sp x ≤ 2 ^ (dpW N sp x * dpW N sp x) := (size_facts _).2
        have h4 : s + 1 ≤ (codeK N + 1) * (s + 1 + (1 + (Nat.bits x.length).length) + 1) :=
          le_trans (by omega) (Nat.le_mul_of_pos_left _ hc)
        omega
      refine r.halt (AHalt.step ⟨dp_pre (Or.inl ⟨23, .cb false 0, rfl⟩), e4⟩ ?_)
      rw [astep_inc (show dpD (codeK N + 1) (dpkE true) = .inc 23 (.cb false 0) from rfl)]
      exact ih (s + 1) _ (by omega) (by omega) (by omega)
        (by rw [Function.update_of_ne (by decide)]; exact e1)
        (by rw [Function.update_self, e2]) (by rw [Function.update_of_ne (by decide)]; exact e3)
        (register_update_le _ _ _ _ e4 (by rw [e2]; exact hsB))

open Classical in
/-- **`D`'s run**: from `scan` with all registers clear, `D` answers `x ∈ L` through register
values at most `2 ^ (dpW · dpW)`.

**Proof sketch.** Count `N := |x|` (`inputLength_loop`, decider `0`), set `ℓ := 1` and halve
`N` to `0` (`Complexity.Codec.halvCount_loop`), so `ℓ = 1 + |bits |x||`; set `s := 1` and run the deepening loop
(`dp_body`). Every value met is at most `|x| < 2 ^ ℓ ≤ 2 ^ dpW`. -/
private theorem dp_run {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) (x : List Bool) :
    AHalt (dpD (codeK N + 1)) (dpOrc N) x
      (GuardLe (dpD (codeK N + 1)) x (2 ^ (dpW N sp x * dpW N sp x)))
      (some .scan, fun _ => 0, none) (decide (x ∈ L)) := by
  have hl := dp_bits_logSpace x.length
  have hW1 : 1 + (Nat.bits x.length).length ≤ dpW N sp x :=
    le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega : 0 < codeK N + 1))
  have hWB : 2 ^ dpW N sp x ≤ 2 ^ (dpW N sp x * dpW N sp x) := (size_facts _).2
  have hn : x.length < 2 ^ dpW N sp x :=
    (dp_bits_logSpace x.length).2.2.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hWlt : dpW N sp x < 2 ^ dpW N sp x := Nat.lt_two_pow_self
  set B := 2 ^ (dpW N sp x * dpW N sp x) with hB
  have hnB : x.length ≤ B := by omega
  have hlB : 1 + (Nat.bits x.length).length ≤ B := by omega
  have r1 := inputLength_loop (dpD (codeK N + 1)) (dpOrc N) x 21 0 .scan .incN .lInc rfl rfl
    (fun m _ => indicator_inputLenLang x m) B hnB (fun _ => 0) (fun _ => Nat.zero_le _)
    (Nat.zero_le _)
  have b1 : ∀ r, Function.update (fun _ : Fin 25 => 0) 21 x.length r ≤ B :=
    register_update_le _ _ _ _ (fun _ => Nat.zero_le _) hnB
  refine (r1.mono fun _ h => h).halt ((dp_inc (l := .lInc) rfl b1).halt ?_)
  rw [Function.update_of_ne (by decide), zero_add]
  have b2 := register_update_le _ 22 _ _ b1 (show 1 ≤ B by omega)
  have e21 : Function.update (Function.update (fun _ : Fin 25 => 0) 21 x.length) 22 1 21 =
      x.length := by
    rw [Function.update_of_ne (by decide), Function.update_self]
  refine (Codec.halvCount_loop (dpD (codeK N + 1)) (dpOrc N) x 21 22 (by decide) .hz .hh .hi .sOne
    rfl rfl rfl B _ b2 (by rw [Function.update_self, e21]; omega)).halt ?_
  rw [Function.update_self, e21]
  have b3 := register_update_le _ 22 _ _ (register_update_le _ 21 _ _ b2 (Nat.zero_le _)) hlB
  refine (dp_inc (l := .sOne) rfl b3).halt ?_
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_of_ne (by decide), zero_add]
  exact dp_body h x _ 1 _ rfl le_rfl (by omega)
    (by rw [Function.update_of_ne (by decide), Function.update_self])
    (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)])
    (register_update_le _ _ _ _ b3 (by omega))

/-! ## The contract -/

/-- **The deepening machine meets the contract**: if `N` decides `L` in space `sp`, a register
machine with five logspace deciders decides `L` with every register of at most
`C · (sp |x| + logSpace |x| + 1)²` binary digits. The deciders are `inputLenLang`,
`initLang N`, `acceptLang N`, `stepLang N` and `edgeLang N`, and `C = 9 (codeK N + 1)² + 2`.

**Proof sketch.** `D`'s run (`dp_run`) answers `x ∈ L` with every register at most
`2 ^ (W · W)`, `W = (codeK N + 1)(sp |x| + ℓ + 2)` and `ℓ ≤ logSpace |x| + 1`
(`dp_bits_logSpace`). A value `v ≤ 2 ^ (W · W)` has `|bits (v + 1)| ≤ W · W + 2`
(`length_bits_le`), and `W ≤ 3 (codeK N + 1) X` with `X = sp |x| + logSpace |x| + 1 ≥ 1`, so
`W · W + 2 ≤ (9 (codeK N + 1)² + 2) X²`. -/
theorem deepen_contract {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) : DeepenContract L sp := by
  refine ⟨25, 5, DpLb (codeK N + 1), inferInstance, inferInstance, dpD (codeK N + 1), .scan,
    dpAs N, fun j => ?_, 9 * (codeK N + 1) ^ 2 + 2, fun x => ?_⟩
  · fin_cases j
    exacts [inputLenLang_mem, initLang_mem, acceptLang_mem, stepLang_mem, edgeLang_mem]
  · rw [indicator_eq_decide]
    refine (dp_run h x).mono fun a ha => ⟨ha.1, fun r => ?_⟩
    have hl := (dp_bits_logSpace x.length).2.1
    have hls : 1 ≤ logSpace x.length := by rw [logSpace_eq]; omega
    set X := sp x.length + logSpace x.length + 1 with hX
    set W := dpW N sp x with hW
    have hW3 : W ≤ 3 * (codeK N + 1) * X := by
      rw [hW, dpW, mul_comm 3, mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have hlt : a.2.1 r + 1 < 2 ^ (W * W + 2) := by
      have := ha.2 r
      have e : 2 ^ (W * W + 2) = 4 * 2 ^ (W * W) := by rw [pow_add]; ring
      have := Nat.two_pow_pos (W * W)
      omega
    refine (length_bits_le hlt).trans ?_
    have h1 : W * W ≤ 3 * (codeK N + 1) * X * (3 * (codeK N + 1) * X) := Nat.mul_le_mul hW3 hW3
    have h2 : 1 ≤ X * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc W * W + 2 ≤ 3 * (codeK N + 1) * X * (3 * (codeK N + 1) * X) + 2 * (X * X) := by omega
      _ = (9 * (codeK N + 1) ^ 2 + 2) * X ^ 2 := by ring

end Complexity.LogProg.SavitchARM
