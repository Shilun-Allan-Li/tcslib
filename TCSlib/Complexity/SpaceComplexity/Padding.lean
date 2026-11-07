/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.SpaceComplexity.Codec.Word

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding transfers space bounds down

Padding a language by a polynomial number of ones lowers the space it needs, measured in the
padded length: if `L ∈ SPACE S`, the language of its members padded by `C · (|x| + 1)^d` ones,
`padLang L (fun n => C * (n + 1) ^ d)`, lies in `SPACE T` for every `T` that is at least linear
and dominates `S` at the padded length. This is the space form of the padding argument
[AB09, Exercise 3.2] calls for; `Complexity.SPACE_linear_ne_NP` uses it at `S n = n² + 1`,
`T n = n + 1` and the pad `(|x| + 1)²`.

## Main definitions

* `Complexity.padLang` — the members `x` of `L`, each padded by `pad |x|` ones:
  `pairEncode x 1^{pad |x|}`.

## Main results

* `Complexity.mem_padLang_iff` — `padLang`'s defining formula.
* `Complexity.mem_SPACE_padLang` — the padded language is in `SPACE T`. (Statement; its proof is
  a fill.)

## Implementation notes

The pad is a unary block after `pairEncode`, so a member's first component and its length are
recovered from the padded word (`Turing.length_pairEncode`). The lower bound `m + 1 ≤ T m` pays
for checking that the input is a padded word at all, and for the copy of its first component;
`S n ≤ T (2n + 2 + C (n + 1)^d)` pays for deciding `L` on that component.

## References

* [AB09] S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009.
-/

namespace Complexity

open Turing

/-- **The padded language**: the members `x` of `L`, each followed by `pad |x|` ones, as the
pair `pairEncode x 1^{pad |x|}`. [AB09, Exercise 3.2] -/
def padLang (L : Language Bool) (pad : ℕ → ℕ) : Language Bool :=
  {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}

/-- **Membership in `padLang`, unfolded**: `y ∈ padLang L pad` exactly when `y` is a member `x`
of `L` paired with `pad |x|` ones. -/
theorem mem_padLang_iff {L : Language Bool} {pad : ℕ → ℕ} {y : List Bool} :
    y ∈ padLang L pad ↔ ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true) :=
  Iff.rfl

/-! ### The padded words, the virtual input and the bank's languages (E-PAD) -/

/-- **Padded words**: `y` is the pair of some `a` with `C (|a| + 1)^d` ones. -/
private def epadValid (C d : ℕ) (y : List Bool) : Prop :=
  ∃ a, y = pairEncode a (List.replicate (C * (a.length + 1) ^ d) true)

/-- The language of padded words: the validator's language. -/
private def epadV (C d : ℕ) : Language Bool := {y | epadValid C d y}

/-- Membership in the validator's language. -/
private lemma epad_mem_V {C d : ℕ} {y : List Bool} :
    y ∈ (epadV C d : Set (List Bool)) ↔ epadValid C d y :=
  Iff.rfl

open Classical in
/-- **The virtual input** of the run phase: the first component of a padded word, and the
empty word on every other input. -/
private noncomputable def epadVirt (C d : ℕ) (y : List Bool) : List Bool :=
  if epadValid C d y then pairFstD y else []

/-- **The bank's languages.** On a query word `⟨y, w⟩` whose index word `w` is canonical
(`w.getLastD true = true`) and no wider than `|y|` in binary, mode `false` asks whether `y`
is padded and the index is below the first component's length, mode `true` whether `y` is
padded and the first component's indexed bit is `1`. -/
private def epadQ (C d : ℕ) (mode : Bool) : Language Bool :=
  {z | ∃ y w, pairDecode z = some (y, w) ∧ w.getLastD true = true ∧
    w.length ≤ (Nat.bits y.length).length ∧ epadValid C d y ∧
    (if mode = true then (pairFstD y).getD (LogProg.bitsVal w) false = true
      else LogProg.bitsVal w < (pairFstD y).length)}

/-- On a padded word the virtual input is its first component. -/
private lemma epadVirt_of_valid {C d : ℕ} {y : List Bool} (h : epadValid C d y) :
    epadVirt C d y = pairFstD y := by
  classical
  rw [epadVirt, if_pos h]

/-- Off the padded words the virtual input is empty. -/
private lemma epadVirt_of_not_valid {C d : ℕ} {y : List Bool} (h : ¬ epadValid C d y) :
    epadVirt C d y = [] := by
  classical
  rw [epadVirt, if_neg h]

/-- The virtual input is no longer than the input. -/
private lemma epadVirt_length_le (C d : ℕ) (y : List Bool) :
    (epadVirt C d y).length ≤ y.length := by
  by_cases h : epadValid C d y
  · rw [epadVirt_of_valid h]; exact length_pairFstD_le y
  · rw [epadVirt_of_not_valid h]; exact Nat.zero_le _

/-- Membership in the bank's language, for a decoded pair. -/
private lemma epad_mem_Q_iff {C d : ℕ} {mode : Bool} {z y w : List Bool}
    (hd : pairDecode z = some (y, w)) :
    z ∈ (epadQ C d mode : Set (List Bool)) ↔ w.getLastD true = true ∧
      w.length ≤ (Nat.bits y.length).length ∧ epadValid C d y ∧
      (if mode = true then (pairFstD y).getD (LogProg.bitsVal w) false = true
        else LogProg.bitsVal w < (pairFstD y).length) := by
  constructor
  · rintro ⟨y', w', hd', h⟩
    rw [hd, Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl⟩ := hd'
    exact h
  · intro h
    exact ⟨y, w, hd, h⟩

/-- A word that is not a pair is not in the bank's language. -/
private lemma epad_not_mem_Q {C d : ℕ} {mode : Bool} {z : List Bool} (hd : pairDecode z = none) :
    z ∉ (epadQ C d mode : Set (List Bool)) := by
  rintro ⟨y, w, hd', -⟩
  rw [hd] at hd'
  cases hd'

/-- **A genuine query** `⟨y, bits i⟩` with `i ≤ |y|` is in the bank's language exactly when `y`
is padded and the mode's question holds at `i`. -/
private lemma epad_query_mem_iff (C d : ℕ) (mode : Bool) (y : List Bool) (i : ℕ)
    (hi : i ≤ y.length) :
    pairEncode y (Nat.bits i) ∈ epadQ C d mode ↔ epadValid C d y ∧
      (if mode = true then (pairFstD y).getD i false = true else i < (pairFstD y).length) := by
  show pairEncode y (Nat.bits i) ∈ (epadQ C d mode : Set (List Bool)) ↔ _
  rw [epad_mem_Q_iff (pairDecode_pairEncode y (Nat.bits i)), LogProg.bitsVal_bits]
  exact ⟨fun h => h.2.2, fun h => ⟨(LogProg.drop_canon _).mpr (LogProg.canon_bits i),
    LogProg.length_bits_mono hi, h⟩⟩

/-! ### Register machines: syntactic preconditions, counting loops, the validity block and
the validator (E-PAD checkpoint 2)

The validator and the bank are abstract register machines (`Complexity.LogProg.ARM`) over the
eighteen registers `Fin 18`, calling the two input deciders `inputBitLang` (`0`) and
`inputLenLang` (`1`). -/

namespace LogProg

/-! ### Syntactic preconditions of single instructions -/

/-- The instructions whose syntactic preconditions hold at every configuration: an equality
test of two distinct registers, a call with distinct arguments, and every instruction that does
not compare a register with the input (`jeqIn`, `jeqFst`, `jeqSnd` are excluded). -/
private def epadOk {m d : ℕ} {Λ : Type} : Ins m d Λ → Prop
  | .jeq r s _ _ => r ≠ s
  | .call _ _ args _ _ => args.Nodup
  | .jeqIn _ _ _ => False
  | .jeqFst _ _ _ => False
  | .jeqSnd _ _ _ => False
  | _ => True

/-- **The syntactic preconditions from the instruction** (`preS_of_ins`), at a label holding an
`epadOk` instruction. -/
private lemma epad_preS {m d : ℕ} {Λ : Type} {A : ARM m d Λ} {x : List Bool} {l : Λ}
    {w : Fin m → ℕ} {res : Option Bool} {i : Ins m d Λ} (h : A l = i) (hi : epadOk i) :
    PreS A x (some l, w, res) :=
  preS_of_ins (fun _ _ _ _ h' => by rw [h] at h'; subst h'; exact hi)
    (fun _ _ _ _ _ h' => by rw [h] at h'; subst h'; exact hi)
    (fun _ _ _ h' => by rw [h] at h'; subst h'; exact hi.elim)
    (fun _ _ _ h' => by rw [h] at h'; subst h'; exact hi.elim)
    (fun _ _ _ h' => by rw [h] at h'; subst h'; exact hi.elim)

/-! ### Counting loops of the validator -/

section Loops
variable {m d : ℕ} {Λ : Type}

/-- Close a goal about updated register files by cases on the register. -/
local macro "epad_upd" : tactic =>
  `(tactic| (funext s; simp only [Function.update_apply]; split_ifs <;> subst_vars <;>
    (try simp_all) <;> omega))

/-- **The ones scan**: the loop `test: jeq ptr lim exit read; read: call j [ptr] inc fail;
inc: inc cnt adv₀; adv_i: inc ptr adv_{i+1}` (`stride` advances back to `test`) walks a
strided segment `w`: if every letter is `1` it exits with the pointer at the end and `|w|`
added to `cnt`, and at the first `0` it fails. -/
private theorem epad_ones_loop (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (ptr lim cnt : Fin m) (hpl : ptr ≠ lim) (hpc : ptr ≠ cnt) (hlc : lim ≠ cnt)
    (j : Fin d) (test read inc exit fail : Λ) (adv : ℕ → Λ) (stride B : ℕ)
    (htest : A test = .jeq ptr lim exit read)
    (hread : A read = .call j .whole [ptr] inc fail)
    (hinc : A inc = .inc cnt (adv 0))
    (hadv : ∀ i < stride, A (adv i) = .inc ptr (adv (i + 1)))
    (hend : adv stride = test) (hs : 0 < stride) :
    ∀ (w : List Bool) (v : Fin m → ℕ), (∀ r, v r ≤ B) →
      v lim = v ptr + stride * w.length → v cnt + w.length ≤ B →
      (∀ i < w.length, oracle j (pairEncode x (Nat.bits (v ptr + stride * i))) =
        w.getD i false) →
      ((∀ i < w.length, w.getD i false = true) →
        AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (some test, v, none)
          (some exit, Function.update (Function.update v ptr (v lim)) cnt (v cnt + w.length),
            none)) ∧
      ((∃ i < w.length, w.getD i false = false) →
        ∃ v', (∀ r, v' r ≤ B) ∧ (∀ r, r ≠ ptr → r ≠ cnt → v' r = v r) ∧
          AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (some test, v, none)
            (some fail, v', none)) := by
  intro w
  induction w with
  | nil =>
    intro v hv hl _ _
    have eq : v ptr = v lim := by simpa using hl.symm
    refine ⟨fun _ => ?_, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
    have e : Function.update (Function.update v ptr (v lim)) cnt
        (v cnt + ([] : List Bool).length) = v := by
      rw [← eq, Function.update_eq_self, List.length_nil, Nat.add_zero, Function.update_eq_self]
    rw [e]
    have hstep := AReach.single (A := A) (oracle := oracle) (x := x)
      (G := fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (a := (some test, v, none))
      ⟨epad_preS htest hpl, hv⟩
    rwa [astep_jeq htest, if_pos eq] at hstep
  | cons b w ih =>
    intro v hv hl hc ho
    simp only [List.length_cons] at hl hc
    have hne : v ptr ≠ v lim := by
      have : stride * 1 ≤ stride * (w.length + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hb : oracle j (pairEncode x (Nat.bits (v ptr))) = b := by
      simpa using ho 0 (by simp)
    have h1 : AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (some test, v, none)
        (some (if b then inc else fail), v, none) := by
      refine AReach.step ⟨epad_preS htest hpl, hv⟩ ?_
      rw [astep_jeq htest, if_neg hne]
      have hstep := AReach.single (A := A) (oracle := oracle) (x := x)
        (G := fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (a := (some read, v, none))
        ⟨epad_preS hread (List.nodup_singleton _), hv⟩
      rwa [astep_call hread, vword_whole₁, hb] at hstep
    cases b with
    | false =>
      refine ⟨fun hall => ?_, fun _ => ⟨v, hv, fun _ _ _ => rfl, h1⟩⟩
      have := hall 0 (by simp)
      simp at this
    | true =>
      -- one unit counted, then `stride` pointer increments
      set v₁ := Function.update v cnt (v cnt + 1) with hv₁
      set v₂ := Function.update v₁ ptr (v₁ ptr + stride) with hv₂
      have hv₁b : ∀ r, v₁ r ≤ B := register_update_le v cnt B _ hv (by omega)
      have hroom : v ptr + stride ≤ v lim := by
        rw [hl, Nat.mul_succ]; omega
      have hv₂b : ∀ r, v₂ r ≤ B := register_update_le v₁ ptr B _ hv₁b (by
        rw [hv₁, Function.update_of_ne hpc]; exact hroom.trans (hv lim))
      have h2 : AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
          (some inc, v, none) (some test, v₂, none) := by
        refine AReach.step ⟨epad_preS hinc trivial, hv⟩ ?_
        rw [astep_inc hinc, ← hv₁]
        have hc := arm_chain A oracle x ptr true adv stride B
          (fun i hi => (hadv i hi).trans (cond_true _ _).symm) v₁ hv₁b
          (by show v₁ ptr + stride ≤ B
              rw [hv₁, Function.update_of_ne hpc]; exact hroom.trans (hv lim))
        rwa [hend, cond_true, ← hv₂] at hc
      have hl₂ : v₂ lim = v₂ ptr + stride * w.length := by
        simp only [hv₂, hv₁, Function.update_self, Function.update_of_ne hpl.symm,
          Function.update_of_ne hlc, Function.update_of_ne hpc]
        rw [hl, Nat.mul_succ]; omega
      have hc₂ : v₂ cnt + w.length ≤ B := by
        simp only [hv₂, hv₁, Function.update_self, Function.update_of_ne hpc.symm]
        omega
      have ho₂ : ∀ i < w.length, oracle j (pairEncode x (Nat.bits (v₂ ptr + stride * i))) =
          w.getD i false := by
        intro i hi
        have := ho (i + 1) (by simp; omega)
        simp only [hv₂, hv₁, Function.update_self, Function.update_of_ne hpc]
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm stride] using this
      obtain ⟨ih₁, ih₂⟩ := ih v₂ hv₂b hl₂ hc₂ ho₂
      have h12 := h1
      simp only [if_true] at h12
      refine ⟨fun hall => ?_, fun ⟨i, hi, hf⟩ => ?_⟩
      · have hall' : ∀ i < w.length, w.getD i false = true := fun i hi => by
          simpa using hall (i + 1) (by simp; omega)
        have hr := (h12.trans h2).trans (ih₁ hall')
        have e : Function.update (Function.update v₂ ptr (v₂ lim)) cnt (v₂ cnt + w.length) =
            Function.update (Function.update v ptr (v lim)) cnt (v cnt + (true :: w).length) := by
          rw [hv₂, hv₁]
          epad_upd
        rwa [e] at hr
      · cases i with
        | zero => simp at hf
        | succ i =>
          obtain ⟨v', hv', hfr, hr⟩ := ih₂ ⟨i, by simpa using hi, by simpa using hf⟩
          refine ⟨v', hv', fun r hr1 hr2 => ?_, (h12.trans h2).trans hr⟩
          rw [hfr r hr1 hr2, hv₂, Function.update_of_ne hr1, hv₁, Function.update_of_ne hr2]

/-- **Multiplying by counting**: the loop `ml: jz kr exit md; md: dec kr addT`, then
`t := p` (`addT: jeq t p scT addB; addB: inc t addT`, the published `registerCopy_loop`) and
`q += t, t := 0` (`scT: jz t ml scD; scD: dec t scI; scI: inc q scT`, the published
`registerScale_loop` at factor `1`), adds `kr · p` to `q` and clears `kr`. -/
private theorem epad_mul_loop (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (kr t p q : Fin m) (hkt : kr ≠ t) (hkp : kr ≠ p) (hkq : kr ≠ q)
    (htp : t ≠ p) (htq : t ≠ q) (hpq : p ≠ q)
    (ml md addT addB scT scD scI exit : Λ)
    (hml : A ml = .jz kr exit md) (hmd : A md = .dec kr addT)
    (hT : A addT = .jeq t p scT addB) (hB : A addB = .inc t addT)
    (hS : A scT = .jz t ml scD) (hD : A scD = .dec t scI) (hI : A scI = .inc q scT) (B : ℕ) :
    ∀ (k : ℕ) (v : Fin m → ℕ), v kr = k → v t = 0 → (∀ r, v r ≤ B) → v q + k * v p ≤ B →
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (some ml, v, none)
        (some exit, Function.update (Function.update v kr 0) q (v q + k * v p), none) := by
  intro k
  induction k with
  | zero =>
    intro v hk _ hv _
    have e : Function.update (Function.update v kr 0) q (v q + 0 * v p) = v := by
      funext s
      simp only [Function.update_apply, Nat.zero_mul, Nat.add_zero]
      split_ifs <;> subst_vars <;> simp_all
    rw [e]
    have hstep := AReach.single (A := A) (oracle := oracle) (x := x)
      (G := fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (a := (some ml, v, none))
      ⟨epad_preS hml trivial, hv⟩
    rwa [astep_jz hml, if_pos hk] at hstep
  | succ k ih =>
    intro v hk ht hv hb
    have hpk : v p ≤ (k + 1) * v p := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
    obtain ⟨v₁, hv₁⟩ : ∃ w, w = Function.update v kr k := ⟨_, rfl⟩
    have b₁ : ∀ r, v₁ r ≤ B := by
      rw [hv₁]; exact register_update_le v kr B _ hv (by have := hv kr; omega)
    have h₁t : v₁ t = 0 := by rw [hv₁, Function.update_of_ne hkt.symm, ht]
    have h₁p : v₁ p = v p := by rw [hv₁, Function.update_of_ne hkp.symm]
    have h₁q : v₁ q = v q := by rw [hv₁, Function.update_of_ne hkq.symm]
    -- `t := p`
    have hcp := registerCopy_loop A oracle x t p htp addT addB scT hT hB B v₁ b₁
      (by rw [h₁t]; exact Nat.zero_le _)
    obtain ⟨v₂, hv₂⟩ : ∃ w, w = Function.update v₁ t (v₁ p) := ⟨_, rfl⟩
    rw [← hv₂] at hcp
    have b₂ : ∀ r, v₂ r ≤ B := by rw [hv₂]; exact register_update_le v₁ t B _ b₁ (b₁ p)
    -- `q += t`, `t := 0`
    have hsc := registerScale_loop A oracle x t q htq scT scD ml
      (fun i => if i = 0 then scI else scT) 1 hS hD
      (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact hI) rfl B v₂ b₂ (by
          rw [hv₂, Function.update_self, Function.update_of_ne htq.symm, h₁p, h₁q, Nat.one_mul]
          omega)
    obtain ⟨v₃, hv₃⟩ : ∃ w, w = Function.update (Function.update v₂ t 0) q
        (v₂ q + 1 * v₂ t) := ⟨_, rfl⟩
    rw [← hv₃] at hsc
    have b₃ : ∀ r, v₃ r ≤ B := by
      rw [hv₃]
      refine register_update_le _ q B _ (register_update_le _ t B 0 b₂ (Nat.zero_le _)) ?_
      rw [hv₂, Function.update_self, Function.update_of_ne htq.symm, h₁p, h₁q, Nat.one_mul]
      omega
    have key : ∀ s, v₃ s = if s = kr then k else if s = q then v q + v p else v s := by
      intro s
      rw [hv₃, hv₂, hv₁]
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    have hr := ih v₃ (by rw [key]; simp) (by rw [key]; simp [htq, hkt.symm, ht])
      b₃ (by rw [key, key]; simp only [↓reduceIte, if_neg hkq.symm, if_neg hkp.symm,
          if_neg hpq]; rw [Nat.succ_mul] at hb; omega)
    refine AReach.step ⟨epad_preS hml trivial, hv⟩ ?_
    rw [astep_jz hml, if_neg (by omega)]
    refine AReach.step ⟨epad_preS hmd trivial, hv⟩ ?_
    rw [astep_dec hmd, hk, Nat.add_sub_cancel, ← hv₁]
    refine hcp.trans (hsc.trans ?_)
    have e : Function.update (Function.update v₃ kr 0) q (v₃ q + k * v₃ p) =
        Function.update (Function.update v kr 0) q (v q + (k + 1) * v p) := by
      funext s
      simp only [Function.update_apply, key]
      split_ifs <;> subst_vars <;> simp_all
      ring
    rwa [e] at hr

/-- **Powering by counting**: the loop `pw: jz dc exit pd; pd: dec dc mkTest`, then
`kr := n` (`mkTest`, `mkBump`), the multiplication loop (`q := kr · p`), then `p := q`
(`mv: clr p`, `mvTest`, `mvBump`) and `mvc: clr q pw`, multiplies `p` by `n ^ dc`. -/
private theorem epad_pow_loop (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (n dc kr t p q : Fin m)
    (hnd : n ≠ dc) (hnk : n ≠ kr) (hnp : n ≠ p) (hnq : n ≠ q)
    (hdk : dc ≠ kr) (hdt : dc ≠ t) (hdp : dc ≠ p) (hdq : dc ≠ q)
    (hkt : kr ≠ t) (hkp : kr ≠ p) (hkq : kr ≠ q) (htp : t ≠ p) (htq : t ≠ q) (hpq : p ≠ q)
    (pw pd mkTest mkBump ml md addT addB scT scD scI mv mvTest mvBump mvc exit : Λ)
    (hpw : A pw = .jz dc exit pd) (hpd : A pd = .dec dc mkTest)
    (hmkT : A mkTest = .jeq kr n ml mkBump) (hmkB : A mkBump = .inc kr mkTest)
    (hml : A ml = .jz kr mv md) (hmd : A md = .dec kr addT)
    (hT : A addT = .jeq t p scT addB) (hB : A addB = .inc t addT)
    (hS : A scT = .jz t ml scD) (hD : A scD = .dec t scI) (hI : A scI = .inc q scT)
    (hmv : A mv = .clr p mvTest) (hmvT : A mvTest = .jeq p q mvc mvBump)
    (hmvB : A mvBump = .inc p mvTest) (hmvc : A mvc = .clr q pw) (B : ℕ) :
    ∀ (e : ℕ) (v : Fin m → ℕ), v dc = e → v q = 0 → v kr = 0 → v t = 0 → 1 ≤ v n →
      (∀ r, v r ≤ B) → v p * v n ^ e ≤ B →
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (some pw, v, none)
        (some exit, Function.update (Function.update v dc 0) p (v p * v n ^ e), none) := by
  intro e
  induction e with
  | zero =>
    intro v he _ _ _ _ hv _
    have eq : Function.update (Function.update v dc 0) p (v p * v n ^ 0) = v := by
      funext s
      simp only [Function.update_apply, pow_zero, Nat.mul_one]
      split_ifs <;> subst_vars <;> simp_all
    rw [eq]
    have hstep := AReach.single (A := A) (oracle := oracle) (x := x)
      (G := fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (a := (some pw, v, none))
      ⟨epad_preS hpw trivial, hv⟩
    rwa [astep_jz hpw, if_pos he] at hstep
  | succ e ih =>
    intro v he hq hk ht hn hv hb
    have hpow : 1 ≤ v n ^ e := Nat.one_le_pow _ _ hn
    have hpn : v p * v n ≤ v p * v n ^ (e + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_self_pow (Nat.succ_ne_zero e) _)
    have hnB : v n ≤ B := hv n
    -- `dc := e`, then `kr := n`
    set v₁ := Function.update v dc e with hv₁
    have b₁ : ∀ r, v₁ r ≤ B := register_update_le v dc B _ hv (by have := hv dc; omega)
    have hc₁ := registerCopy_loop A oracle x kr n hnk.symm mkTest mkBump ml hmkT hmkB B v₁ b₁
      (by rw [hv₁, Function.update_of_ne hdk.symm, hk]; exact Nat.zero_le _)
    set v₂ := Function.update v₁ kr (v₁ n) with hv₂
    have b₂ : ∀ r, v₂ r ≤ B := register_update_le v₁ kr B _ b₁ (b₁ n)
    -- `q := kr · p`
    have hm := epad_mul_loop A oracle x kr t p q hkt hkp hkq htp htq hpq ml md addT addB scT
      scD scI mv hml hmd hT hB hS hD hI B (v₂ kr) v₂ rfl
      (by rw [hv₂, Function.update_of_ne hkt.symm, hv₁, Function.update_of_ne hdt.symm, ht])
      b₂ (by
        rw [hv₂, Function.update_of_ne hkq.symm, Function.update_self,
          Function.update_of_ne hkp.symm, hv₁, Function.update_of_ne hdq.symm,
          Function.update_of_ne hnd, Function.update_of_ne hdp.symm, hq, Nat.zero_add,
          Nat.mul_comm]
        exact hpn.trans hb)
    have hval : v₂ q + v₂ kr * v₂ p = v p * v n := by
      rw [hv₂, Function.update_of_ne hkq.symm, Function.update_self,
        Function.update_of_ne hkp.symm, hv₁, Function.update_of_ne hdq.symm,
        Function.update_of_ne hnd, Function.update_of_ne hdp.symm, hq, Nat.zero_add,
        Nat.mul_comm]
    obtain ⟨v₃, hv₃⟩ : ∃ w, w = Function.update (Function.update v₂ kr 0) q
        (v₂ q + v₂ kr * v₂ p) := ⟨_, rfl⟩
    rw [← hv₃] at hm
    have hq₃ : v₃ q = v p * v n := by rw [hv₃, Function.update_self, hval]
    have b₃ : ∀ r, v₃ r ≤ B := by
      rw [hv₃]
      refine register_update_le _ q B _ (register_update_le _ kr B 0 b₂ (Nat.zero_le _)) ?_
      rw [hval]; exact hpn.trans hb
    -- `p := q`
    set v₄ := Function.update v₃ p 0 with hv₄
    have b₄ : ∀ r, v₄ r ≤ B := register_update_le v₃ p B 0 b₃ (Nat.zero_le _)
    have hc₄ := registerCopy_loop A oracle x p q hpq mvTest mvBump mvc hmvT hmvB B v₄ b₄
      (by rw [hv₄, Function.update_self]; exact Nat.zero_le _)
    set v₅ := Function.update v₄ p (v₄ q) with hv₅
    have b₅ : ∀ r, v₅ r ≤ B := register_update_le v₄ p B _ b₄ (b₄ q)
    set v₆ := Function.update v₅ q 0 with hv₆
    have b₆ : ∀ r, v₆ r ≤ B := register_update_le v₅ q B 0 b₅ (Nat.zero_le _)
    have key : ∀ s, v₆ s = if s = dc then e else if s = p then v p * v n else v s := by
      intro s
      rw [hv₆, hv₅, hv₄, hv₃, hv₂, hv₁]
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [Nat.mul_comm]
    have hr := ih v₆ (by rw [key]; simp) (by rw [key]; simp [hpq.symm, hdq.symm, hq])
      (by rw [key]; simp [hkp, hdk.symm, hk]) (by rw [key]; simp [htp, hdt.symm, ht])
      (by rw [key]; simpa [hnp, hnd] using hn) b₆
      (by rw [key, key]; simp only [↓reduceIte, if_neg hdp.symm, if_neg hnp, if_neg hnd]
          rw [Nat.mul_assoc, ← pow_succ']; exact hb)
    refine AReach.step ⟨epad_preS hpw trivial, hv⟩ ?_
    rw [astep_jz hpw, if_neg (by omega)]
    refine AReach.step ⟨epad_preS hpd trivial, hv⟩ ?_
    rw [astep_dec hpd, he, Nat.add_sub_cancel, ← hv₁]
    refine hc₁.trans (hm.trans ?_)
    refine AReach.step ⟨epad_preS hmv trivial, b₃⟩ ?_
    rw [astep_clr hmv, ← hv₄]
    refine hc₄.trans ?_
    refine AReach.step ⟨epad_preS hmvc trivial, b₅⟩ ?_
    rw [astep_clr hmvc, ← hv₆]
    have eq : Function.update (Function.update v₆ dc 0) p (v₆ p * v₆ n ^ e) =
        Function.update (Function.update v dc 0) p (v p * v n ^ (e + 1)) := by
      funext s
      simp only [Function.update_apply, key]
      split_ifs <;> subst_vars <;> simp_all [pow_succ', Nat.mul_assoc]
    rwa [eq] at hr

end Loops

end LogProg

open LogProg

/-! ### The validity block -/

/-- The labels of the validity block: the pair scan (`scan` … `adv`), `|a| + 1` from the
pointer (`cpTest`, `cpBump`, `half1`, `half2`), the ones scan of the pad (`os…`), the chains
loading `C` and `d` (`cInc`, `dInc`), the power loop (`pw` … `mvc`) and the final comparison
(`cmp`). -/
private inductive EPadVL (C d : ℕ) where
  | scan | first | test (b : Bool) | read (b : Bool) | adv (k : Fin 4) (second : Bool)
  | cpTest | cpBump | half1 | half2
  | osTest | osRead | osInc | osAdv (second : Bool)
  | cInc (i : Fin C) | dInc (i : Fin d)
  | pw | pd | mkTest | mkBump | ml | md | addT | addB | scT | scD | scI
  | mv | mvTest | mvBump | mvc | cmp

/-- Every label of the validity block, listed. -/
private def epadVLAll (C d : ℕ) : List (EPadVL C d) :=
  [.scan, .first, .test false, .test true, .read false, .read true] ++
  ((List.finRange 4).flatMap fun k => [.adv k false, .adv k true]) ++
  [.cpTest, .cpBump, .half1, .half2, .osTest, .osRead, .osInc, .osAdv false, .osAdv true] ++
  (List.finRange C).map .cInc ++ (List.finRange d).map .dInc ++
  [.pw, .pd, .mkTest, .mkBump, .ml, .md, .addT, .addB, .scT, .scD, .scI, .mv, .mvTest, .mvBump,
    .mvc, .cmp]

/-- The validity block's labels form a finite type (a local instance of the proofs, so that no
public instance is declared). -/
private noncomputable def epadVLFintype (C d : ℕ) : Fintype (EPadVL C d) := by
  classical
  refine Fintype.ofList (epadVLAll C d) (fun l => ?_)
  cases l with
  | adv k b => cases b <;> simp [epadVLAll]
  | _ => simp [epadVLAll]

/-- The stride of the block: `1` on the input itself, `2` on the doubled first field of a
query. -/
private def epadS (wide : Bool) : ℕ := if wide then 2 else 1

/-- The targets of the pair scan's advance chains. -/
private def epadAdvEnd {C d : ℕ} {Λ : Type} (ι : EPadVL C d → Λ) (k : Fin 4) : Λ :=
  if k = 0 then ι (.test false) else if k = 1 then ι (.test true)
  else if k = 2 then ι .scan else ι .cpTest

/-- The pair scan's advance chains, indexed as `alignedPair_loop` reads them. -/
private def epadAdv {C d : ℕ} {Λ : Type} (ι : EPadVL C d → Λ) (wide : Bool) (k : Fin 4)
    (i : ℕ) : Λ :=
  if i = 0 then ι (.adv k false) else if i = 1 ∧ wide = true then ι (.adv k true)
  else epadAdvEnd ι k

/-- The ones scan's advance chain. -/
private def epadOsAdv {C d : ℕ} {Λ : Type} (ι : EPadVL C d → Λ) (wide : Bool) (i : ℕ) : Λ :=
  if i = 0 then ι (.osAdv false) else if i = 1 ∧ wide = true then ι (.osAdv true)
  else ι .osTest

/-- The chain loading `d` into the power counter. -/
private def epadDI {C d : ℕ} {Λ : Type} (ι : EPadVL C d → Λ) (j : ℕ) : Λ :=
  if h : j < d then ι (.dInc ⟨j, h⟩) else ι .pw

/-- The chain loading `C` into the power accumulator, then the chain of `d`. -/
private def epadCI {C d : ℕ} {Λ : Type} (ι : EPadVL C d → Λ) (j : ℕ) : Λ :=
  if h : j < C then ι (.cInc ⟨j, h⟩) else epadDI ι 0

/-- **The validity block's code**, its labels embedded by `ι`, exiting to `yes` or `no`.
Registers: `0` pointer, `1` limit, `2` `|a| + 1`, `3` `|b|`, `4` power, `5` product,
`6` multiplier count, `7` addition count, `8` power count. Decider `0` is the input-bit
oracle. -/
private def epadValCode (wide : Bool) (C d : ℕ) {Λ : Type} (ι : EPadVL C d → Λ)
    (yes no : Λ) : EPadVL C d → Ins 18 2 Λ
  | .scan => .jeq 0 1 no (ι .first)
  | .first => .call 0 .whole [0] (ι (.adv 1 false)) (ι (.adv 0 false))
  | .test b => .jeq 0 1 no (ι (.read b))
  | .read b => .call 0 .whole [0] (if b then ι (.adv 2 false) else ι (.adv 3 false))
      (if b then no else ι (.adv 2 false))
  | .adv k false => .inc 0 (if wide then ι (.adv k true) else epadAdvEnd ι k)
  | .adv k true => .inc 0 (epadAdvEnd ι k)
  | .cpTest => .jeq 2 0 (ι .half1) (ι .cpBump)
  | .cpBump => .inc 2 (ι .cpTest)
  | .half1 => .half 2 (if wide then ι .half2 else ι .osTest)
  | .half2 => .half 2 (ι .osTest)
  | .osTest => .jeq 0 1 (epadCI ι 0) (ι .osRead)
  | .osRead => .call 0 .whole [0] (ι .osInc) no
  | .osInc => .inc 3 (ι (.osAdv false))
  | .osAdv false => .inc 0 (if wide then ι (.osAdv true) else ι .osTest)
  | .osAdv true => .inc 0 (ι .osTest)
  | .cInc i => .inc 4 (epadCI ι (i.val + 1))
  | .dInc i => .inc 8 (epadDI ι (i.val + 1))
  | .pw => .jz 8 (ι .cmp) (ι .pd)
  | .pd => .dec 8 (ι .mkTest)
  | .mkTest => .jeq 6 2 (ι .ml) (ι .mkBump)
  | .mkBump => .inc 6 (ι .mkTest)
  | .ml => .jz 6 (ι .mv) (ι .md)
  | .md => .dec 6 (ι .addT)
  | .addT => .jeq 7 4 (ι .scT) (ι .addB)
  | .addB => .inc 7 (ι .addT)
  | .scT => .jz 7 (ι .ml) (ι .scD)
  | .scD => .dec 7 (ι .scI)
  | .scI => .inc 5 (ι .scT)
  | .mv => .clr 4 (ι .mvTest)
  | .mvTest => .jeq 4 5 (ι .mvc) (ι .mvBump)
  | .mvBump => .inc 4 (ι .mvTest)
  | .mvc => .clr 5 (ι .pw)
  | .cmp => .jeq 3 4 yes no

/-- A decoded pair is padded exactly when its second field is the pad. -/
private lemma epad_valid_iff_of_decode {C d : ℕ} {y a b : List Bool}
    (h : pairDecode y = some (a, b)) :
    epadValid C d y ↔ b = List.replicate (C * (a.length + 1) ^ d) true := by
  constructor
  · rintro ⟨a', ha'⟩
    rw [ha', pairDecode_pairEncode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro hb
    exact ⟨a, by rw [eq_pairEncode_of_pairDecode y a b h, hb]⟩

/-- A word that is not a pair is not padded. -/
private lemma epad_not_valid_of_decode {C d : ℕ} {y : List Bool} (h : pairDecode y = none) :
    ¬ epadValid C d y := by
  rintro ⟨a, ha⟩
  rw [ha, pairDecode_pairEncode] at h
  cases h

/-- A word is a run of ones of length `n` exactly when all its letters are `1` and its length
is `n`. -/
private lemma epad_eq_replicate_iff (b : List Bool) (n : ℕ) :
    b = List.replicate n true ↔ (∀ i < b.length, b.getD i false = true) ∧ b.length = n := by
  rw [List.eq_replicate_iff]
  constructor
  · rintro ⟨hl, hm⟩
    refine ⟨fun i hi => ?_, hl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hm _ (List.getElem_mem hi)
  · rintro ⟨hm, hl⟩
    refine ⟨hl, fun c hc => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have := hm i hi
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

open Classical in
/-- **The validity block's run.** Started at `scan` with the pointer `0`, the limit
`s · |y|` (`s` the stride) and its working registers `2 … 8` clear, on an input whose
letters at `s · j` spell `y`, the block reaches `yes` if `y` is a padded word and `no`
otherwise. It leaves the registers from `9` on unchanged, keeps every register at most `B`,
and on a padded word leaves `|a| + 1` in register `2`. -/
private theorem epad_val_run {Λ : Type} (A : ARM 18 2 Λ) (oracle : Fin 2 → List Bool → Bool)
    (x y : List Bool) (wide : Bool) (C d : ℕ) (ι : EPadVL C d → Λ) (yes no : Λ)
    (hA : ∀ l, A (ι l) = epadValCode wide C d ι yes no l)
    (hy : ∀ j < y.length,
      oracle 0 (pairEncode x (Nat.bits (epadS wide * j))) = y.getD j false)
    (B : ℕ) (hB : C * (y.length + 1) ^ d + d + 2 * y.length + 2 ≤ B)
    (v : Fin 18 → ℕ) (hv : ∀ r, v r ≤ B) (h0 : v 0 = 0) (h1 : v 1 = epadS wide * y.length)
    (hz : ∀ r : Fin 18, 2 ≤ r.val → r.val ≤ 8 → v r = 0) :
    ∃ v', (∀ r : Fin 18, 9 ≤ r.val → v' r = v r) ∧ (∀ r, v' r ≤ B) ∧
      (epadValid C d y → v' 2 = (pairFstD y).length + 1) ∧
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some (ι .scan), v, none) (some (if epadValid C d y then yes else no), v', none) := by
  classical
  obtain ⟨s, hs_def⟩ : ∃ s, s = epadS wide := ⟨_, rfl⟩
  rw [← hs_def] at hy h1
  have hs1 : 1 ≤ s := by rw [hs_def, epadS]; split <;> omega
  have hs2 : s ≤ 2 := by rw [hs_def, epadS]; split <;> omega
  have hsy : s * y.length ≤ 2 * y.length := Nat.mul_le_mul_right _ hs2
  have hfar : ∀ r : Fin 18, 9 ≤ r.val → ∀ i : Fin 18, i.val ≤ 8 → r ≠ i := by
    intro r hr i hi h; rw [h] at hr; omega
  -- the pair scan
  have hadv : ∀ (k : Fin 4) (i : ℕ), i < s →
      A (epadAdv ι wide k i) = .inc 0 (epadAdv ι wide k (i + 1)) := by
    intro k i hi
    cases wide with
    | false =>
      have : i = 0 := by rw [hs_def] at hi; simp [epadS] at hi; omega
      subst this
      exact hA (.adv k false)
    | true =>
      rw [hs_def] at hi; simp only [epadS, if_true] at hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · exact hA (.adv k false)
      · exact hA (.adv k true)
  have hend : epadAdv ι wide 0 s = ι (.test false) ∧ epadAdv ι wide 1 s = ι (.test true) ∧
      epadAdv ι wide 2 s = ι .scan ∧ epadAdv ι wide 3 s = ι .cpTest := by
    rw [hs_def]; cases wide <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hap := alignedPair_loop A oracle x 0 1 0 (ι .scan) (ι .first) (fun b => ι (.test b))
    (fun b => ι (.read b)) no (ι .cpTest) (epadAdv ι wide) s B (by omega) (by decide)
    (hA .scan) (hA .first) (fun b => hA (.test b)) (fun b => hA (.read b)) hadv hend y v hv
    (by rw [h0, h1, Nat.zero_add]) (fun i hi => by rw [h0, Nat.zero_add]; exact hy i hi)
  cases hd : pairDecode y with
  | none =>
    simp only [hd] at hap
    obtain ⟨t, ht, hr⟩ := hap
    have hnv := epad_not_valid_of_decode (C := C) (d := d) hd
    refine ⟨Function.update v 0 (v 0 + s * t), fun r hr9 => ?_,
      register_update_le v 0 B _ hv ?_, fun h => absurd h hnv, ?_⟩
    · exact Function.update_of_ne (hfar r hr9 0 (by decide)) _ _
    · rw [h0, Nat.zero_add]
      exact (Nat.mul_le_mul_left s ht).trans (hsy.trans (by omega))
    · rw [if_neg hnv]; exact hr
  | some ab =>
    obtain ⟨a, b⟩ := ab
    simp only [hd] at hap
    have hy' : y = pairEncode a b := eq_pairEncode_of_pairDecode y a b hd
    have hlen : y.length = 2 * a.length + 2 + b.length := by rw [hy', length_pairEncode]
    have hfst : pairFstD y = a := by rw [hy', pairFstD_pairEncode]
    have hval : epadValid C d y ↔ b = List.replicate (C * (a.length + 1) ^ d) true :=
      epad_valid_iff_of_decode hd
    have hpowy : C * (a.length + 1) ^ d ≤ C * (y.length + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hpow1 : C ≤ C * (a.length + 1) ^ d :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos _))
    -- after the scan: the pointer at `s (2|a| + 2)`
    obtain ⟨v₁, hv₁⟩ : ∃ w, w = Function.update v 0 (v 0 + s * (2 * a.length + 2)) :=
      ⟨_, rfl⟩
    rw [← hv₁] at hap
    have hp₁ : s * (2 * a.length + 2) ≤ s * y.length := Nat.mul_le_mul_left _ (by omega)
    have b₁ : ∀ r, v₁ r ≤ B := by
      rw [hv₁]; exact register_update_le v 0 B _ hv (by rw [h0]; omega)
    -- `|a| + 1` into register `2`: copy the pointer, then halve
    have hcp := registerCopy_loop A oracle x 2 0 (by decide) (ι .cpTest) (ι .cpBump) (ι .half1)
      (hA .cpTest) (hA .cpBump) B v₁ b₁ (by
        rw [hv₁, Function.update_of_ne (by decide), hz 2 (by decide) (by decide)]
        exact Nat.zero_le _)
    obtain ⟨v₂, hv₂⟩ : ∃ w, w = Function.update v₁ 2 (v₁ 0) := ⟨_, rfl⟩
    rw [← hv₂] at hcp
    have b₂ : ∀ r, v₂ r ≤ B := by rw [hv₂]; exact register_update_le v₁ 2 B _ b₁ (b₁ 0)
    obtain ⟨v₃, hv₃⟩ : ∃ w, w = Function.update v₂ 2 (a.length + 1) := ⟨_, rfl⟩
    have b₃ : ∀ r, v₃ r ≤ B := by
      rw [hv₃]; exact register_update_le v₂ 2 B _ b₂ (by omega)
    have h₂₂ : v₂ 2 = s * (2 * a.length + 2) := by
      rw [hv₂, Function.update_self, hv₁, Function.update_self, h0, Nat.zero_add]
    have hhalf : AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some (ι .half1), v₂, none) (some (ι .osTest), v₃, none) := by
      cases wide with
      | false =>
        have hs : s = 1 := by rw [hs_def]; rfl
        have hc : A (ι .half1) = .half 2 (ι .osTest) := hA .half1
        refine AReach.step ⟨epad_preS hc trivial, b₂⟩ ?_
        rw [astep_half hc, h₂₂, hs, hv₃]
        have : 1 * (2 * a.length + 2) / 2 = a.length + 1 := by omega
        rw [this]
        exact AReach.refl _
      | true =>
        have hs : s = 2 := by rw [hs_def]; rfl
        have hc : A (ι .half1) = .half 2 (ι .half2) := hA .half1
        have hc' : A (ι .half2) = .half 2 (ι .osTest) := hA .half2
        refine AReach.step ⟨epad_preS hc trivial, b₂⟩ ?_
        rw [astep_half hc, h₂₂, hs]
        refine AReach.step
          ⟨epad_preS hc' trivial, register_update_le v₂ 2 B _ b₂ (by omega)⟩ ?_
        rw [astep_half hc', Function.update_self, Function.update_idem, hv₃]
        have : 2 * (2 * a.length + 2) / 2 / 2 = a.length + 1 := by omega
        rw [this]
        exact AReach.refl _
    -- the ones scan of the pad
    have hv₃0 : v₃ 0 = s * (2 * a.length + 2) := by
      rw [hv₃, Function.update_of_ne (by decide), hv₂, Function.update_of_ne (by decide), hv₁,
        Function.update_self, h0, Nat.zero_add]
    have hv₃1 : v₃ 1 = s * y.length := by
      rw [hv₃, Function.update_of_ne (by decide), hv₂, Function.update_of_ne (by decide), hv₁,
        Function.update_of_ne (by decide), h1]
    have hv₃r : ∀ r : Fin 18, 3 ≤ r.val → v₃ r = v r := by
      intro r hr
      have h2 : r ≠ 2 := fun h => by rw [h] at hr; simp at hr
      have h0' : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
      rw [hv₃, Function.update_of_ne h2, hv₂, Function.update_of_ne h2, hv₁,
        Function.update_of_ne h0']
    have hoadv : ∀ i < s, A (epadOsAdv ι wide i) = .inc 0 (epadOsAdv ι wide (i + 1)) := by
      intro i hi
      cases wide with
      | false =>
        have : i = 0 := by rw [hs_def] at hi; simp [epadS] at hi; omega
        subst this
        exact hA (.osAdv false)
      | true =>
        rw [hs_def] at hi; simp only [epadS, if_true] at hi
        obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
        · exact hA (.osAdv false)
        · exact hA (.osAdv true)
    have hoend : epadOsAdv ι wide s = ι .osTest := by rw [hs_def]; cases wide <;> rfl
    have hos := epad_ones_loop A oracle x 0 1 3 (by decide) (by decide) (by decide) 0
      (ι .osTest) (ι .osRead) (ι .osInc) (epadCI ι 0) no (epadOsAdv ι wide) s B
      (hA .osTest) (hA .osRead) (hA .osInc) hoadv hoend (by omega) b v₃ b₃
      (by rw [hv₃0, hv₃1, hlen, Nat.mul_add])
      (by rw [hv₃r 3 (by decide), hz 3 (by decide) (by decide)]; omega)
      (fun i hi => by
        have h := hy (2 * a.length + 2 + i) (by omega)
        rw [hy', pairEncode_getD_snd] at h
        rw [hv₃0, ← h, ← Nat.mul_add])
    by_cases hones : ∀ i < b.length, b.getD i false = true
    · -- the pad is all ones: load `C` and `d`, power, compare
      have hr4 := hos.1 hones
      obtain ⟨v₄, hv₄⟩ : ∃ w, w = Function.update (Function.update v₃ 0 (v₃ 1)) 3
          (v₃ 3 + b.length) := ⟨_, rfl⟩
      rw [← hv₄] at hr4
      have b₄ : ∀ r, v₄ r ≤ B := by
        rw [hv₄]
        exact register_update_le _ 3 B _ (register_update_le _ 0 B _ b₃ (b₃ 1))
          (by rw [hv₃r 3 (by decide), hz 3 (by decide) (by decide)]; omega)
      have hv₄r : ∀ r : Fin 18, 4 ≤ r.val → v₄ r = v r := by
        intro r hr
        have h3 : r ≠ 3 := fun h => by rw [h] at hr; simp at hr
        have h0' : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
        rw [hv₄, Function.update_of_ne h3, Function.update_of_ne h0', hv₃r r (by omega)]
      have hv₄2 : v₄ 2 = a.length + 1 := by
        rw [hv₄, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hv₃,
          Function.update_self]
      have hv₄3 : v₄ 3 = b.length := by
        rw [hv₄, Function.update_self, hv₃r 3 (by decide), hz 3 (by decide) (by decide),
          Nat.zero_add]
      -- `C` into register `4`
      have hc5 := arm_chain A oracle x 4 true (epadCI ι) C B (fun i hi => by
          rw [cond_true]
          have e1 : epadCI ι i = ι (.cInc ⟨i, hi⟩) := dif_pos hi
          rw [e1]
          exact hA (.cInc ⟨i, hi⟩)) v₄ b₄
        (by rw [cond_true, hv₄r 4 (by decide), hz 4 (by decide) (by decide)]; omega)
      have eC : epadCI ι C = epadDI ι 0 := dif_neg (Nat.lt_irrefl C)
      rw [eC, cond_true, hv₄r 4 (by decide), hz 4 (by decide) (by decide), Nat.zero_add] at hc5
      obtain ⟨v₅, hv₅⟩ : ∃ w, w = Function.update v₄ 4 C := ⟨_, rfl⟩
      rw [← hv₅] at hc5
      have b₅ : ∀ r, v₅ r ≤ B := by
        rw [hv₅]; exact register_update_le v₄ 4 B _ b₄ (by omega)
      -- `d` into register `8`
      have hc6 := arm_chain A oracle x 8 true (epadDI ι) d B (fun i hi => by
          rw [cond_true]
          have e1 : epadDI ι i = ι (.dInc ⟨i, hi⟩) := dif_pos hi
          rw [e1]
          exact hA (.dInc ⟨i, hi⟩)) v₅ b₅
        (by rw [cond_true, hv₅, Function.update_of_ne (by decide), hv₄r 8 (by decide),
              hz 8 (by decide) (by decide)]; omega)
      have eD : epadDI ι d = ι .pw := dif_neg (Nat.lt_irrefl d)
      have hv₅8 : v₅ 8 = 0 := by
        rw [hv₅, Function.update_of_ne (by decide), hv₄r 8 (by decide),
          hz 8 (by decide) (by decide)]
      rw [eD, cond_true, hv₅8, Nat.zero_add] at hc6
      obtain ⟨v₆, hv₆⟩ : ∃ w, w = Function.update v₅ 8 d := ⟨_, rfl⟩
      rw [← hv₆] at hc6
      have b₆ : ∀ r, v₆ r ≤ B := by
        rw [hv₆]; exact register_update_le v₅ 8 B _ b₅ (by omega)
      have hv₆r : ∀ r : Fin 18, r ≠ 4 → r ≠ 8 → v₆ r = v₄ r := by
        intro r h4 h8
        rw [hv₆, Function.update_of_ne h8, hv₅, Function.update_of_ne h4]
      -- the power loop: register `4` becomes `C (|a| + 1)^d`
      have hpw := epad_pow_loop A oracle x 2 8 6 7 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (ι .pw) (ι .pd) (ι .mkTest) (ι .mkBump) (ι .ml) (ι .md) (ι .addT) (ι .addB) (ι .scT)
        (ι .scD) (ι .scI) (ι .mv) (ι .mvTest) (ι .mvBump) (ι .mvc) (ι .cmp)
        (hA .pw) (hA .pd) (hA .mkTest) (hA .mkBump) (hA .ml) (hA .md) (hA .addT) (hA .addB)
        (hA .scT) (hA .scD) (hA .scI) (hA .mv) (hA .mvTest) (hA .mvBump) (hA .mvc) B d v₆
        (by rw [hv₆, Function.update_self])
        (by rw [hv₆r 5 (by decide) (by decide), hv₄r 5 (by decide), hz 5 (by decide) (by decide)])
        (by rw [hv₆r 6 (by decide) (by decide), hv₄r 6 (by decide), hz 6 (by decide) (by decide)])
        (by rw [hv₆r 7 (by decide) (by decide), hv₄r 7 (by decide), hz 7 (by decide) (by decide)])
        (by rw [hv₆r 2 (by decide) (by decide), hv₄2]; omega) b₆
        (by rw [hv₆r 2 (by decide) (by decide), hv₄2, hv₆, Function.update_of_ne (by decide),
              hv₅, Function.update_self]; omega)
      have hp6 : v₆ 4 * v₆ 2 ^ d = C * (a.length + 1) ^ d := by
        rw [hv₆r 2 (by decide) (by decide), hv₄2, hv₆, Function.update_of_ne (by decide), hv₅,
          Function.update_self]
      rw [hp6] at hpw
      obtain ⟨v₇, hv₇⟩ : ∃ w, w = Function.update (Function.update v₆ 8 0) 4
          (C * (a.length + 1) ^ d) := ⟨_, rfl⟩
      rw [← hv₇] at hpw
      have b₇ : ∀ r, v₇ r ≤ B := by
        rw [hv₇]
        exact register_update_le _ 4 B _ (register_update_le _ 8 B 0 b₆ (Nat.zero_le _))
          (by omega)
      have hv₇3 : v₇ 3 = b.length := by
        rw [hv₇, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          hv₆r 3 (by decide) (by decide), hv₄3]
      have hv₇4 : v₇ 4 = C * (a.length + 1) ^ d := by rw [hv₇, Function.update_self]
      have hv₇2 : v₇ 2 = a.length + 1 := by
        rw [hv₇, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          hv₆r 2 (by decide) (by decide), hv₄2]
      have hv₇r : ∀ r : Fin 18, 9 ≤ r.val → v₇ r = v r := by
        intro r hr
        have h4 : r ≠ 4 := hfar r hr 4 (by decide)
        have h8 : r ≠ 8 := hfar r hr 8 (by decide)
        rw [hv₇, Function.update_of_ne h4, Function.update_of_ne h8, hv₆r r h4 h8,
          hv₄r r (by omega)]
      have hiff : epadValid C d y ↔ b.length = C * (a.length + 1) ^ d := by
        rw [hval, epad_eq_replicate_iff]
        exact ⟨fun h => h.2, fun h => ⟨hones, h⟩⟩
      have hcmp : A (ι .cmp) = .jeq 3 4 yes no := hA .cmp
      refine ⟨v₇, hv₇r, b₇, fun _ => by rw [hv₇2, hfst], ?_⟩
      refine hap.trans (hcp.trans (hhalf.trans (hr4.trans (hc5.trans (hc6.trans
        (hpw.trans ?_))))))
      have hstep := AReach.single (A := A) (oracle := oracle) (x := x)
        (G := fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B) (a := (some (ι .cmp), v₇, none))
        ⟨epad_preS hcmp (show (3 : Fin 18) ≠ 4 by decide), b₇⟩
      rw [astep_jeq hcmp, hv₇3, hv₇4] at hstep
      by_cases hv' : epadValid C d y
      · rw [if_pos (hiff.mp hv')] at hstep
        rwa [if_pos hv']
      · rw [if_neg (fun h => hv' (hiff.mpr h))] at hstep
        rwa [if_neg hv']
    · -- a `0` in the pad: reject
      have hz0 : ∃ i < b.length, b.getD i false = false := by
        push_neg at hones
        obtain ⟨i, hi, h⟩ := hones
        exact ⟨i, hi, by simpa using h⟩
      obtain ⟨v', hv', hfr, hr⟩ := hos.2 hz0
      have hnv : ¬ epadValid C d y := fun h => hones ((epad_eq_replicate_iff _ _).mp
        (hval.mp h)).1
      refine ⟨v', fun r hr9 => ?_, hv', fun h => absurd h hnv, ?_⟩
      · rw [hfr r (hfar r hr9 0 (by decide)) (hfar r hr9 3 (by decide)), hv₃r r (by omega)]
      · rw [if_neg hnv]
        exact hap.trans (hcp.trans (hhalf.trans hr))

/-! ### The validator -/

/-- The validator's labels around the block: the length count and the two answers. -/
private inductive EPadVX where
  | lscan | linc | yes | no

/-- The validator's extra labels form a finite type (a local instance of the proofs). -/
private noncomputable def epadVXFintype : Fintype EPadVX := by
  classical
  exact Fintype.ofList [.lscan, .linc, .yes, .no] (fun l => by cases l <;> simp)

/-- **The validator**: count `|y|` into register `1`, run the validity block at stride `1`,
answer. -/
private def epadVA (C d : ℕ) : ARM 18 2 (EPadVL C d ⊕ EPadVX)
  | .inl l => epadValCode false C d Sum.inl (.inr .yes) (.inr .no) l
  | .inr .lscan => .call 1 .whole [1] (.inr .linc) (.inl .scan)
  | .inr .linc => .inc 1 (.inr .lscan)
  | .inr .yes => .ret true
  | .inr .no => .ret false

/-- The deciders the register machines call: the input's bits (`0`) and length (`1`). -/
private def epadIn : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

/-- Both input deciders are logspace. -/
private lemma epadIn_mem (j : Fin 2) : epadIn j ∈ LOGSPACE := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
  · show inputBitLang ∈ LOGSPACE
    exact inputBitLang_mem
  · show inputLenLang ∈ LOGSPACE
    exact inputLenLang_mem

/-- The oracle of the register machines: the input deciders' answers. -/
private noncomputable def epadOr : Fin 2 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (epadIn j : Set (List Bool)) V

/-- The input deciders' answers on a genuine query `⟨y, bits p⟩`: decider `0` reads letter `p`,
decider `1` compares `p` with `|y|`. -/
private lemma epadIn_answer (y : List Bool) (p : ℕ) :
    epadOr 0 (pairEncode y (Nat.bits p)) = y.getD p false ∧
      epadOr 1 (pairEncode y (Nat.bits p)) = decide (p < y.length) := by
  show MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _ ∧
    MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  exact ⟨indicator_inputBitLang y p, indicator_inputLenLang y p⟩

/-- The register bound of the validator and the bank: `(C + d + 8)(n + 1)^{d + 1}` covers
`C (n + 1)^d + d + 4n + 4`. -/
private lemma epad_bound (C d n : ℕ) :
    C * (n + 1) ^ d + d + 4 * n + 4 ≤ (C + d + 8) * (n + 1) ^ (d + 1) := by
  have hP : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have e : (C + d + 8) * (n + 1) ^ (d + 1) = C * (n + 1) ^ d * (n + 1) +
      d * ((n + 1) ^ d * (n + 1)) + 8 * ((n + 1) ^ d * (n + 1)) := by ring
  have h1 : C * (n + 1) ^ d ≤ C * (n + 1) ^ d * (n + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h3 : n + 1 ≤ (n + 1) ^ d * (n + 1) := Nat.le_mul_of_pos_left _ hP
  have h2 : d ≤ d * ((n + 1) ^ d * (n + 1)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The validator** (checkpoint 2): the padded words are decided in logarithmic space,
malformed inputs included.

**Proof sketch.** `arm_decides_poly` on `epadVA`: `inputLength_loop` loads `|y|`, then
`epad_val_run` at stride `1` reaches the answer `[y ∈ epadV]`; every register stays below
`(C + d + 8)(|y| + 1)^{d + 1}`. -/
private theorem epad_V_mem (C d : ℕ) : epadV C d ∈ LOGSPACE := by
  classical
  letI := epadVLFintype C d
  letI := epadVXFintype
  refine arm_decides_poly (epadVA C d) (.inr .lscan) epadIn epadIn_mem (C + d + 8) (d + 1)
    fun y => ?_
  have hB := epad_bound C d y.length
  have hlen := inputLength_loop (epadVA C d) epadOr y 1 1 (.inr .lscan)
    (.inr .linc) (.inl .scan) rfl rfl (fun n _ => (epadIn_answer y n).2)
    ((C + d + 8) * (y.length + 1) ^ (d + 1)) (by omega) (fun _ => 0)
    (fun _ => Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨v', -, hb, -, hr⟩ := epad_val_run (epadVA C d) epadOr y y false C d Sum.inl
    (.inr .yes) (.inr .no) (fun _ => rfl)
    (fun j _ => by rw [show epadS false * j = j from Nat.one_mul j]; exact (epadIn_answer y j).1)
    ((C + d + 8) * (y.length + 1) ^ (d + 1)) (by omega)
    (Function.update (fun _ => 0) 1 y.length)
    (register_update_le _ 1 _ _ (fun _ => Nat.zero_le _) (by omega))
    (by rw [Function.update_of_ne (by decide)])
    (by rw [Function.update_self]; exact (Nat.one_mul _).symm)
    (fun r h2 _ => by
      rw [Function.update_of_ne (fun h => by rw [h] at h2; simp at h2)])
  refine hlen.halt (hr.halt ?_)
  by_cases hv : epadValid C d y
  · have hy : MultiTapeTM.indicator (epadV C d : Set (List Bool)) y = true := by
      rw [indicator_eq_decide]; exact decide_eq_true (epad_mem_V.mpr hv)
    rw [if_pos hv, hy]
    exact AHalt.ret rfl ⟨epad_preS (show epadVA C d (.inr .yes) = .ret true from rfl) trivial, hb⟩
  · have hy : MultiTapeTM.indicator (epadV C d : Set (List Bool)) y = false := by
      rw [indicator_eq_decide]; exact decide_eq_false (fun h => hv (epad_mem_V.mp h))
    rw [if_neg hv, hy]
    exact AHalt.ret rfl ⟨epad_preS (show epadVA C d (.inr .no) = .ret false from rfl) trivial, hb⟩

/-! ### The bank (E-PAD checkpoint 3)

The bank answers the simulator's queries `⟨y, bits i⟩` about the virtual input `epadVirt y`.
On an input `z` it counts `|z|`, parses `z = ⟨y, w⟩`, checks that the index word `w` is
canonical and no wider than `|y|`, decodes `i = bitsVal w`, runs the validity block on `y` at
stride `2` (`y`'s letters are `z`'s doubled first field), and then seeks `i` below `|a|` with
stride `4` (letter `i` of `a` is letter `4i` of `z`): mode `false` answers whether it is found,
mode `true` reads the letter found. Registers `9` … `17`: `|z|`, the pointer, the tail base,
the cap, `i`, the decoder's scratch, and the seek's pointer, limit and index. -/

/-- The bank's labels around the validity block. -/
private inductive EPadBX where
  | lscan | linc
  | zscan | zfirst | ztest (b : Bool) | zread (b : Bool) | zadv (k : Fin 4)
  | c1T | c1B | c2T | c2B | dd1 | dd2 | c3T | c3B | hcap
  | ttest (b : Bool) | tcheck | tread | thalve (b : Bool) | tadv (b : Bool)
  | c4T | c4B
  | dtest | ddown | dread | dcopy (b : Bool) | dbump (b : Bool) | dclear (b : Bool)
  | dscale (b : Bool) | dtake (b : Bool) | dinc (b : Bool) (second : Bool) | dadd (b : Bool)
  | q1T | q1B | q1d | qsT | qsD | qsI (i : Fin 4)
  | seek | probe | bump | sadv (i : Fin 4) | hit
  | yes | no

/-- Every bank label, listed. -/
private def epadBXAll : List EPadBX :=
  [.lscan, .linc, .zscan, .zfirst, .ztest false, .ztest true, .zread false, .zread true] ++
  (List.finRange 4).map .zadv ++
  [.c1T, .c1B, .c2T, .c2B, .dd1, .dd2, .c3T, .c3B, .hcap, .ttest false, .ttest true, .tcheck,
    .tread, .thalve false, .thalve true, .tadv false, .tadv true, .c4T, .c4B, .dtest, .ddown,
    .dread] ++
  ([false, true].flatMap fun b => [.dcopy b, .dbump b, .dclear b, .dscale b, .dtake b,
    .dinc b false, .dinc b true, .dadd b]) ++
  [.q1T, .q1B, .q1d, .qsT, .qsD] ++ (List.finRange 4).map .qsI ++
  [.seek, .probe, .bump] ++ (List.finRange 4).map .sadv ++ [.hit, .yes, .no]

/-- The bank's labels form a finite type (a local instance of the proofs). -/
private noncomputable def epadBXFintype : Fintype EPadBX := by
  classical
  refine Fintype.ofList epadBXAll (fun l => ?_)
  cases l with
  | dcopy b => cases b <;> simp [epadBXAll]
  | dbump b => cases b <;> simp [epadBXAll]
  | dclear b => cases b <;> simp [epadBXAll]
  | dscale b => cases b <;> simp [epadBXAll]
  | dtake b => cases b <;> simp [epadBXAll]
  | dinc b c => cases b <;> cases c <;> simp [epadBXAll]
  | dadd b => cases b <;> simp [epadBXAll]
  | ztest b => cases b <;> simp [epadBXAll]
  | zread b => cases b <;> simp [epadBXAll]
  | ttest b => cases b <;> simp [epadBXAll]
  | thalve b => cases b <;> simp [epadBXAll]
  | tadv b => cases b <;> simp [epadBXAll]
  | _ => simp [epadBXAll]

/-- The targets of the outer pair scan's advances. -/
private def epadZEnd (k : Fin 4) : EPadBX :=
  if k = 0 then .ztest false else if k = 1 then .ztest true else if k = 2 then .zscan else .c1T

/-- **The bank** in mode `mode`, as an abstract register machine. -/
private def epadBA (C d : ℕ) (mode : Bool) : ARM 18 2 (EPadVL C d ⊕ EPadBX)
  | .inl l => epadValCode true C d Sum.inl (.inr .q1T) (.inr .no) l
  | .inr .lscan => .call 1 .whole [9] (.inr .linc) (.inr .zscan)
  | .inr .linc => .inc 9 (.inr .lscan)
  | .inr .zscan => .jeq 10 9 (.inr .no) (.inr .zfirst)
  | .inr .zfirst => .call 0 .whole [10] (.inr (.zadv 1)) (.inr (.zadv 0))
  | .inr (.ztest b) => .jeq 10 9 (.inr .no) (.inr (.zread b))
  | .inr (.zread b) => .call 0 .whole [10] (if b then .inr (.zadv 2) else .inr (.zadv 3))
      (if b then .inr .no else .inr (.zadv 2))
  | .inr (.zadv k) => .inc 10 (.inr (epadZEnd k))
  | .inr .c1T => .jeq 11 10 (.inr .c2T) (.inr .c1B)
  | .inr .c1B => .inc 11 (.inr .c1T)
  | .inr .c2T => .jeq 1 10 (.inr .dd1) (.inr .c2B)
  | .inr .c2B => .inc 1 (.inr .c2T)
  | .inr .dd1 => .dec 1 (.inr .dd2)
  | .inr .dd2 => .dec 1 (.inr .c3T)
  | .inr .c3T => .jeq 12 1 (.inr .hcap) (.inr .c3B)
  | .inr .c3B => .inc 12 (.inr .c3T)
  | .inr .hcap => .half 12 (.inr (.ttest true))
  | .inr (.ttest b) => .jeq 10 9 (if b then .inr .c4T else .inr .no) (.inr .tcheck)
  | .inr .tcheck => .jz 12 (.inr .no) (.inr .tread)
  | .inr .tread => .call 0 .whole [10] (.inr (.thalve true)) (.inr (.thalve false))
  | .inr (.thalve b) => .half 12 (.inr (.tadv b))
  | .inr (.tadv b) => .inc 10 (.inr (.ttest b))
  | .inr .c4T => .jeq 10 9 (.inr .dtest) (.inr .c4B)
  | .inr .c4B => .inc 10 (.inr .c4T)
  | .inr .dtest => .jeq 10 11 (.inl .scan) (.inr .ddown)
  | .inr .ddown => .dec 10 (.inr .dread)
  | .inr .dread => .call 0 .whole [10] (.inr (.dcopy true)) (.inr (.dcopy false))
  | .inr (.dcopy b) => .jeq 14 13 (.inr (.dclear b)) (.inr (.dbump b))
  | .inr (.dbump b) => .inc 14 (.inr (.dcopy b))
  | .inr (.dclear b) => .clr 13 (.inr (.dscale b))
  | .inr (.dscale b) => .jz 14 (.inr (.dadd b)) (.inr (.dtake b))
  | .inr (.dtake b) => .dec 14 (.inr (.dinc b false))
  | .inr (.dinc b false) => .inc 13 (.inr (.dinc b true))
  | .inr (.dinc b true) => .inc 13 (.inr (.dscale b))
  | .inr (.dadd b) => if b then .inc 13 (.inr .dtest) else .jz 14 (.inr .dtest) (.inr .dtest)
  | .inr .q1T => .jeq 17 2 (.inr .q1d) (.inr .q1B)
  | .inr .q1B => .inc 17 (.inr .q1T)
  | .inr .q1d => .dec 17 (.inr .qsT)
  | .inr .qsT => .jz 17 (.inr .seek) (.inr .qsD)
  | .inr .qsD => .dec 17 (.inr (.qsI 0))
  | .inr (.qsI i) => .inc 16 (if i = 3 then .inr .qsT else .inr (.qsI (i + 1)))
  | .inr .seek => .jeq 15 16 (.inr .no) (.inr .probe)
  | .inr .probe => .jeq 17 13 (.inr .hit) (.inr .bump)
  | .inr .bump => .inc 17 (.inr (.sadv 0))
  | .inr (.sadv i) => .inc 15 (if i = 3 then .inr .seek else .inr (.sadv (i + 1)))
  | .inr .hit => if mode then .call 0 .whole [15] (.inr .yes) (.inr .no) else .ret true
  | .inr .yes => .ret true
  | .inr .no => .ret false

/-- **The bank's last phase.** From `q1T`, with `na + 1` in register `2`, the index `i` in
register `13` and the seek registers `15`, `16`, `17` clear, the bank answers: in mode `false`
whether `i < na`; in mode `true` letter `4i` of the input if `i < na`, and `0` otherwise.

**Proof sketch.** `registerCopy_loop` and one decrement load `na` into register `17`;
`registerScale_loop` at factor `4` moves `4 na` into the seek limit `16`; `indexedSeek_loop` at
stride `4` hits exactly when `i < na`, with its pointer at `4i`. -/
private theorem epad_bank_post (C d : ℕ) (mode : Bool) (z : List Bool) (B na i : ℕ)
    (v : Fin 18 → ℕ) (hv : ∀ r, v r ≤ B) (h2 : v 2 = na + 1) (h13 : v 13 = i)
    (h15 : v 15 = 0) (h16 : v 16 = 0) (h17 : v 17 = 0) (hB : 4 * na + 1 ≤ B) :
    AHalt (epadBA C d mode) epadOr z
      (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B) (some (.inr .q1T), v, none)
      (if i < na then (if mode then z.getD (4 * i) false else true) else false) := by
  -- `17 := na + 1`, then `na`
  have hc1 := registerCopy_loop (epadBA C d mode) epadOr z 17 2 (by decide) (.inr .q1T)
    (.inr .q1B) (.inr .q1d) rfl rfl B v hv (by rw [h17]; exact Nat.zero_le _)
  obtain ⟨v₁, hv₁⟩ : ∃ w, w = Function.update v 17 (v 2) := ⟨_, rfl⟩
  rw [← hv₁] at hc1
  have b₁ : ∀ r, v₁ r ≤ B := by rw [hv₁]; exact register_update_le v 17 B _ hv (hv 2)
  obtain ⟨v₂, hv₂⟩ : ∃ w, w = Function.update v₁ 17 na := ⟨_, rfl⟩
  have b₂ : ∀ r, v₂ r ≤ B := by rw [hv₂]; exact register_update_le v₁ 17 B _ b₁ (by omega)
  have hd : AReach (epadBA C d mode) epadOr z
      (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B) (some (.inr .q1d), v₁, none)
      (some (.inr .qsT), v₂, none) := by
    have hc : epadBA C d mode (.inr .q1d) = .dec 17 (.inr .qsT) := rfl
    refine AReach.step ⟨epad_preS hc trivial, b₁⟩ ?_
    rw [astep_dec hc, hv₂, hv₁, Function.update_self, h2, Nat.add_sub_cancel,
      Function.update_idem]
    exact AReach.refl _
  -- `16 += 4 · 17`, `17 := 0`
  have hsc := registerScale_loop (epadBA C d mode) epadOr z 17 16 (by decide) (.inr .qsT)
    (.inr .qsD) (.inr .seek) (fun i => if h : i < 4 then .inr (.qsI ⟨i, h⟩) else .inr .qsT) 4
    rfl rfl (fun i hi => by
      obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      all_goals rfl) rfl B v₂ b₂ (by
        rw [hv₂, Function.update_self, Function.update_of_ne (by decide), hv₁,
          Function.update_of_ne (by decide), h16]
        omega)
  obtain ⟨v₃, hv₃⟩ : ∃ w, w = Function.update (Function.update v₂ 17 0) 16
      (v₂ 16 + 4 * v₂ 17) := ⟨_, rfl⟩
  rw [← hv₃] at hsc
  have h₃ : ∀ r, v₃ r = if r = 16 then 4 * na else if r = 17 then 0 else v r := by
    intro r
    rw [hv₃, hv₂, hv₁]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h16]
    split_ifs <;> subst_vars <;> simp_all
  have b₃ : ∀ r, v₃ r ≤ B := by
    intro r; rw [h₃]; split_ifs
    · omega
    · exact Nat.zero_le _
    · exact hv r
  -- the seek
  have hseek := indexedSeek_loop (epadBA C d mode) epadOr z 15 16 17 13 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (.inr .seek) (.inr .probe) (.inr .bump)
    (.inr .hit) (.inr .no) (fun i => if h : i < 4 then .inr (.sadv ⟨i, h⟩) else .inr .seek) 4 B
    (by omega) rfl rfl rfl (fun i hi => by
      obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      all_goals rfl) rfl na v₃ b₃
    (by rw [h₃, h₃]; simp only [Fin.reduceEq, ↓reduceIte, h15]; omega)
    (by rw [h₃]; simp only [Fin.reduceEq, ↓reduceIte]; omega)
    (by rw [h₃]; simp only [Fin.reduceEq, ↓reduceIte]; exact Nat.zero_le _)
  have h313 : v₃ 13 = i := by rw [h₃]; simp only [Fin.reduceEq, ↓reduceIte, h13]
  have h317 : v₃ 17 = 0 := by rw [h₃]; simp only [Fin.reduceEq, ↓reduceIte]
  have h315 : v₃ 15 = 0 := by rw [h₃]; simp only [Fin.reduceEq, ↓reduceIte, h15]
  rw [h313, h317, Nat.zero_add] at hseek
  refine hc1.halt (hd.halt (hsc.halt ?_))
  by_cases hi : i < na
  · rw [if_pos hi] at hseek ⊢
    obtain ⟨v₄, hv₄⟩ : ∃ w, w = Function.update (Function.update v₃ 15 (v₃ 15 + 4 * (i - 0)))
        17 i := ⟨_, rfl⟩
    rw [← hv₄] at hseek
    have b₄ : ∀ r, v₄ r ≤ B := by
      rw [hv₄]
      refine register_update_le _ 17 B _ (register_update_le _ 15 B _ b₃ ?_) (by omega)
      rw [h315]; omega
    have h415 : v₄ 15 = 4 * i := by
      rw [hv₄, Function.update_of_ne (by decide), Function.update_self, h315]; omega
    refine hseek.halt ?_
    cases mode with
    | false =>
      exact AHalt.ret rfl ⟨epad_preS (show epadBA C d false (.inr .hit) = .ret true from rfl)
        trivial, b₄⟩
    | true =>
      have hc : epadBA C d true (.inr .hit) = .call 0 .whole [15] (.inr .yes) (.inr .no) := rfl
      refine AHalt.step ⟨epad_preS hc (List.nodup_singleton _), b₄⟩ ?_
      rw [astep_call hc, vword_whole₁, h415]
      have ho : epadOr 0 (pairEncode z (Nat.bits (4 * i))) = z.getD (4 * i) false :=
        (epadIn_answer z (4 * i)).1
      rw [ho]
      cases hb : z.getD (4 * i) false
      · exact AHalt.ret rfl ⟨epad_preS (show epadBA C d true (.inr .no) = .ret false from rfl)
          trivial, b₄⟩
      · exact AHalt.ret rfl ⟨epad_preS (show epadBA C d true (.inr .yes) = .ret true from rfl)
          trivial, b₄⟩
  · rw [if_neg hi] at hseek ⊢
    obtain ⟨v₄, hv₄⟩ : ∃ w, w = Function.update (Function.update v₃ 15 (v₃ 16)) 17 na :=
      ⟨_, rfl⟩
    rw [← hv₄] at hseek
    have b₄ : ∀ r, v₄ r ≤ B := by
      rw [hv₄]
      exact register_update_le _ 17 B _ (register_update_le _ 15 B _ b₃ (b₃ 16)) (by omega)
    exact hseek.halt (AHalt.ret rfl ⟨epad_preS
      (show epadBA C d mode (.inr .no) = .ret false from rfl) trivial, b₄⟩)

/-- A number of `|bits n|` binary digits is below `2 n + 2`: `2 ^ |bits n| ≤ 2 n + 1`. -/
private lemma epad_two_pow_bits (n : ℕ) : 2 ^ (Nat.bits n).length ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits]
  · have h1 := length_bits_le_log n
    have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    calc 2 ^ (Nat.bits n).length ≤ 2 ^ (Nat.log 2 n + 1) := Nat.pow_le_pow_right (by omega) h1
      _ = 2 * 2 ^ Nat.log 2 n := by rw [pow_succ]; ring
      _ ≤ 2 * n + 1 := by omega

/-- **The bank's first phase.** From the start, the bank counts `|z|` and parses
`z = ⟨y, w⟩`; it rejects a word that is not a pair, or whose index word `w` is not canonical
or wider than `|y|`; otherwise it decodes `i = bitsVal w` into register `13` and enters the
validity block with its pointer `0`, its limit `2 |y|` and its working registers clear, the
seek registers `15`–`17` clear, all registers at most `B`.

**Proof sketch.** `inputLength_loop`; `alignedPair_loop` at stride `1` on `z`; three
`registerCopy_loop`s, two decrements and a halving set the tail base `2|y| + 2`, the block's
limit `2|y|` and the cap `|y|`; `canonicalTail_loop` checks the index word; one more copy moves
the pointer to the end, and `boundedDecode_loop` decodes the index (its values stay below
`2 ^ |bits |y||` by `Codec.bitsVal_lt_two_pow`). -/
private theorem epad_bank_pre (C d : ℕ) (mode : Bool) (z : List Bool) (B : ℕ)
    (hB : 2 * z.length + 1 ≤ B) :
    (pairDecode z = none → ∃ v, (∀ r, v r ≤ B) ∧
      AReach (epadBA C d mode) epadOr z (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B)
        (some (.inr .lscan), fun _ => 0, none) (some (.inr .no), v, none)) ∧
    (∀ y w, pairDecode z = some (y, w) →
      (¬ (w.getLastD true = true ∧ w.length ≤ (Nat.bits y.length).length) → ∃ v, (∀ r, v r ≤ B) ∧
        AReach (epadBA C d mode) epadOr z
          (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B)
          (some (.inr .lscan), fun _ => 0, none) (some (.inr .no), v, none)) ∧
      (w.getLastD true = true ∧ w.length ≤ (Nat.bits y.length).length → ∃ v, (∀ r, v r ≤ B) ∧
        v 0 = 0 ∧ v 1 = 2 * y.length ∧ (∀ r : Fin 18, 2 ≤ r.val → r.val ≤ 8 → v r = 0) ∧
        v 13 = LogProg.bitsVal w ∧ v 15 = 0 ∧ v 16 = 0 ∧ v 17 = 0 ∧
        AReach (epadBA C d mode) epadOr z
          (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B)
          (some (.inr .lscan), fun _ => 0, none) (some (.inl .scan), v, none))) := by
  -- the length
  have hlen := inputLength_loop (epadBA C d mode) epadOr z 9 1 (.inr .lscan) (.inr .linc)
    (.inr .zscan) rfl rfl (fun n _ => (epadIn_answer z n).2) B (by omega) (fun _ => 0)
    (fun _ => Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨v₀, hv₀⟩ : ∃ w, w = Function.update (fun _ : Fin 18 => 0) 9 z.length := ⟨_, rfl⟩
  rw [← hv₀] at hlen
  have b₀ : ∀ r, v₀ r ≤ B := by
    rw [hv₀]; exact register_update_le _ 9 B _ (fun _ => Nat.zero_le _) (by omega)
  have h₀ : ∀ r : Fin 18, r ≠ 9 → v₀ r = 0 := fun r hr => by
    rw [hv₀, Function.update_of_ne hr]
  have h₀9 : v₀ 9 = z.length := by rw [hv₀, Function.update_self]
  -- the outer pair scan
  have hap := alignedPair_loop (epadBA C d mode) epadOr z 10 9 0 (.inr .zscan) (.inr .zfirst)
    (fun b => .inr (.ztest b)) (fun b => .inr (.zread b)) (.inr .no) (.inr .c1T)
    (fun k i => if i = 0 then .inr (.zadv k) else .inr (epadZEnd k)) 1 B (by omega) (by decide)
    rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun k i hi => by obtain rfl : i = 0 := by omega
                      rfl)
    ⟨rfl, rfl, rfl, rfl⟩ z v₀ b₀ (by rw [h₀9, h₀ 10 (by decide)]; omega)
    (fun i _ => by rw [h₀ 10 (by decide), Nat.zero_add, Nat.one_mul]
                   exact (epadIn_answer z i).1)
  refine ⟨fun hd => ?_, fun y w hd => ?_⟩
  · simp only [hd] at hap
    obtain ⟨t, ht, hr⟩ := hap
    exact ⟨_, register_update_le v₀ 10 B _ b₀ (by rw [h₀ 10 (by decide)]; omega), hlen.trans hr⟩
  simp only [hd] at hap
  have hz : z = pairEncode y w := eq_pairEncode_of_pairDecode z y w hd
  have hzl : z.length = 2 * y.length + 2 + w.length := by rw [hz, length_pairEncode]
  obtain ⟨v₁, hv₁⟩ : ∃ u, u = Function.update v₀ 10 (v₀ 10 + 1 * (2 * y.length + 2)) :=
    ⟨_, rfl⟩
  rw [← hv₁] at hap
  have b₁ : ∀ r, v₁ r ≤ B := by
    rw [hv₁]; exact register_update_le v₀ 10 B _ b₀ (by rw [h₀ 10 (by decide)]; omega)
  have h₁10 : v₁ 10 = 2 * y.length + 2 := by
    rw [hv₁, Function.update_self, h₀ 10 (by decide)]; omega
  -- the tail base, the block's limit and the cap
  have hc1 := registerCopy_loop (epadBA C d mode) epadOr z 11 10 (by decide) (.inr .c1T)
    (.inr .c1B) (.inr .c2T) rfl rfl B v₁ b₁ (by
      rw [hv₁, Function.update_of_ne (by decide), h₀ 11 (by decide)]; exact Nat.zero_le _)
  obtain ⟨v₂, hv₂⟩ : ∃ u, u = Function.update v₁ 11 (v₁ 10) := ⟨_, rfl⟩
  rw [← hv₂] at hc1
  have b₂ : ∀ r, v₂ r ≤ B := by rw [hv₂]; exact register_update_le v₁ 11 B _ b₁ (b₁ 10)
  have hc2 := registerCopy_loop (epadBA C d mode) epadOr z 1 10 (by decide) (.inr .c2T)
    (.inr .c2B) (.inr .dd1) rfl rfl B v₂ b₂ (by
      rw [hv₂, Function.update_of_ne (by decide), hv₁, Function.update_of_ne (by decide),
        h₀ 1 (by decide)]
      exact Nat.zero_le _)
  obtain ⟨v₃, hv₃⟩ : ∃ u, u = Function.update v₂ 1 (v₂ 10) := ⟨_, rfl⟩
  rw [← hv₃] at hc2
  have b₃ : ∀ r, v₃ r ≤ B := by rw [hv₃]; exact register_update_le v₂ 1 B _ b₂ (b₂ 10)
  have h₂10 : v₂ 10 = 2 * y.length + 2 := by
    rw [hv₂, Function.update_of_ne (by decide), h₁10]
  obtain ⟨v₄, hv₄⟩ : ∃ u, u = Function.update v₃ 1 (2 * y.length) := ⟨_, rfl⟩
  have b₄ : ∀ r, v₄ r ≤ B := by rw [hv₄]; exact register_update_le v₃ 1 B _ b₃ (by omega)
  have hdd : AReach (epadBA C d mode) epadOr z
      (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B) (some (.inr .dd1), v₃, none)
      (some (.inr .c3T), v₄, none) := by
    have hc : epadBA C d mode (.inr .dd1) = .dec 1 (.inr .dd2) := rfl
    have hc' : epadBA C d mode (.inr .dd2) = .dec 1 (.inr .c3T) := rfl
    refine AReach.step ⟨epad_preS hc trivial, b₃⟩ ?_
    rw [astep_dec hc]
    refine AReach.step ⟨epad_preS hc' trivial,
      register_update_le v₃ 1 B _ b₃ ((Nat.sub_le _ _).trans (b₃ 1))⟩ ?_
    rw [astep_dec hc']
    have e : Function.update (Function.update v₃ 1 (v₃ 1 - 1)) 1
        (Function.update v₃ 1 (v₃ 1 - 1) 1 - 1) = v₄ := by
      rw [hv₄, hv₃]
      funext s
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [e]
    exact AReach.refl _
  have hc3 := registerCopy_loop (epadBA C d mode) epadOr z 12 1 (by decide) (.inr .c3T)
    (.inr .c3B) (.inr .hcap) rfl rfl B v₄ b₄ (by
      rw [hv₄, Function.update_of_ne (by decide), hv₃, Function.update_of_ne (by decide), hv₂,
        Function.update_of_ne (by decide), hv₁, Function.update_of_ne (by decide),
        h₀ 12 (by decide)]
      exact Nat.zero_le _)
  obtain ⟨v₅, hv₅⟩ : ∃ u, u = Function.update v₄ 12 (v₄ 1) := ⟨_, rfl⟩
  rw [← hv₅] at hc3
  have b₅ : ∀ r, v₅ r ≤ B := by rw [hv₅]; exact register_update_le v₄ 12 B _ b₄ (b₄ 1)
  obtain ⟨v₆, hv₆⟩ : ∃ u, u = Function.update v₅ 12 y.length := ⟨_, rfl⟩
  have b₆ : ∀ r, v₆ r ≤ B := by rw [hv₆]; exact register_update_le v₅ 12 B _ b₅ (by omega)
  have hhc : AReach (epadBA C d mode) epadOr z
      (fun a => PreS (epadBA C d mode) z a ∧ ∀ r, a.2.1 r ≤ B) (some (.inr .hcap), v₅, none)
      (some (.inr (.ttest true)), v₆, none) := by
    have hc : epadBA C d mode (.inr .hcap) = .half 12 (.inr (.ttest true)) := rfl
    refine AReach.step ⟨epad_preS hc trivial, b₅⟩ ?_
    rw [astep_half hc]
    have e : Function.update v₅ 12 (v₅ 12 / 2) = v₆ := by
      rw [hv₆, hv₅]
      funext s
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [e]
    exact AReach.refl _
  -- the register file before the tail check
  have h₆ : ∀ r : Fin 18, v₆ r = if r = 1 then 2 * y.length else if r = 9 then z.length
      else if r = 10 then 2 * y.length + 2 else if r = 11 then 2 * y.length + 2
      else if r = 12 then y.length else 0 := by
    intro r
    rw [hv₆, hv₅, hv₄, hv₃, hv₂, hv₁, hv₀]
    simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    split_ifs <;> simp_all
  -- the tail check
  have hct := canonicalTail_loop (epadBA C d mode) epadOr z 10 9 12 (by decide) (by decide)
    (by decide) 0 (fun b => .inr (.ttest b)) (.inr .tcheck) (.inr .tread) (.inr .no) (.inr .c4T)
    (fun b => .inr (.thalve b)) (fun b i => if i = 0 then .inr (.tadv b) else .inr (.ttest b))
    1 B (by omega) (fun _ => rfl) rfl rfl (fun _ => rfl)
    (fun b i hi => by obtain rfl : i = 0 := by omega
                      rfl)
    (fun _ => rfl) w true v₆ b₆ (by rw [h₆, h₆]; simp only [Fin.reduceEq, ↓reduceIte]; omega)
    (fun i hi => by
      rw [h₆]; simp only [Fin.reduceEq, ↓reduceIte, Nat.one_mul]
      rw [(epadIn_answer z _).1, hz, pairEncode_getD_snd])
  obtain ⟨v', b', hp', hfr', hct⟩ := hct
  have h612 : v₆ 12 = y.length := by rw [h₆]; simp only [Fin.reduceEq, ↓reduceIte]
  rw [h612] at hct
  refine ⟨fun hbad => ?_, fun hok => ?_⟩
  · have hno : (if w.length ≤ (Nat.bits y.length).length then
        (if w.getLastD true = true then (Sum.inr EPadBX.c4T : EPadVL C d ⊕ EPadBX)
          else .inr .no) else .inr .no) = .inr .no := by
      split_ifs with h1 h2
      · exact absurd ⟨h2, h1⟩ hbad
      · rfl
      · rfl
    rw [hno] at hct
    exact ⟨v', b', hlen.trans (hap.trans (hc1.trans (hc2.trans (hdd.trans (hc3.trans
      (hhc.trans hct))))))⟩
  rw [if_pos hok.2, if_pos hok.1] at hct
  -- the pointer to the end, then the decoder
  have h'9 : v' 9 = z.length := by
    rw [hfr' 9 (by decide) (by decide), h₆]; simp only [Fin.reduceEq, ↓reduceIte]
  have hc4 := registerCopy_loop (epadBA C d mode) epadOr z 10 9 (by decide) (.inr .c4T)
    (.inr .c4B) (.inr .dtest) rfl rfl B v' b' (by
      rw [h'9]; rw [h₆] at hp'; simp only [Fin.reduceEq, ↓reduceIte] at hp'; exact hp')
  obtain ⟨v₇, hv₇⟩ : ∃ u, u = Function.update v' 10 (v' 9) := ⟨_, rfl⟩
  rw [← hv₇] at hc4
  have b₇ : ∀ r, v₇ r ≤ B := by rw [hv₇]; exact register_update_le v' 10 B _ b' (b' 9)
  have h₇ : ∀ r : Fin 18, r ≠ 10 → r ≠ 12 → v₇ r = v₆ r := fun r h10 h12 => by
    rw [hv₇, Function.update_of_ne h10, hfr' r h10 h12]
  have hw : w.length ≤ (Nat.bits y.length).length := hok.2
  have hval : ∀ i ≤ w.length, LogProg.bitsVal (w.drop i) ≤ B := by
    intro i _
    have h1 := Codec.bitsVal_lt_two_pow (w.drop i)
    have h2 : 2 ^ (w.drop i).length ≤ 2 ^ (Nat.bits y.length).length :=
      Nat.pow_le_pow_right (by omega) ((by simp : (w.drop i).length ≤ w.length).trans hw)
    have h3 := epad_two_pow_bits y.length
    omega
  have hdec := boundedDecode_loop (epadBA C d mode) epadOr z 10 11 13 14 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) 0 (.inr .dtest) (.inr .ddown)
    (.inr .dread) (.inl .scan) (fun b => .inr (.dcopy b)) (fun b => .inr (.dbump b))
    (fun b => .inr (.dclear b)) (fun b => .inr (.dscale b)) (fun b => .inr (.dtake b))
    (fun b => .inr (.dadd b))
    (fun b i => if i = 0 then .inr (.dinc b false) else if i = 1 then .inr (.dinc b true)
      else .inr (.dscale b))
    rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun b i hi => by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      all_goals rfl)
    (fun _ => rfl) (fun b => by cases b <;> rfl) w B hval w.length le_rfl v₇ b₇
    (by rw [hv₇, Function.update_self, h'9, Function.update_of_ne (by decide),
          hfr' 11 (by decide) (by decide), h₆]
        simp only [Fin.reduceEq, ↓reduceIte]; omega)
    (by rw [h₇ 13 (by decide) (by decide), h₆, List.drop_length]
        simp only [Fin.reduceEq, ↓reduceIte]
        rw [← Nat.zero_bits, LogProg.bitsVal_bits])
    (by rw [h₇ 14 (by decide) (by decide), h₆]; simp only [Fin.reduceEq, ↓reduceIte])
    (fun i hi => by
      rw [h₇ 11 (by decide) (by decide), h₆]; simp only [Fin.reduceEq, ↓reduceIte]
      rw [(epadIn_answer z _).1, hz, pairEncode_getD_snd])
  obtain ⟨v'', b'', -, h''13, -, hfr'', hdec⟩ := hdec
  have h'' : ∀ r : Fin 18, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 14 → v'' r = v₆ r :=
    fun r h10 h12 h13 h14 => by rw [hfr'' r h10 h13 h14, h₇ r h10 h12]
  refine ⟨v'', b'', ?_, ?_, fun r h2 h8 => ?_, h''13, ?_, ?_, ?_, hlen.trans (hap.trans
    (hc1.trans (hc2.trans (hdd.trans (hc3.trans (hhc.trans (hct.trans (hc4.trans hdec))))))))⟩
  · rw [h'' 0 (by decide) (by decide) (by decide) (by decide), h₆]
    simp only [Fin.reduceEq, ↓reduceIte]
  · rw [h'' 1 (by decide) (by decide) (by decide) (by decide), h₆]
    simp only [↓reduceIte]
  · have hne : ∀ k : Fin 18, 9 ≤ k.val → r ≠ k := fun k hk h => by rw [h] at h8; omega
    have hne1 : r ≠ 1 := fun h => by rw [h] at h2; simp at h2
    rw [h'' r (hne 10 (by decide)) (hne 12 (by decide)) (hne 13 (by decide))
      (hne 14 (by decide)), h₆, if_neg hne1, if_neg (hne 9 (by decide)),
      if_neg (hne 10 (by decide)), if_neg (hne 11 (by decide)), if_neg (hne 12 (by decide))]
  · rw [h'' 15 (by decide) (by decide) (by decide) (by decide), h₆]
    simp only [Fin.reduceEq, ↓reduceIte]
  · rw [h'' 16 (by decide) (by decide) (by decide) (by decide), h₆]
    simp only [Fin.reduceEq, ↓reduceIte]
  · rw [h'' 17 (by decide) (by decide) (by decide) (by decide), h₆]
    simp only [Fin.reduceEq, ↓reduceIte]

/-- Letter `4i` of `⟨⟨a, b⟩, w⟩` is letter `i` of `a`, for `i < |a|`. -/
private lemma epad_getD_four (a b w : List Bool) (i : ℕ) (hi : i < a.length) :
    (pairEncode (pairEncode a b) w).getD (4 * i) false = a.getD i false := by
  rw [pairEncode_getD, if_pos (by rw [length_pairEncode]; omega),
    show 4 * i / 2 = 2 * i by omega, pairEncode_getD, if_pos (by omega),
    show 2 * i / 2 = i by omega]

/-- **The bank** (checkpoint 3): both query languages are decided in logarithmic space.

**Proof sketch.** `arm_decides_poly` on `epadBA`: the first phase `epad_bank_pre` parses the
query and decodes its index (rejecting malformed queries), the validity block `epad_val_run`
runs at stride `2` on the first field (rejecting unpadded words), and `epad_bank_post` answers.
Registers stay below `(C + d + 8)(|z| + 1)^{d + 1}`. -/
private theorem epad_Q_mem (C d : ℕ) (mode : Bool) : epadQ C d mode ∈ LOGSPACE := by
  classical
  letI := epadVLFintype C d
  letI := epadBXFintype
  refine arm_decides_poly (epadBA C d mode) (.inr .lscan) epadIn epadIn_mem (C + d + 8) (d + 1)
    fun z => ?_
  have hB := epad_bound C d z.length
  obtain ⟨hnone, hsome⟩ := epad_bank_pre C d mode z ((C + d + 8) * (z.length + 1) ^ (d + 1))
    (by omega)
  have hno : ∀ v : Fin 18 → ℕ, (∀ r, v r ≤ (C + d + 8) * (z.length + 1) ^ (d + 1)) →
      AHalt (epadBA C d mode) epadOr z (fun a => PreS (epadBA C d mode) z a ∧
        ∀ r, a.2.1 r ≤ (C + d + 8) * (z.length + 1) ^ (d + 1)) (some (.inr .no), v, none)
        false := fun v hv =>
    AHalt.ret rfl ⟨epad_preS (show epadBA C d mode (.inr .no) = .ret false from rfl) trivial, hv⟩
  cases hd : pairDecode z with
  | none =>
    obtain ⟨v, hv, hr⟩ := hnone hd
    have hans : MultiTapeTM.indicator (epadQ C d mode : Set (List Bool)) z = false := by
      rw [indicator_eq_decide]; exact decide_eq_false (epad_not_mem_Q hd)
    rw [hans]
    exact hr.halt (hno v hv)
  | some yw =>
    obtain ⟨y, w⟩ := yw
    obtain ⟨hbad, hok⟩ := hsome y w hd
    have hz : z = pairEncode y w := eq_pairEncode_of_pairDecode z y w hd
    have hzl : z.length = 2 * y.length + 2 + w.length := by rw [hz, length_pairEncode]
    by_cases hw : w.getLastD true = true ∧ w.length ≤ (Nat.bits y.length).length
    · obtain ⟨v, hv, h0, h1, hzr, h13, h15, h16, h17, hr⟩ := hok hw
      have hpowy : C * (y.length + 1) ^ d ≤ C * (z.length + 1) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      obtain ⟨v', hfr, hb', hval2, hr'⟩ := epad_val_run (epadBA C d mode) epadOr z y true C d
        Sum.inl (.inr .q1T) (.inr .no) (fun _ => rfl)
        (fun j hj => by
          rw [show epadS true * j = 2 * j from rfl, (epadIn_answer z _).1, hz, pairEncode_getD,
            if_pos (by omega), show 2 * j / 2 = j by omega])
        ((C + d + 8) * (z.length + 1) ^ (d + 1)) (by omega) v hv h0 h1 hzr
      by_cases hvy : epadValid C d y
      · rw [if_pos hvy] at hr'
        obtain ⟨a, ha⟩ := hvy
        have hfst : pairFstD y = a := by rw [ha, pairFstD_pairEncode]
        have hya : y.length = 2 * a.length + 2 + C * (a.length + 1) ^ d := by
          rw [ha, length_pairEncode, List.length_replicate]
        have hpost := epad_bank_post C d mode z ((C + d + 8) * (z.length + 1) ^ (d + 1))
          a.length (LogProg.bitsVal w) v' hb' (by rw [hval2 ⟨a, ha⟩, hfst])
          (by rw [hfr 13 (by decide), h13]) (by rw [hfr 15 (by decide), h15])
          (by rw [hfr 16 (by decide), h16]) (by rw [hfr 17 (by decide), h17]) (by omega)
        have hans : MultiTapeTM.indicator (epadQ C d mode : Set (List Bool)) z =
            (if LogProg.bitsVal w < a.length then
              (if mode then z.getD (4 * LogProg.bitsVal w) false else true) else false) := by
          rw [indicator_eq_decide]
          have hm := epad_mem_Q_iff (C := C) (d := d) (mode := mode) hd
          rw [hfst] at hm
          by_cases hi : LogProg.bitsVal w < a.length
          · rw [if_pos hi]
            cases mode with
            | false =>
              exact decide_eq_true (hm.mpr ⟨hw.1, hw.2, ⟨a, ha⟩, by simpa using hi⟩)
            | true =>
              have h4 : z.getD (4 * LogProg.bitsVal w) false = a.getD (LogProg.bitsVal w) false :=
                by rw [hz, ha, epad_getD_four a _ w _ hi]
              rw [if_pos rfl, h4]
              cases hb : a.getD (LogProg.bitsVal w) false
              · refine decide_eq_false (fun h => ?_)
                have h5 := (hm.mp h).2.2.2
                rw [if_pos rfl, hb] at h5
                exact Bool.false_ne_true h5
              · exact decide_eq_true (hm.mpr ⟨hw.1, hw.2, ⟨a, ha⟩, by rw [if_pos rfl]; exact hb⟩)
          · rw [if_neg hi]
            refine decide_eq_false (fun h => ?_)
            have h4 := (hm.mp h).2.2.2
            cases mode with
            | false => exact hi (by simpa using h4)
            | true =>
              simp only [if_true] at h4
              rw [List.getD_eq_default _ _ (by omega)] at h4
              exact Bool.false_ne_true h4
        rw [hans]
        exact hr.halt (hr'.halt hpost)
      · rw [if_neg hvy] at hr'
        have hans : MultiTapeTM.indicator (epadQ C d mode : Set (List Bool)) z = false := by
          rw [indicator_eq_decide]
          exact decide_eq_false (fun h => hvy ((epad_mem_Q_iff hd).mp h).2.2.1)
        rw [hans]
        exact hr.halt (hr'.halt (hno v' hb'))
    · obtain ⟨v, hv, hr⟩ := hbad hw
      have hans : MultiTapeTM.indicator (epadQ C d mode : Set (List Bool)) z = false := by
        rw [indicator_eq_decide]
        exact decide_eq_false (fun h => hw ⟨((epad_mem_Q_iff hd).mp h).1,
          ((epad_mem_Q_iff hd).mp h).2.1⟩)
      rw [hans]
      exact hr.halt (hno v hv)

/-! ### The run phase (E-PAD checkpoint 3) -/

/-- **The run phase** (checkpoint 3): the oracle-input simulator runs `L`'s decider on the
virtual input `epadVirt y`, answered by the bank, within `K · T |y|` work cells, on every input.

**Proof sketch.** `LogProg.OIS.compile_decides` with `L`'s decider `M` (space `c · S`) and the
bank `![M₀, M₁]` of `epadQ`'s deciders (space `c_j · logSpace`), whose laws on genuine queries
are `epad_query_mem_iff`. With `m = |y|` and `v = epadVirt y`: on a padded `y = ⟨a, 1^{…}⟩`,
`m = 2|a| + 2 + C (|a| + 1)^d`, so `S |v| ≤ T m` by `hST`; otherwise `v = []` and
`S 0 ≤ S 0 · T m`. The index register costs `|bits (|v| + 1)| + 2 ≤ 4 T m` and the bank
`k_D (2B + 1)` with `B = (c₀ + c₁)(3m + 4) + 1`, so `2B + 1 ≤ (8 (c₀ + c₁) + 3) T m`. -/
private theorem epad_run {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    ∃ (K : ℕ) (O : FinTM Bool), O.ComputesInSpace
      (fun y => [MultiTapeTM.indicator (L : Set (List Bool)) (epadVirt C d y)])
      (fun n => K * T n) := by
  classical
  obtain ⟨c, M, hM⟩ := mem_SPACE_iff.mp hL
  have hQ0 := epad_Q_mem C d false
  have hQ1 := epad_Q_mem C d true
  rw [LOGSPACE_eq, mem_SPACE_iff] at hQ0 hQ1
  obtain ⟨c0, M0, h0⟩ := hQ0
  obtain ⟨c1, M1, h1⟩ := hQ1
  let Ms : Fin 2 → FinTM Bool := ![M0, M1]
  let As : Fin 2 → Language Bool := ![epadQ C d false, epadQ C d true]
  let sb : Fin 2 → ℕ → ℕ := ![fun n => c0 * logSpace n, fun n => c1 * logSpace n]
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j) := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
    · show M0.DecidesInSpace (epadQ C d false) (fun n => c0 * logSpace n)
      exact h0
    · show M1.DecidesInSpace (epadQ C d true) (fun n => c1 * logSpace n)
      exact h1
  have hsb : ∀ j q, sb j q ≤ (c0 + c1) * (q + 1) := by
    intro j q
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
    · show c0 * logSpace q ≤ (c0 + c1) * (q + 1)
      exact Nat.mul_le_mul (Nat.le_add_right _ _) (logSpace_le_succ q)
    · show c1 * logSpace q ≤ (c0 + c1) * (q + 1)
      exact Nat.mul_le_mul (Nat.le_add_left _ _) (logSpace_le_succ q)
  refine ⟨M.k * (2 * c * (S 0 + 1) + 1) + 4 +
      (LogProg.bankK Ms + LogProg.bankK Ms) * (8 * (c0 + c1) + 3),
    LogProg.compileFinTM (LogProg.OIS.prog M) (LogProg.OIS.start M) (LogProg.bankTM Ms)
      (LogProg.bankStart Ms), ?_⟩
  rw [FinTM.computesInSpace_iff]
  intro y
  set v := epadVirt C d y with hv
  obtain ⟨t, ht, hs⟩ :=
    (FinTM.computesInSpace_iff _ _ _).mp ((FinTM.decidesInSpace_iff _ _ _).mp hM) v
  have hvm : v.length ≤ y.length := epadVirt_length_le C d y
  set B := (c0 + c1) * (3 * y.length + 4) + 1 with hB
  have hbits : ∀ i ≤ v.length, (Nat.bits i).length ≤ y.length + 1 := by
    intro i hi
    have h1 := LogProg.length_bits_le_log i
    have h2 := Nat.log_le_self 2 i
    omega
  have hBnd : ∀ j, ∀ i ≤ v.length,
      max (sb j (pairEncode y (Nat.bits i)).length) 1 ≤ B := by
    intro j i hi
    have hq := hsb j (pairEncode y (Nat.bits i)).length
    rw [length_pairEncode] at hq ⊢
    have hb := hbits i hi
    have hmono : (c0 + c1) * (2 * y.length + 2 + (Nat.bits i).length + 1) ≤
        (c0 + c1) * (3 * y.length + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    refine max_le ?_ (by omega)
    omega
  have hA0 : ∀ i ≤ v.length,
      pairEncode y (Nat.bits i) ∈ As 0 ↔ i < v.length := by
    intro i hi
    show pairEncode y (Nat.bits i) ∈ epadQ C d false ↔ i < v.length
    rw [epad_query_mem_iff C d false y i (hi.trans hvm)]
    simp only [Bool.false_eq_true, if_false]
    by_cases hval : epadValid C d y
    · rw [hv, epadVirt_of_valid hval]
      exact ⟨fun h => h.2, fun h => ⟨hval, h⟩⟩
    · rw [hv, epadVirt_of_not_valid hval]
      exact ⟨fun h => absurd h.1 hval, fun h => absurd h (Nat.not_lt_zero _)⟩
  have hA1 : ∀ i < v.length,
      pairEncode y (Nat.bits i) ∈ As 1 ↔ v.getD i false = true := by
    intro i hi
    show pairEncode y (Nat.bits i) ∈ epadQ C d true ↔ v.getD i false = true
    rw [epad_query_mem_iff C d true y i (hi.le.trans hvm)]
    simp only [if_true]
    by_cases hval : epadValid C d y
    · rw [hv, epadVirt_of_valid hval]
      exact ⟨fun h => h.2, fun h => ⟨hval, h⟩⟩
    · rw [hv, epadVirt_of_not_valid hval] at hi
      exact absurd hi (Nat.not_lt_zero _)
  obtain ⟨T', hT', hSp⟩ := LogProg.OIS.compile_decides M Ms As sb hMs y v
    [MultiTapeTM.indicator (L : Set (List Bool)) v] hA0 hA1 t ht B hBnd
  refine ⟨T', hT', hSp.trans ?_⟩
  -- the space ledger
  have hTm := hT y.length
  have hS : S v.length ≤ (S 0 + 1) * T y.length := by
    by_cases hval : epadValid C d y
    · obtain ⟨a, ha⟩ := hval
      have hva : v.length = a.length := by
        rw [hv, epadVirt_of_valid ⟨a, ha⟩, ha, pairFstD_pairEncode]
      have hma : y.length = 2 * a.length + 2 + C * (a.length + 1) ^ d := by
        rw [ha, length_pairEncode, List.length_replicate]
      rw [hva]
      have h1 := hST a.length
      rw [← hma] at h1
      calc S a.length ≤ T y.length := h1
        _ ≤ (S 0 + 1) * T y.length := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    · have hv0 : v.length = 0 := by rw [hv, epadVirt_of_not_valid hval]; rfl
      rw [hv0]
      calc S 0 ≤ S 0 * T y.length := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ (S 0 + 1) * T y.length := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hsp : M.tm.spaceUsed (M.tm.initCfg v) t ≤ c * ((S 0 + 1) * T y.length) :=
    hs.trans (Nat.mul_le_mul_left c hS)
  have hW : (Nat.bits (v.length + 1)).length + 2 ≤ 4 * T y.length := by
    have h1 := LogProg.length_bits_le_log (v.length + 1)
    have h2 := Nat.log_le_self 2 (v.length + 1)
    omega
  have h2B : 2 * B + 1 ≤ (8 * (c0 + c1) + 3) * T y.length := by
    have h1 : (c0 + c1) * (3 * y.length + 4) ≤ (c0 + c1) * (4 * T y.length) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (8 * (c0 + c1) + 3) * T y.length =
        2 * ((c0 + c1) * (4 * T y.length)) + 3 * T y.length := by ring
    rw [e, hB]
    omega
  have hk1 : M.k * (2 * M.tm.spaceUsed (M.tm.initCfg v) t + 1) ≤
      M.k * ((2 * c * (S 0 + 1) + 1) * T y.length) := by
    apply Nat.mul_le_mul_left
    have e : (2 * c * (S 0 + 1) + 1) * T y.length =
        2 * (c * ((S 0 + 1) * T y.length)) + T y.length := by ring
    rw [e]
    omega
  set kD := LogProg.bankK Ms + LogProg.bankK Ms with hkD
  have hk2 : kD * (2 * B + 1) ≤ kD * ((8 * (c0 + c1) + 3) * T y.length) :=
    Nat.mul_le_mul_left _ h2B
  have e : (M.k * (2 * c * (S 0 + 1) + 1) + 4 + kD * (8 * (c0 + c1) + 3)) * T y.length =
      M.k * ((2 * c * (S 0 + 1) + 1) * T y.length) + 4 * T y.length +
        kD * ((8 * (c0 + c1) + 3) * T y.length) := by ring
  rw [e]
  omega

/-- **Padding transfers space bounds down** ([AB09, Exercise 3.2], the padding argument in space
form): if `L ∈ SPACE S`, then the language of `L`'s members padded by `C · (|x| + 1)^d` ones lies
in `SPACE T` for every `T` with `m + 1 ≤ T m` (room to validate the padding and to copy the first
component) and `S n ≤ T (2n + 2 + C (n + 1)^d)` (room for `L`'s decider, at the padded length
`|pairEncode x 1^{C (|x|+1)^d}| = 2|x| + 2 + C (|x| + 1)^d`).

**Proof sketch.** Let `M` decide `L` within `c · S` cells. On input `y`, first check that `y` is a
pair `pairEncode x w` whose second component `w` consists of exactly `C (|x| + 1)^d` ones;
reject otherwise. That needs `O(|y|)` cells. Then run `M` on `x` (copied to a work tape, or read
in place through a bounded input device) and answer as `M` does, within `c · S |x|` cells. For a
validated `y`, `|y| = 2|x| + 2 + C (|x| + 1)^d`, so both phases fit in `O(T |y|)`. -/
theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T := by
  sorry

end Complexity
