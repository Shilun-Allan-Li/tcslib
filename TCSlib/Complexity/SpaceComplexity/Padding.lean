/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.ClassNP.PolyTimePairing

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

/-- **A genuine query** `⟨y, bits i⟩` with `i ≤ |y|` is in the bank's language exactly when `y`
is padded and the mode's question holds at `i`. -/
private lemma epad_query_mem_iff (C d : ℕ) (mode : Bool) (y : List Bool) (i : ℕ)
    (hi : i ≤ y.length) :
    pairEncode y (Nat.bits i) ∈ epadQ C d mode ↔ epadValid C d y ∧
      (if mode = true then (pairFstD y).getD i false = true else i < (pairFstD y).length) := by
  constructor
  · rintro ⟨y', w, hd, -, -, hv, hq⟩
    rw [pairDecode_pairEncode, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    rw [LogProg.bitsVal_bits] at hq
    exact ⟨hv, hq⟩
  · rintro ⟨hv, hq⟩
    refine ⟨y, Nat.bits i, pairDecode_pairEncode y (Nat.bits i),
      (LogProg.drop_canon (Nat.bits i)).mpr (LogProg.canon_bits i),
      LogProg.length_bits_mono hi, hv, ?_⟩
    rw [LogProg.bitsVal_bits]
    exact hq

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

/-- The input deciders' answers on a genuine query `⟨y, bits p⟩`: decider `0` reads letter `p`,
decider `1` compares `p` with `|y|`. -/
private lemma epadIn_answer (y : List Bool) (p : ℕ) :
    MultiTapeTM.indicator (epadIn 0 : Set (List Bool)) (pairEncode y (Nat.bits p)) =
        y.getD p false ∧
      MultiTapeTM.indicator (epadIn 1 : Set (List Bool)) (pairEncode y (Nat.bits p)) =
        decide (p < y.length) := by
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
  have hlen := inputLength_loop (epadVA C d)
    (fun j V => MultiTapeTM.indicator (epadIn j : Set (List Bool)) V) y 1 1 (.inr .lscan)
    (.inr .linc) (.inl .scan) rfl rfl (fun n _ => (epadIn_answer y n).2)
    ((C + d + 8) * (y.length + 1) ^ (d + 1)) (by omega) (fun _ => 0)
    (fun _ => Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨v', -, hb, -, hr⟩ := epad_val_run (epadVA C d)
    (fun j V => MultiTapeTM.indicator (epadIn j : Set (List Bool)) V) y y false C d Sum.inl
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
