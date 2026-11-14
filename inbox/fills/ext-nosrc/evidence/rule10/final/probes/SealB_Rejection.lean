/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.InformationTheory.Samples
import TCSlib.InformationTheory.Entropy

set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealB_Rejection"
  let phase : String := "install"
  let payload : String := "TCSlib.InformationTheory.FinDist.HasMinEntropy\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.IsFlatSource\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.IsSource\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist._sizeOf_1\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist._sizeOf_inst\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.collision\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.expect\tTCSlib.InformationTheory.Samples\nTCSlib.InformationTheory.FinDist.flat\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.iid\tTCSlib.InformationTheory.Samples\nTCSlib.InformationTheory.FinDist.instCoeFunForallReal\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.map\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.maxProb\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.minEntropy\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.probTrue\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.prod\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.shannonEntropy\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.uniform\tTCSlib.InformationTheory.FinDist"
  let expected : Nat := 18
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let group := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (group.push n)
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  let mut verified : Nat := 0
  for line in lines do
    let [spelling, expectedHome] := line.splitOn "\t" |
      throwError "FILL-HARNESS {label}: malformed request"
    let names := (catalog[spelling]?).getD #[]
    unless names.size == 1 do throwError "FILL-HARNESS {label}: absent/ambiguous name {spelling}"
    let n := names[0]!
    let some mi := env.getModuleIdxFor? n | throwError "FILL-HARNESS {label}: missing home {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "FILL-HARNESS {label}: home mismatch {spelling}"
    let some ci := env.find? n | throwError "FILL-HARNESS {label}: missing constant {spelling}"
    unless ci.isDefinition do throwError "FILL-HARNESS {label}: nondefinition {spelling}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless before == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "FILL-HARNESS {label}: seal inactive at {phase} for {spelling}"
    let row := Lean.Json.mkObj [
      ("label", Lean.toJson label), ("phase", Lean.toJson phase),
      ("name", Lean.toJson n.toString), ("home", Lean.toJson home.toString)]
    Lean.logInfo m!"FILL_SEAL_NAME {row.compress}"
    verified := verified + 1
  unless verified == expected do throwError "FILL-HARNESS {label}: count mismatch {verified} vs {expected}"
  Lean.logInfo m!"FILL_SEAL_DONE {label} {phase} {expected} {verified}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite rejection sampling

The first accepted point among `t` independent trials is returned; a final independent point
is returned when all trials fail. The resulting law and its acceptance probability are computed
from the published finite-distribution readers.

## Main definitions

* `Rejection.select`: the first accepted point among the first `t` entries, otherwise entry `t`.
* `Rejection.law`: the recursive distribution of this rejection sampler.

## Main results

* `Rejection.select_uniform_law`: the recursive law is the law of the finite tuple selector.
* `Rejection.law_eq_mixture`: the law is a mixture of uniform and the accepted flat law.
* `Rejection.law_probTrue`: its acceptance probability is `1-(1-q)^(t+1)`.
* `Rejection.law_isSource`: the source bound is preserved by this mixture.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.2, Theorem 183.6.
-/

namespace TCSlib.Cryptography.Randomness.Rejection

open TCSlib.InformationTheory Finset

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Pushing the uniform distribution through a bijection preserves uniformity:
`map e U_α = U_β`. -/
theorem map_uniform_equiv [DecidableEq β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (FinDist.uniform α).map e = FinDist.uniform β := by
  classical
  apply FinDist.ext
  intro b
  rw [FinDist.map_apply]
  have hf : (univ : Finset α).filter (fun a => e a = b) = {e.symm b} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply b).symm)
    · rintro rfl
      exact e.apply_symm_apply b
  rw [hf, sum_singleton, FinDist.uniform_apply, FinDist.uniform_apply,
    Fintype.card_congr e]

/-- Summing a function over a pushforward is summing its composite over the original law:
`∑ b, map f p b · g b = ∑ a, p a · g (f a)`. The proof exchanges the two finite sums and
uses the unique image `f a` of each input. -/
theorem sum_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (∑ b, (p.map f) b * g b) = ∑ a, p a * g (f a) := by
  classical
  simp only [FinDist.map_apply, sum_mul, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp only [if_neg (Ne.symm hba), zero_mul]
  · intro h
    exact False.elim (h (mem_univ _))

/-- Expectation under a pushforward composes the test:
`E_{map f p}[g] = E_p[g ∘ f]`. -/
theorem expect_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a)) := by
  rw [FinDist.expect_eq, FinDist.expect_eq]
  exact sum_map p f g

/-- Acceptance under a pushforward composes the Boolean test:
`Pr_{map f p}[D] = Pr_p[D ∘ f]`. -/
theorem probTrue_map [DecidableEq β] (p : FinDist α) (f : α → β) (D : β → Bool) :
    (p.map f).probTrue D = p.probTrue (fun a => D (f a)) := by
  rw [FinDist.probTrue_eq_expect, expect_map, FinDist.probTrue_eq_expect]

/-- A Boolean acceptance probability is nonnegative. -/
theorem probTrue_nonneg (p : FinDist α) (D : α → Bool) : 0 ≤ p.probTrue D := by
  rw [FinDist.probTrue_eq]
  exact sum_nonneg fun a _ => p.nonneg a

/-- A Boolean acceptance probability is at most one. -/
theorem probTrue_le_one (p : FinDist α) (D : α → Bool) : p.probTrue D ≤ 1 := by
  rw [FinDist.probTrue_eq, ← p.sum_prob]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => p.nonneg a)

/-- A pushforward's mass at `b` is the expectation of its preimage indicator:
`map f p b = E_p[1_{f(a)=b}]`. -/
theorem map_apply_expect [DecidableEq β] (p : FinDist α) (f : α → β) (b : β) :
    (p.map f) b = p.expect (fun a => if f a = b then 1 else 0) := by
  classical
  rw [FinDist.map_apply, FinDist.expect_eq, sum_filter]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- Successive pushforwards compose: `map g (map f p) = map (g ∘ f) p`. -/
theorem map_map [DecidableEq β] [DecidableEq γ] (p : FinDist α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (fun a => g (f a)) := by
  classical
  apply FinDist.ext
  intro c
  rw [map_apply_expect, expect_map, map_apply_expect]

/-- Mapping only the second coordinate of an independent pair can be done before or after
pairing: `map g (p × map f q) = map (fun (x,y) => g (x,f y)) (p × q)`. -/
theorem map_prod_snd [DecidableEq β] [DecidableEq γ] {δ : Type*} [Fintype δ]
    [DecidableEq δ] (p : FinDist α) (q : FinDist β) (f : β → γ) (g : α × γ → δ) :
    (p.prod (q.map f)).map g = (p.prod q).map (fun z => g (z.1, f z.2)) := by
  classical
  apply FinDist.ext
  intro d
  rw [map_apply_expect, map_apply_expect, FinDist.expect_prod, FinDist.expect_prod]
  congr 1
  funext a
  exact expect_map q f (fun c => if g (a, c) = d then 1 else 0)

/-- The product of two uniform laws is the uniform law on pairs: `U_α × U_β = U_(α×β)`. -/
theorem uniform_prod [Nonempty α] [Nonempty β] :
    (FinDist.uniform α).prod (FinDist.uniform β) = FinDist.uniform (α × β) := by
  apply FinDist.ext
  intro z
  rw [FinDist.prod_apply, FinDist.uniform_apply, FinDist.uniform_apply,
    FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

/-- A nonempty tuple is equivalent to its first entry and its tail. -/
def tupleEquiv (t : ℕ) : (Fin (t + 1 + 1) → α) ≃ α × (Fin (t + 1) → α) where
  toFun x := (x 0, fun i => x i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv z := by
    apply Prod.ext
    · simp
    · funext i
      simp

/-- The tuple equivalence reads the first entry and the tail:
`tupleEquiv t x = (x 0, fun i => x i.succ)`. -/
theorem tupleEquiv_apply (t : ℕ) (x : Fin (t + 1 + 1) → α) :
    tupleEquiv t x = (x 0, fun i => x i.succ) := rfl

/-- The inverse tuple equivalence prepends its first coordinate:
`(tupleEquiv t).symm (a,x) = Fin.cons a x`. -/
theorem tupleEquiv_symm_apply (t : ℕ) (z : α × (Fin (t + 1) → α)) :
    (tupleEquiv t).symm z = Fin.cons z.1 z.2 := rfl

/-- The first entry of the inverse tuple equivalence is the pair's first coordinate. -/
theorem tupleEquiv_symm_zero (t : ℕ) (z : α × (Fin (t + 1) → α)) :
    (tupleEquiv t).symm z 0 = z.1 := by
  rw [tupleEquiv_symm_apply]
  simp

/-- Each successor entry of the inverse tuple equivalence is the corresponding tail entry. -/
theorem tupleEquiv_symm_succ (t : ℕ) (z : α × (Fin (t + 1) → α)) (i : Fin (t + 1)) :
    (tupleEquiv t).symm z i.succ = z.2 i := by
  rw [tupleEquiv_symm_apply]
  simp

/-- Select the first accepted entry among `t` trials; if all fail, return the final entry.
There are `t+1` entries in total, so the fallback is always present. -/
def select (D : α → Bool) : (t : ℕ) → (Fin (t + 1) → α) → α
  | 0, x => x 0
  | t + 1, x => if D (x 0) then x 0 else select D t (fun i => x i.succ)

/-- With no rejection trials, the selector returns its sole entry: `select D 0 x = x 0`. -/
theorem select_zero (D : α → Bool) (x : Fin 1 → α) : select D 0 x = x 0 := rfl

/-- With one more rejection trial, accept the first entry if its test succeeds, otherwise
select from the tail: `select D (t+1) x = if D (x 0) then x 0 else select D t (x ∘ succ)`. -/
theorem select_succ (D : α → Bool) (t : ℕ) (x : Fin (t + 1 + 1) → α) :
    select D (t + 1) x = if D (x 0) then x 0 else select D t (fun i => x i.succ) := rfl

/-- The law of rejection sampling with `t` trials and an independent uniform fallback.
At each trial, a fresh uniform point is accepted if its test succeeds. -/
noncomputable def law [DecidableEq α] [Nonempty α] (D : α → Bool) : ℕ → FinDist α
  | 0 => FinDist.uniform α
  | t + 1 => ((FinDist.uniform α).prod (law D t)).map
      (fun z => if D z.1 then z.1 else z.2)

/-- With zero trials, the rejection law is uniform: `law D 0 = U_α`. -/
theorem law_zero [DecidableEq α] [Nonempty α] (D : α → Bool) :
    law D 0 = FinDist.uniform α := rfl

/-- One more trial draws a fresh uniform point independently of the remaining sampler:
`law D (t+1) = map (fun (x,y) => if D x then x else y) (U_α × law D t)`. -/
theorem law_succ [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    law D (t + 1) = ((FinDist.uniform α).prod (law D t)).map
      (fun z => if D z.1 then z.1 else z.2) := rfl

/-- Selecting from `t+1` independent uniform entries has the recursive rejection law:
`map (select D t) U_(α^(t+1)) = law D t`.

**Proof sketch.** Split a tuple into its first entry and its tail. Uniformity is preserved by
this bijection, and uniformity on pairs is the product of the two uniform laws. The induction
hypothesis identifies the selected tail with the remaining rejection sampler. -/
theorem select_uniform_law [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    (FinDist.uniform (Fin (t + 1) → α)).map (select D t) = law D t := by
  classical
  induction t with
  | zero =>
    rw [law_zero]
    let e : (Fin 1 → α) ≃ α :=
      { toFun := fun x => x 0
        invFun := fun a _ => a
        left_inv := by
          intro x
          funext i
          have hi : i = 0 := Subsingleton.elim _ _
          rw [hi]
        right_inv := fun _ => rfl }
    exact map_uniform_equiv e
  | succ t ih =>
    rw [law_succ, ← ih]
    have hu : FinDist.uniform (Fin (t + 1 + 1) → α) =
        (FinDist.uniform (α × (Fin (t + 1) → α))).map (tupleEquiv t).symm :=
      (map_uniform_equiv (tupleEquiv (α := α) t).symm).symm
    rw [hu, map_map, ← uniform_prod, map_prod_snd]
    congr 1

/-- Independent branching returns the first point on acceptance and the second on rejection:
its mass at `a` is `1_{D(a)} p(a) + Pr_p[¬D] q(a)`.

**Proof sketch.** Expand the map and product readers. For a fixed first point, the inner sum
is either its whole mass or the mass of the second point at `a`. Split the outer sum into
accepted and rejected first points. -/
theorem branch_apply [DecidableEq α] (p q : FinDist α) (D : α → Bool) (a : α) :
    ((p.prod q).map (fun z => if D z.1 then z.1 else z.2)) a =
      (if D a then p a else 0) + (1 - p.probTrue D) * q a := by
  classical
  rw [FinDist.map_apply, sum_filter, Fintype.sum_prod_type]
  simp only [FinDist.prod_apply]
  have inner (x : α) :
      (∑ y, if (if D x then x else y) = a then p x * q y else 0) =
        if D x then (if x = a then p x else 0) else p x * q a := by
    cases hd : D x
    · simp [hd]
    · by_cases hxa : x = a
      · simp [hd, hxa, ← mul_sum, q.sum_prob]
      · simp [hd, hxa]
  simp_rw [inner]
  have split (x : α) :
      (if D x then (if x = a then p x else 0) else p x * q a) =
        (if x = a then (if D a then p a else 0) else 0) +
          (if !D x then p x * q a else 0) := by
    by_cases hxa : x = a
    · subst x
      cases D a <;> simp
    · cases hd : D x <;> simp [hd, hxa]
  simp_rw [split]
  rw [sum_add_distrib]
  have hn : (∑ x, if !D x then p x * q a else 0) =
      (1 - p.probTrue D) * q a := by
    rw [← FinDist.probTrue_not, FinDist.probTrue_eq, sum_mul, sum_filter]
  rw [hn]
  simp

/-- One rejection trial satisfies the point recurrence
`law D (t+1) a = 1_{D(a)} / |α| + (1-q) law D t a`, where `q = Pr_{U_α}[D]`. -/
theorem law_succ_apply [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) (a : α) :
    law D (t + 1) a =
      (if D a then (Fintype.card α : ℝ)⁻¹ else 0) +
        (1 - (FinDist.uniform α).probTrue D) * law D t a := by
  rw [law_succ, branch_apply, FinDist.uniform_apply]

/-- The acceptance probabilities obey
`Pr_{law D (t+1)}[D] = q + (1-q) Pr_{law D t}[D]`. -/
theorem law_succ_probTrue [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    (law D (t + 1)).probTrue D =
      (FinDist.uniform α).probTrue D +
        (1 - (FinDist.uniform α).probTrue D) * (law D t).probTrue D := by
  classical
  rw [FinDist.probTrue_eq]
  simp_rw [law_succ_apply]
  rw [sum_add_distrib, ← mul_sum]
  have hi : (∑ a ∈ (univ : Finset α).filter (fun a => D a = true),
      if D a then (Fintype.card α : ℝ)⁻¹ else 0) = (FinDist.uniform α).probTrue D := by
    rw [FinDist.probTrue_eq]
    apply sum_congr rfl
    intro a ha
    simp [(mem_filter.1 ha).2, FinDist.uniform_apply]
  rw [hi, ← FinDist.probTrue_eq (law D t) D]

/-- The rejection sampler accepts with probability `1-(1-q)^(t+1)`, including the independent
fallback's chance to accept. This formula also holds for `q=0` and `q=1`.

**Proof sketch.** The zero-trial law has acceptance `q`. Each additional trial fails with
probability `1-q`, multiplying the probability that the remaining sampler fails by that factor. -/
theorem law_probTrue [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    (law D t).probTrue D = 1 - (1 - (FinDist.uniform α).probTrue D) ^ (t + 1) := by
  induction t with
  | zero => rw [law_zero]; ring
  | succ t ih => rw [law_succ_probTrue, ih, pow_succ]; ring

/-- For positive uniform acceptance `q`, the rejection law's point mass is
`(1-q)^t / |α| + 1_{D(a)} (1-(1-q)^t) / (|α| q)`.

**Proof sketch.** Induct on the trial count using the point recurrence. On accepted points the
geometric sum contributes `(1-(1-q)^t)/q`; on rejected points only the fallback contributes. -/
theorem law_apply [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (a : α) :
    law D t a =
      (1 - (FinDist.uniform α).probTrue D) ^ t * (Fintype.card α : ℝ)⁻¹ +
        (if D a then
          (1 - (1 - (FinDist.uniform α).probTrue D) ^ t) *
            (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D else 0) := by
  have hq0 : (FinDist.uniform α).probTrue D ≠ 0 := ne_of_gt hq
  induction t with
  | zero => rw [law_zero, FinDist.uniform_apply]; simp
  | succ t ih =>
    rw [law_succ_apply, ih, pow_succ]
    cases D a <;> simp
    · ring
    · field_simp [hq0]
      <;> ring

/-- Uniform acceptance is the cardinality of the accepted set divided by the whole cardinality:
`Pr_{U_α}[D] = |{a : D a}| / |α|`. -/
theorem uniform_probTrue [Nonempty α] (D : α → Bool) :
    (FinDist.uniform α).probTrue D =
      (((univ : Finset α).filter (fun a => D a = true)).card : ℝ) *
        (Fintype.card α : ℝ)⁻¹ := by
  classical
  rw [FinDist.probTrue_eq]
  simp only [FinDist.uniform_apply, sum_const, nsmul_eq_mul]

/-- Positive uniform acceptance implies that the accepted set is nonempty. -/
theorem accepted_nonempty [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) :
    ((univ : Finset α).filter (fun a => D a = true)).Nonempty := by
  classical
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.1 h
  have hz : (FinDist.uniform α).probTrue D = 0 := by
    rw [FinDist.probTrue_eq, he, sum_empty]
  linarith

/-- The flat law on the accepted set has point mass `1/(|α| q)` at accepted points and zero
elsewhere, where `q=Pr_{U_α}[D]`. -/
theorem accepted_flat_apply [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hs : ((univ : Finset α).filter (fun a => D a = true)).Nonempty) (a : α) :
    FinDist.flat ((univ : Finset α).filter (fun a => D a = true)) hs a =
      if D a then (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D else 0 := by
  classical
  rw [FinDist.flat_apply]
  have hm : a ∈ (univ : Finset α).filter (fun a => D a = true) ↔ D a = true := by simp
  simp only [hm]
  by_cases hd : D a = true
  · rw [if_pos hd, if_pos hd, uniform_probTrue]
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hs0 : ((((univ : Finset α).filter (fun a => D a = true)).card : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 hs.card_pos.ne'
    field_simp [hc, hs0]
  · rw [if_neg hd, if_neg hd]

/-- The rejection law is the pointwise mixture
`(1-q)^t U_α + (1-(1-q)^t) flat({a : D a})` for `q>0`. -/
theorem law_apply_flat [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (a : α) :
    law D t a =
      (1 - (FinDist.uniform α).probTrue D) ^ t * (FinDist.uniform α) a +
        (1 - (1 - (FinDist.uniform α).probTrue D) ^ t) *
          FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
            (accepted_nonempty D hq) a := by
  rw [law_apply D hq, FinDist.uniform_apply, accepted_flat_apply]
  cases D a <;> simp <;> ring

/-- A mixture of `p` and `q` with weight `w∈[0,1]` gives mass
`w p(a) + (1-w) q(a)` to each point. -/
noncomputable def mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) : FinDist α where
  prob a := w * p a + (1 - w) * q a
  nonneg a := add_nonneg (mul_nonneg hw0 (p.nonneg a))
    (mul_nonneg (sub_nonneg.2 hw1) (q.nonneg a))
  sum_prob := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, p.sum_prob, q.sum_prob]
    ring

/-- The point probability of the mixture is its defining convex combination:
`mixture w p q a = w p(a) + (1-w) q(a)`. -/
theorem mixture_apply (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) (a : α) :
    mixture w hw0 hw1 p q a = w * p a + (1 - w) * q a := rfl

/-- Mixtures of two `k`-sources are `k`-sources: their point probabilities share the same
upper bound `2^(-k)`, which is preserved by a convex combination. -/
theorem mixture_isSource (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) (k : ℝ) (hp : FinDist.IsSource k p) (hq : FinDist.IsSource k q) :
    FinDist.IsSource k (mixture w hw0 hw1 p q) := by
  have hp' := (FinDist.hasMinEntropy_iff p k).1
    (FinDist.isSource_iff_hasMinEntropy.1 hp)
  have hq' := (FinDist.hasMinEntropy_iff q k).1
    (FinDist.isSource_iff_hasMinEntropy.1 hq)
  apply FinDist.isSource_iff_hasMinEntropy.2
  apply (FinDist.hasMinEntropy_iff _ _).2
  intro a
  rw [mixture_apply]
  calc w * p a + (1 - w) * q a
      ≤ w * (2 : ℝ) ^ (-k) + (1 - w) * (2 : ℝ) ^ (-k) :=
        add_le_add (mul_le_mul_of_nonneg_left (hp' a) hw0)
          (mul_le_mul_of_nonneg_left (hq' a) (sub_nonneg.2 hw1))
    _ = (2 : ℝ) ^ (-k) := by ring

/-- The probability `(1-q)^t` that all rejection trials fail is nonnegative. -/
theorem failure_pow_nonneg [Nonempty α] (D : α → Bool) (t : ℕ) :
    0 ≤ (1 - (FinDist.uniform α).probTrue D) ^ t :=
  pow_nonneg (sub_nonneg.2 (probTrue_le_one _ _)) _

/-- The probability `(1-q)^t` that all rejection trials fail is at most one. -/
theorem failure_pow_le_one [Nonempty α] (D : α → Bool) (t : ℕ) :
    (1 - (FinDist.uniform α).probTrue D) ^ t ≤ 1 := by
  have hb0 : 0 ≤ 1 - (FinDist.uniform α).probTrue D :=
    sub_nonneg.2 (probTrue_le_one _ _)
  have hb1 : 1 - (FinDist.uniform α).probTrue D ≤ 1 := by
    linarith [probTrue_nonneg (FinDist.uniform α) D]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ]
    calc (1 - (FinDist.uniform α).probTrue D) ^ t *
        (1 - (FinDist.uniform α).probTrue D) ≤ 1 * 1 := mul_le_mul ih hb1 hb0 zero_le_one
      _ = 1 := one_mul _

/-- The rejection law is exactly the convex mixture
`(1-q)^t U_α + (1-(1-q)^t) flat({a : D a})`. -/
theorem law_eq_mixture [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) :
    law D t = mixture ((1 - (FinDist.uniform α).probTrue D) ^ t)
      (failure_pow_nonneg D t) (failure_pow_le_one D t) (FinDist.uniform α)
      (FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
        (accepted_nonempty D hq)) := by
  apply FinDist.ext
  intro a
  rw [mixture_apply]
  exact law_apply_flat D hq t a

/-- If `1/(|α|q) ≤ 2^(-k)`, the flat law on the accepted set is a `k`-source. -/
theorem accepted_flat_isSource [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hs : ((univ : Finset α).filter (fun a => D a = true)).Nonempty) (k : ℝ)
    (hbound : (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D ≤ (2 : ℝ) ^ (-k)) :
    FinDist.IsSource k (FinDist.flat ((univ : Finset α).filter (fun a => D a = true)) hs) := by
  apply FinDist.isSource_iff_hasMinEntropy.2
  apply (FinDist.hasMinEntropy_iff _ _).2
  intro a
  rw [accepted_flat_apply]
  split_ifs
  · exact hbound
  · positivity

/-- The rejection law is a `k`-source whenever its uniform and accepted-flat components are
`k`-sources. This follows from its exact mixture identity and convexity of the point bound. -/
theorem law_isSource [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (k : ℝ)
    (hU : FinDist.IsSource k (FinDist.uniform α))
    (hflat : FinDist.IsSource k
      (FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
        (accepted_nonempty D hq))) :
    FinDist.IsSource k (law D t) := by
  rw [law_eq_mixture D hq t]
  exact mixture_isSource _ _ _ _ _ _ hU hflat

end TCSlib.Cryptography.Randomness.Rejection

set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealB_Rejection"
  let phase : String := "eof"
  let payload : String := "TCSlib.InformationTheory.FinDist.HasMinEntropy\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.IsFlatSource\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.IsSource\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist._sizeOf_1\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist._sizeOf_inst\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.collision\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.expect\tTCSlib.InformationTheory.Samples\nTCSlib.InformationTheory.FinDist.flat\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.iid\tTCSlib.InformationTheory.Samples\nTCSlib.InformationTheory.FinDist.instCoeFunForallReal\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.map\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.maxProb\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.minEntropy\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.probTrue\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.prod\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.shannonEntropy\tTCSlib.InformationTheory.Entropy\nTCSlib.InformationTheory.FinDist.uniform\tTCSlib.InformationTheory.FinDist"
  let expected : Nat := 18
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let group := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (group.push n)
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  let mut verified : Nat := 0
  for line in lines do
    let [spelling, expectedHome] := line.splitOn "\t" |
      throwError "FILL-HARNESS {label}: malformed request"
    let names := (catalog[spelling]?).getD #[]
    unless names.size == 1 do throwError "FILL-HARNESS {label}: absent/ambiguous name {spelling}"
    let n := names[0]!
    let some mi := env.getModuleIdxFor? n | throwError "FILL-HARNESS {label}: missing home {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "FILL-HARNESS {label}: home mismatch {spelling}"
    let some ci := env.find? n | throwError "FILL-HARNESS {label}: missing constant {spelling}"
    unless ci.isDefinition do throwError "FILL-HARNESS {label}: nondefinition {spelling}"
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "FILL-HARNESS {label}: seal inactive at {phase} for {spelling}"
    let row := Lean.Json.mkObj [
      ("label", Lean.toJson label), ("phase", Lean.toJson phase),
      ("name", Lean.toJson n.toString), ("home", Lean.toJson home.toString)]
    Lean.logInfo m!"FILL_SEAL_NAME {row.compress}"
    verified := verified + 1
  unless verified == expected do throwError "FILL-HARNESS {label}: count mismatch {verified} vs {expected}"
  Lean.logInfo m!"FILL_SEAL_DONE {label} {phase} {expected} {verified}"
