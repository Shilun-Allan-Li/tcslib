/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Randomness.Learning.Distinguisher
import TCSlib.Cryptography.Randomness.Extraction.Rejection
import TCSlib.LearningTheory.PAC
/- DLC-SEAL Randomness_Learning_Law: whole-file closure seal of `TCSlib/Cryptography/Randomness/Learning/Law.lean`, variant A (PolyExpr.eval open), strict. -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let coeOpen : Bool := false
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
          continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Randomness_Learning_Law: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The prediction game as the distinguisher's acceptance probability

Step 1 of [PS10, Theorem 179.1, proof], the law: both the prediction game of the PAC layer and
the acceptance probability of the distinguisher of `exists_learnDist` against a keyed family are
uniform probabilities of one event over the keys, `m` examples, the learner's coins and a fresh
point (`gameProb`).

* **The prediction game** (`predictSuccess_eq_uprob`): its law is a product of uniform laws, the
  uniform law on the product (`iid_uniform`, `Rejection.uniform_prod`), so its success
  probability is the uniform probability of the event (`Rejection.uniform_probTrue`).
* **The distinguisher** (`exists_learnDist_acceptProb`): its coins are, through the bijection of
  `exists_learnDist`, the `m(n) + 1` points and the learner's coins; the points are the examples
  followed by the fresh point (`Fin.snoc`, `snocEquiv`), so for every family `G`,
  `acceptProb G (oracleDist B) = gameProb m G (learnerFn A n m)`.

## Main definitions

* `LearnPRF.gameProb`: the game probability with a family `G` and a learner `ℓ`.
* `LearnPRF.learnerFn`: the learner of a machine, as a function (the learner of the learning
  game, restated here since helper modules do not import the owned file).
* `LearnPRF.snocEquiv`: examples and a fresh point as one tuple.

## Main results

* `LearnPRF.iid_uniform`: independent uniform samples are a uniform tuple.
* `LearnPRF.predictSuccess_eq_uprob`: the prediction game as a uniform probability.
* `LearnPRF.exists_learnDist_acceptProb`: the distinguisher's acceptance probability is the game
  probability of the machine's learner.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity Turing TCSlib.Cryptography TCSlib.InformationTheory TCSlib.LearningTheory.PAC
  Finset

/-! ### Uniform laws -/

/-- **Independent uniform samples are a uniform tuple:** `(U_X)^m = U_{X^m}`.

**Proof sketch.** Both give every tuple `|X|^{-m}` (`FinDist.iid_apply`, `FinDist.uniform_apply`,
`Fintype.card_fun`, `Finset.prod_const`). -/
theorem iid_uniform {X : Type*} [Fintype X] [Nonempty X] (m : ℕ) :
    (FinDist.uniform X).iid m = FinDist.uniform (Fin m → X) := by
  classical
  apply FinDist.ext
  intro s
  rw [FinDist.iid_apply]
  simp only [FinDist.uniform_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow, inv_pow]

/-- **The prediction game as a uniform probability:** `predictSuccess C m L` is the uniform
probability over `((i, (s, r)), x)` of `L (label (C i) s) r x == C i x`.

**Proof sketch.** The law of the game is `(U_I × (U_X^m × U_ρ)) × U_X`, the uniform law on the
product (`iid_uniform`, `Rejection.uniform_prod`); acceptance under a uniform law counts the
accepted points (`Rejection.uniform_probTrue`, `uprob_eq_card_filter`). -/
theorem predictSuccess_eq_uprob {X I ρ : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I]
    [Fintype ρ] [Nonempty ρ] (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L =
      uprob fun w : (I × ((Fin m → X) × ρ)) × X =>
        (L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) = true := by
  classical
  rw [predictSuccess_eq, trialDist_eq, iid_uniform, Rejection.uniform_prod,
    Rejection.uniform_prod, Rejection.uniform_prod, Rejection.uniform_probTrue,
    uprob_eq_card_filter, div_eq_mul_inv]

/-! ### The game probability -/

section Game

variable {n : ℕ}

/-- **The game probability** with a family `G : K → {0,1}^n → {0,1}^n` and a learner `ℓ`: the
uniform probability over `((k, (s, r)), x)` that `ℓ`, on the examples `s` labelled by the first
bits of `G k` and the coins `r`, predicts at `x` the first bit of `G k x`. -/
noncomputable def gameProb {K ρ : Type*} [Fintype K] [Fintype ρ] (m : ℕ)
    (G : K → (Fin n → Bool) → (Fin n → Bool))
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) : ℝ :=
  uprob fun w : (K × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) =>
    (ℓ (label (fun x => firstBit (G w.1.1 x)) w.1.2.1) w.1.2.2 w.2 == firstBit (G w.1.1 w.2)) =
      true

/-- `gameProb m G ℓ = uprob (fun ((k, (s, r)), x) =>
(ℓ (label (firstBit ∘ G k) s) r x == firstBit (G k x)) = true)`. -/
theorem gameProb_eq {K ρ : Type*} [Fintype K] [Fintype ρ] (m : ℕ)
    (G : K → (Fin n → Bool) → (Fin n → Bool))
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
    gameProb m G ℓ =
      uprob fun w : (K × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) =>
        (ℓ (label (fun x => firstBit (G w.1.1 x)) w.1.2.1) w.1.2.2 w.2 ==
          firstBit (G w.1.1 w.2)) = true := rfl

/-- **The learner of a machine** `A` at parameter `n` with `m` examples, as a function: on the
labelled sample `S`, the coins `r` and the point `x`, whether `A(1^n, ⟨S', ⟦x⟧⟩; r) = [true]`,
where `S'` is the nested pairs of the examples `⟨⟦x_j⟧, [b_j]⟩`. -/
def learnerFn (A : NUPPT) (n m : ℕ) :
    (Fin m → (Fin n → Bool) × Bool) → A.Coins n → (Fin n → Bool) → Bool :=
  fun S r x => decide (A.runAt n (pairEncode ((List.ofFn fun j =>
    pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []) (List.ofFn x)) r = [true])

/-- `learnerFn A n m S r x =
decide (A.runAt n ⟨(ofFn j ↦ ⟨⟦(S j).1⟧, [(S j).2]⟩).foldr pairEncode [], ⟦x⟧⟩ r = [true])`. -/
theorem learnerFn_eq (A : NUPPT) (n m : ℕ) (S : Fin m → (Fin n → Bool) × Bool) (r : A.Coins n)
    (x : Fin n → Bool) :
    learnerFn A n m S r x = decide (A.runAt n (pairEncode ((List.ofFn fun j =>
      pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []) (List.ofFn x)) r = [true]) :=
  rfl

/-- **Examples and a fresh point as one tuple:** `((k, (s, r)), x) ↦ (k, (snoc s x, r))`. -/
def snocEquiv (K X ρ : Type*) (m : ℕ) :
    (K × ((Fin m → X) × ρ)) × X ≃ K × ((Fin (m + 1) → X) × ρ) where
  toFun w := (w.1.1, (Fin.snoc w.1.2.1 w.2, w.1.2.2))
  invFun z := ((z.1, (Fin.init z.2.1, z.2.2)), z.2.1 (Fin.last m))
  left_inv w := by
    obtain ⟨⟨k, s, r⟩, x⟩ := w
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv z := by
    obtain ⟨k, t, r⟩ := z
    simp only [Fin.snoc_init_self]

/-- `snocEquiv K X ρ m ((k, (s, r)), x) = (k, (Fin.snoc s x, r))`. -/
theorem snocEquiv_apply (K X ρ : Type*) (m : ℕ) (w : (K × ((Fin m → X) × ρ)) × X) :
    snocEquiv K X ρ m w = (w.1.1, (Fin.snoc w.1.2.1 w.2, w.1.2.2)) := rfl

/-- **The distinguisher's acceptance probability is the game probability** [PS10, Theorem 179.1,
proof, step 1]: for a learner machine `A` and a polynomial `m` there is a next-query machine `B`
such that for every `n` and every family `G : K → {0,1}^n → {0,1}^n` (uniform keys),
`acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n) + 1)))` is
`gameProb (m n) G (learnerFn A n (m n))`.

**Proof sketch.** `B` is `exists_learnDist A m`. Relabel the seeds `(k, c)` of the acceptance
probability by `((k, (s, r)), x) ↦ (k, φ (snoc s x, r))` (`uprob_comp_equiv`, `snocEquiv`,
`Equiv.prodCongr`); the verdict of `B` at `φ (snoc s x, r)` against `G k` is the learner's
prediction on the examples `s` labelled by `firstBit ∘ G k` compared with `firstBit (G k x)`
(`exists_learnDist`, `Fin.snoc_castSucc`, `Fin.snoc_last`, `label_apply`). -/
theorem exists_learnDist_acceptProb (A : NUPPT) (m : PolyExpr) :
    ∃ B : NUPPT, ∀ (n : ℕ) {K : Type*} [Fintype K] (G : K → (Fin n → Bool) → (Fin n → Bool)),
      acceptProb G (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) =
        gameProb (m.eval n) G (learnerFn A n (m.eval n)) := by
  obtain ⟨B, hB⟩ := exists_learnDist A m
  refine ⟨B, fun n K _ G => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  rw [acceptProb_def, gameProb_eq, ← uprob_comp_equiv ((snocEquiv K (Fin n → Bool) (A.Coins n)
    (m.eval n)).trans ((Equiv.refl K).prodCongr φ))]
  congr 1
  funext w
  have hlab : ∀ (c : (Fin n → Bool) → Bool) (s : Fin (m.eval n) → Fin n → Bool),
      label c s = fun j => (s j, c (s j)) := fun c s => funext (label_apply c s)
  rw [Equiv.trans_apply, snocEquiv_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_apply, oracleDist_apply, hφ, learnerFn_eq, Fin.snoc_last, hlab]
  simp only [Fin.snoc_castSucc]

end Game

end TCSlib.Cryptography.Randomness.LearnPRF
