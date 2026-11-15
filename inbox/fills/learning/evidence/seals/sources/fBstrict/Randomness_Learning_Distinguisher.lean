/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Randomness.Learning.Sample
/- DLC-SEAL Randomness_Learning_Distinguisher: whole-file closure seal of `TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean`, variant B (PolyExpr.eval sealed), strict. -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
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
  Lean.logInfo m!"DLC-SEAL Randomness_Learning_Distinguisher: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF distinguisher built from a learner

Step 1 of [PS10, Theorem 179.1, proof]: from a learner machine `A` and a polynomial number `m` of
examples, a next-query machine `B` that queries its oracle `g` at `m(n) + 1` points `ρ` drawn from
its coins, labels the first `m(n)` by the first bits of the answers, runs `A` (with its own coins)
on the labelled sample and the last point, and accepts when `A`'s prediction (its output being
`[true]`) equals the first bit of the last answer (`exists_learnDist`).

`B` is the query chain of `MultiMsg.exists_queryChain_nuppt` (non-adaptive queries at points
from the coins, the zero message vector) applied to the machine `C` that, on the encoded tuple,
runs `A` on `learnIn m` (`NUPPT.exists_compParam`) and then compares with `lastLabel m`
(`NUPPT.exists_seq` with the uniform machine of `verdictFun`).

## Main definitions

* `LearnPRF.verdictFun`: the comparison of the prediction with the last label.

## Main results

* `LearnPRF.polyTimeComputable_verdictFun`.
* `LearnPRF.exists_learnDist`: the distinguisher and its verdict against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity Turing TCSlib.Cryptography

/-- **The verdict** on the raw layout whose argument is `⟨w, a⟩` (the encoded tuple `w` and the
learner's output `a`) at parameter `u = 1^n`: `[decide (a = [true]) == lastLabel m ⟨u, w⟩]`. -/
def verdictFun (m : PolyExpr) (z : List Bool) : List Bool :=
  [decide (pairSndD (NUPPT.inArg z) = [true]) ==
    lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))]

/-- `verdictFun m z = [decide (pairSndD (inArg z) = [true]) ==
lastLabel m ⟨inParam z, pairFstD (inArg z)⟩]`. -/
theorem verdictFun_eq (m : PolyExpr) (z : List Bool) :
    verdictFun m z =
      [decide (pairSndD (NUPPT.inArg z) = [true]) ==
        lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))] := rfl

/-- The verdict is polynomial-time: an equality test (`polyTimeComputable_pairEq`) selecting the
last label or its negation (`polyTimeComputable_ite`, `polyTimeComputable_not`,
`polyTimeComputable_lastLabel`). -/
theorem polyTimeComputable_verdictFun (m : PolyExpr) : PolyTimeComputable (verdictFun m) := by
  have hArg := NUPPT.polyTimeComputable_inArg
  have hEq : PolyTimeComputable fun z => [decide (pairSndD (NUPPT.inArg z) = [true])] :=
    (polyTimeComputable_pairEq.comp ((polyTimeComputable_pairSndD.comp hArg).pairEncode
      (polyTimeComputable_const [true]))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hL : PolyTimeComputable fun z =>
      [lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))] :=
    (polyTimeComputable_lastLabel m).comp
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_pairFstD.comp hArg))
  refine (polyTimeComputable_ite hEq hL (polyTimeComputable_not hL)).congr fun z => ?_
  rw [verdictFun_eq]
  cases decide (pairSndD (NUPPT.inArg z) = [true]) <;>
    cases lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z))) <;> rfl

/-- The zero message vector leaves the answers unchanged: `(fun _ => false) + y = y`. -/
private theorem zero_add_fun {n : ℕ} (y : Fin n → Bool) : (fun _ => false) + y = y := by
  funext i
  rw [Pi.add_apply]
  cases y i <;> rfl

/-- **The distinguisher of [PS10, Theorem 179.1, proof]:** for a learner machine `A` and a
polynomial `m`, there is a next-query machine `B` whose coins at `n` are, up to a bijection `φ`,
the `m(n) + 1` query points `ρ` and `A`'s coins `c`, and whose query tree with budget `m(n) + 1`,
evaluated against any oracle `g`, is
`decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, where `S` is the nested labelled
examples `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points.

**Proof sketch.** `A₁ := exists_compParam A` with `pre = learnIn m` and `post = pairSndD` runs `A`
on the learner's input; `C := exists_seq A₁ V` with the uniform machine `V` of `verdictFun m`
compares its output with the last label; `B := MultiMsg.exists_queryChain_nuppt C m 0`. Against
`g` the tree of `B` gives `C`'s verdict on the encoded tuple `tupleWord ρ g` (`zero_add_fun`); the
runs of `C`, `A₁` and `V` unfold by their equations (`NUPPT.runAtL_ofPolyTimeUniform`, the layout
readers), the learner's input and the last label are `learnIn_tupleWord` and
`lastLabel_tupleWord`, and `decide ([b] = [true]) = b`. The coins of `C` are those of `A`
(`A.coins + 0`), relabelled by `finCongr` (`ofFn_arrowCongr_finCongr`). -/
theorem exists_learnDist (A : NUPPT) (m : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (m.eval n + 1) → Fin n → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (m.eval n + 1) → Fin n → Bool)
        (c : A.Coins n),
        (B.toOracleAdversary n n n (m.eval n + 1) (φ (ρ, c))).eval g =
          (decide (A.runAt n (pairEncode ((List.ofFn fun j : Fin (m.eval n) =>
              pairEncode (List.ofFn (ρ j.castSucc)) [firstBit (g (ρ j.castSucc))]).foldr
                pairEncode []) (List.ofFn (ρ (Fin.last _)))) c = [true]) ==
            firstBit (g (ρ (Fin.last _)))) := by
  obtain ⟨A₁, hA₁c, -, -, hA₁⟩ :=
    NUPPT.exists_compParam A (polyTimeComputable_learnIn m) polyTimeComputable_pairSndD
  obtain ⟨C, hCc, -, hC⟩ :=
    A₁.exists_seq (NUPPT.ofPolyTimeUniform (polyTimeComputable_verdictFun m) (.const 0))
  obtain ⟨B, hB⟩ := MultiMsg.exists_queryChain_nuppt C m (fun _ _ _ => false)
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hB n
  have hlen : A.coinLen n = C.coinLen n := by
    simp only [NUPPT.coinLen_eq, hCc, hA₁c, NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add,
      PolyExpr.eval_const, Nat.add_zero]
  have hlen₁ : A₁.coinLen n = A.coinLen n := by simp only [NUPPT.coinLen_eq, hA₁c]
  let ψ : A.Coins n ≃ C.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  refine ⟨((Equiv.refl _).prodCongr ψ).trans φ₀, fun g ρ c => ?_⟩
  have hw : (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (ρ j))
      (List.ofFn ((fun _ _ _ => false : ∀ n, Fin (m.eval n + 1) → Fin n → Bool) n j +
        g (ρ j)))) []).flatten = tupleWord ρ g := by
    rw [tupleWord_eq]
    refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
    rw [zero_add_fun]
  have hc : (List.ofFn c).length ≤ A₁.coinLen n := by rw [List.length_ofFn, hlen₁]
  rw [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, hφ₀, hw,
    NUPPT.runAt_eq, ofFn_arrowCongr_finCongr, hC, List.take_of_length_le hc,
    NUPPT.runAtL_ofPolyTimeUniform, hA₁, pairSndD_pairEncode, verdictFun_eq, NUPPT.inArg_eq,
    NUPPT.inParam_eq]
  simp only [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [learnIn_tupleWord, lastLabel_tupleWord, ← NUPPT.runAt_eq]
  cases decide (A.runAt n (pairEncode ((List.ofFn fun j : Fin (m.eval n) =>
      pairEncode (List.ofFn (ρ j.castSucc)) [firstBit (g (ρ j.castSucc))]).foldr pairEncode [])
      (List.ofFn (ρ (Fin.last _)))) c = [true]) <;>
    cases firstBit (g (ρ (Fin.last _))) <;> rfl

end TCSlib.Cryptography.Randomness.LearnPRF
