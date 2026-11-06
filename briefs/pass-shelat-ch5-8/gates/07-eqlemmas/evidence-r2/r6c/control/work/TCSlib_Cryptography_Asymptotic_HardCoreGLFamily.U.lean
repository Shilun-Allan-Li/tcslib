/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGL

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter for function families

The family side of [PS10, Theorem 87.3] (`FunFamily.StrongOneWay.glPad_hardCore` in
`Asymptotic/HardCore.lean`): the guess count `glK` for a predictor of advantage `n^{−c}` and its
polynomial majorant, the evaluator of the bit `⟨x, r⟩` on `⟨1^n, x ‖ r⟩`, the inverter
`glFamMachine` of `g(x, r) = (f(x), r)` obtained by wrapping the recovery machine `glMachine`
of `Asymptotic/HardCoreGL.lean` (applied to the predictor pre-processed to query `y ‖ q`), and
the identity `invProbOpt_glFam_eq` between its inversion probability and that of the concrete
inverter `HardcoreBit.guessInverter` [PS10, Algorithm 89.6; Gar26, Figure 2.5].

## Main definitions

* `TCSlib.Cryptography.glK`, `TCSlib.Cryptography.glKBound` — the guess count and its
  polynomial majorant.
* `TCSlib.Cryptography.glFamMachine` — the inverter of `g(x, r) = (f(x), r)`.

## Main results

* `TCSlib.Cryptography.glK_real`, `TCSlib.Cryptography.two_pow_glK_le` — the guess-count
  inequalities.
* `TCSlib.Cryptography.exists_glBitEvaluator` — the bit `⟨x, r⟩` is polynomial-time computable.
* `TCSlib.Cryptography.invProbOpt_glFam_eq` — the family inverter inverts exactly as often as
  `guessInverter`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The guess count and its bounds -/

/-- The guess count `k(n) := size (2 m(n) n^{2c})` of the reduction for a predictor of advantage
`n^{−c}`: `2 m n^{2c} < 2^k`, i.e. `2 m ≤ ε²(2^k − 1)` for `ε = n^{−c}`. -/
def glK (mP : PolyExpr) (c n : ℕ) : ℕ := Nat.size (2 * mP.eval n * n ^ (2 * c))

/-- The polynomial majorant `4 m n^{2c} + 1` of `2^{k(n)}`. -/
def glKBound (mP : PolyExpr) (c : ℕ) : PolyExpr :=
  .add (.mul (.const 4) (.mul mP (.pow .var (2 * c)))) (.const 1)

/-- `2 m n^{2c} < 2^{k(n)}`. -/
theorem lt_two_pow_glK (mP : PolyExpr) (c n : ℕ) : 2 * mP.eval n * n ^ (2 * c) < 2 ^ glK mP c n :=
  Nat.lt_size_self _

/-- `2^{k(n)} ≤ 4 m n^{2c} + 1`. -/
theorem two_pow_glK_le (mP : PolyExpr) (c : ℕ) (n : ℕ) :
    2 ^ glK mP c n ≤ (glKBound mP c).eval n := by
  simp only [glKBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var]
  unfold glK
  calc 2 ^ Nat.size (2 * mP.eval n * n ^ (2 * c)) ≤ 2 * (2 * mP.eval n * n ^ (2 * c)) + 1 :=
        two_pow_size_le _
    _ = 4 * (mP.eval n * n ^ (2 * c)) + 1 := by ring

/-- The real form of the guess-count inequality: `2 m ≤ ε² (2^k − 1)` for `ε = 1/n^c`, `n ≥ 1`. -/
theorem glK_real (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    2 * (mP.eval n : ℝ) ≤ (1 / (n : ℝ) ^ c) ^ 2 * ((2 : ℝ) ^ glK mP c n - 1) := by
  have h := lt_two_pow_glK mP c n
  have hnR : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by exact_mod_cast hn) c
  have hcast : (2 * (mP.eval n : ℝ) * (n : ℝ) ^ (2 * c)) + 1 ≤ (2 : ℝ) ^ glK mP c n := by
    exact_mod_cast h
  rw [one_div, inv_pow, ← pow_mul, mul_comm c 2]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- The guess count is positive when the block length is (`n ≥ 1`). -/
theorem glK_pos_or (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    0 < 2 ^ glK mP c n - 1 ∨ mP.eval n = 0 := by
  rcases Nat.eq_zero_or_pos (mP.eval n) with hm | hm
  · exact Or.inr hm
  · left
    have h := lt_two_pow_glK mP c n
    have : 0 < 2 * mP.eval n * n ^ (2 * c) := by positivity
    omega

/-! ## The inverter of `g(x, r) = (f(x), r)` from the recovery machine -/

/-- Pre-processing of the family inverter: on the view of `⟨1^n, y ‖ r⟩`, the string
`y = (y ‖ r).take (outLen n)`. -/
def glFamPre (oP : PolyExpr) (v : List Bool) : List Bool :=
  (NUPPT.inArg v).take (oP.eval (NUPPT.inParam v).length)

/-- The pre-processing is polynomial-time. -/
theorem glFamPre_poly (oP : PolyExpr) : PolyTimeComputable (glFamPre oP) := by
  convert (polyTimeComputable_pairTakePoly oP).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg) using 1
  funext v
  simp [glFamPre]

/-- Post-processing of the family inverter: `answer ++ (y ‖ r).drop (outLen n)`. -/
def glFamPost (oP : PolyExpr) (v : List Bool) : List Bool :=
  pairSndD v ++ (NUPPT.inArg (pairFstD v)).drop (oP.eval (NUPPT.inParam (pairFstD v)).length)

/-- The post-processing is polynomial-time. -/
theorem glFamPost_poly (oP : PolyExpr) : PolyTimeComputable (glFamPost oP) := by
  have h : PolyTimeComputable fun v =>
      (NUPPT.inArg (pairFstD v)).drop (oP.eval (NUPPT.inParam (pairFstD v)).length) := by
    convert (polyTimeComputable_pairDropPoly oP).comp
      ((NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairFstD).pairEncode
        (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)) using 1
    funext v
    simp
  exact polyTimeComputable_pairSndD.append h

/-- **The inverter of `g(x, r) = (f(x), r)`** [PS10, Algorithm 89.6]: the recovery machine on
`y = (y ‖ r).take (outLen n)`, its answer `x'` followed by `r`. -/
noncomputable def glFamMachine (A : NUPPT) (iP oP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  (glMachine A iP K k hk).wrap (glFamPre_poly oP) (glFamPost_poly oP) (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 0)

/-- The family inverter on `y ‖ r` with coins `c` (as a string) returns the recovery machine's
answer on `y` followed by `r`. -/
theorem glFamMachine_runAt (A : NUPPT) (iP oP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (y : Fin (oP.eval n) → Bool) (r : Fin (iP.eval n) → Bool)
    (c : (glMachine A iP K k hk).Coins n) (r' : (glFamMachine A iP oP K k hk).Coins n)
    (hr' : List.ofFn r' = List.ofFn c) :
    (glFamMachine A iP oP K k hk).runAt n (List.ofFn y ++ List.ofFn r) r' =
      (glMachine A iP K k hk).runAt n (List.ofFn y) c ++ List.ofFn r := by
  unfold glFamMachine
  rw [NUPPT.runAt_wrap (glMachine A iP K k hk) (glFamPre_poly oP) (glFamPost_poly oP) _ _ _
    (.const 0) n _ rfl (fun _ : Fin 0 => false) c r' (by rw [hr']; rfl)]
  simp [glFamPre, glFamPost]

/-! ## The evaluator of `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` -/

/-- **The evaluator of the Goldreich–Levin bit** `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` (the efficiency clause
of [PS10, Theorem 87.3], Fact 88.4): cut after `inLen n` bits and apply `ipFun`. -/
theorem exists_glBitEvaluator (iP : PolyExpr) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x r : Fin (iP.eval n) → Bool),
        H (NUPPT.advInput n (List.ofFn x ++ List.ofFn r)) = [HardcoreBit.ip x r] := by
  refine ⟨fun w => ipFun (pairEncode ((pairSndD w).take (iP.eval (pairFstD w).length))
      ((pairSndD w).drop (iP.eval (pairFstD w).length))),
    ptcComp ipFun_poly ((polyTimeComputable_pairTakePoly iP).pairEncode
      (polyTimeComputable_pairDropPoly iP)), fun n x r => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    take_ofFn_append, drop_ofFn_append, ipFun_ofFn]

/-! ## The inversion probability of the family inverter -/

/-- The pre-processing `⟨Y, q⟩ ↦ Y ++ q` of the family predictor. -/
def concatPre (z : List Bool) : List Bool := pairFstD z ++ pairSndD z

/-- The pre-processing is polynomial-time. -/
theorem concatPre_poly : PolyTimeComputable concatPre := polyTimeComputable_pairConcat

/-- The predictor of the family, called by the recovery machine on the pair `⟨y, q⟩`, computes
the concrete predictor `A(1^n, y ‖ q)` of [PS10, Algorithm 89.6]. -/
theorem glPredictorOf_precomp_concat (A : NUPPT) (n o m : ℕ) (y : Fin o → Bool) (q : Fin m → Bool)
    (c : (A.precomp concatPre_poly).Coins n) :
    glPredictorOf (A.precomp concatPre_poly) n m (fun y : Fin o → Bool => List.ofFn y) (y, q) c =
      A.predictor n (o + m) (Fin.appendEquiv o m (y, q)) (A.precomp_coinsEquiv concatPre_poly n c) := by
  simp only [glPredictorOf, NUPPT.runAtL_precomp, concatPre, pairFstD_pairEncode, pairSndD_pairEncode,
    NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_eq, ofFn_appendEquiv,
    NUPPT.precomp_coinsEquiv_ofFn]


/-- **The inversion probability of the family inverter is that of the concrete inverter**
`guessInverter` of [PS10, Algorithm 89.6; Gar26, Figure 2.5] against `HardcoreBit.glPad (f n)`,
for the predictor `A'(y, q) = A(1^n, y ‖ q)`.

**Proof sketch.** Reindex the input by `appendEquiv` and the coins by `glCoinsEquiv` (the unread
coins are dropped by `uprob_fst`); on `(x, r)` with coins `(s, b, c)` the family inverter
returns `guessRecover … ‖ r` (`glFamMachine_runAt`, `glMachine_runAt_guessRecover`), which
inverts `g(x, r) = (f(x), r)` exactly when `guessInverter` does. -/
theorem invProbOpt_glFam_eq (𝓕 : FunFamily) (A : NUPPT) (K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ 𝓕.inLen.eval n = 0) :
    invProbOpt (fun z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool =>
        Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
          (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)))
      ((glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen K k hk).inverter n
        (𝓕.inLen.eval n + 𝓕.inLen.eval n) (𝓕.outLen.eval n + 𝓕.inLen.eval n)) =
    invProb (HardcoreBit.glPad (𝓕.f n))
      (HardcoreBit.guessInverter
        (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) (k n)) := by
  set A₁ := A.precomp concatPre_poly with hA₁
  have hpred : (fun (y : (Fin (𝓕.outLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) (c : A.Coins n) =>
      A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n) (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) =
      glPredictorOf A₁ n (𝓕.inLen.eval n) (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) := by
    funext y c
    obtain ⟨y, q⟩ := y
    exact (glPredictorOf_precomp_concat A n (𝓕.outLen.eval n) (𝓕.inLen.eval n) y q c).symm
  rw [hpred]
  unfold invProbOpt invProb
  have hcoins : (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).coinLen n = (glCoins 𝓕.inLen K A₁).eval n := by
    simp [glFamMachine, NUPPT.coinLen]
  let eC : HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n) ×
      (Fin ((glCoins 𝓕.inLen K A₁).eval n - glNeed A₁ 𝓕.inLen k n) → Bool) ≃
      (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).Coins n :=
    (glCoinsEquiv A₁ n (𝓕.inLen.eval n) (k n) _ (glNeed_le A₁ 𝓕.inLen K k hk n)).trans (finCastEquiv hcoins.symm)
  rw [← uprob_comp_equiv ((Equiv.prodAssoc ((Fin (𝓕.inLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool))
    (HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n))
    (Fin ((glCoins 𝓕.inLen K A₁).eval n - glNeed A₁ 𝓕.inLen k n) → Bool)).trans
    ((Fin.appendEquiv (α := Bool) (𝓕.inLen.eval n) (𝓕.inLen.eval n)).prodCongr eC))]
  refine (OneWay.uprob_congr fun w => ?_).trans (uprob_fst fun v : ((Fin (𝓕.inLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) ×
    HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n) =>
      HardcoreBit.glPad (𝓕.f n) (HardcoreBit.guessInverter
        (glPredictorOf A₁ n (𝓕.inLen.eval n) fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) (k n)
        (HardcoreBit.glPad (𝓕.f n) v.1) v.2) = HardcoreBit.glPad (𝓕.f n) v.1)
  obtain ⟨⟨⟨x, r⟩, g⟩, ex⟩ := w
  simp only [Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.symm_apply_apply, NUPPT.inverter_eq_some_iff]
  have hrun : (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).runAt n
      (List.ofFn (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) (HardcoreBit.glPad (𝓕.f n) (x, r)))) (eC (g, ex)) =
      List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (𝓕.inLen.eval n) (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y))
        (k n) (𝓕.f n x) g) ++ List.ofFn r := by
    rw [ofFn_appendEquiv]
    show (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).runAt n (List.ofFn (𝓕.f n x) ++ List.ofFn r) _ = _
    rw [glFamMachine_runAt A₁ 𝓕.inLen 𝓕.outLen K k hk n (𝓕.f n x) r
      ((glMachine_coinsEquiv A₁ 𝓕.inLen K k hk n).symm
        (glCoinsEquiv A₁ n (𝓕.inLen.eval n) (k n) _ (glNeed_le A₁ 𝓕.inLen K k hk n) (g, ex))) _
      (by simp only [eC, Equiv.trans_apply, glMachine_coinsEquiv_symm_ofFn]
          exact ofFn_finCastEquiv _ _),
      glMachine_runAt_guessRecover A₁ 𝓕.inLen K k hk n hM (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y)
        (𝓕.f n x) g ex]
  rw [hrun]
  constructor
  · rintro ⟨x', hx', hfx'⟩
    rw [← ofFn_appendEquiv, List.ofFn_inj] at hx'
    subst hx'
    rw [Equiv.symm_apply_apply] at hfx'
    exact (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).injective hfx'
  · intro hinv
    refine ⟨Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n) (HardcoreBit.guessRecover
      (glPredictorOf A₁ n (𝓕.inLen.eval n) fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) (k n) (𝓕.f n x) g, r),
      (ofFn_appendEquiv _ _).symm, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact congrArg _ hinv

end TCSlib.Cryptography


/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6c/control/work/TCSlib_Cryptography_Asymptotic_HardCoreGLFamily.coll"
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
