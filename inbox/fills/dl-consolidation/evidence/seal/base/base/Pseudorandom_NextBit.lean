/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Lean
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.NextBit.Concrete
/- DLC-SEAL Pseudorandom_NextBit: whole-file closure seal of `TCSlib/Cryptography/Pseudorandom/NextBit.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
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
  Lean.logInfo m!"DLC-SEAL Pseudorandom_NextBit: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The next-bit characterization of pseudorandom ensembles

The next-bit test bounds the success of every non-uniform polynomial-time predictor by
one half plus a negligible function. The predictor receives `1^n` and the prefix of the
sample [PS10, Definition 75.2 and Remark 75.3]. The reductions implement the finite
predictor and distinguisher as machines. For completeness, the predictor gets the sign in
its advice and reads the position from the prefix length. Where the output length is zero,
the distinguishing advantage is zero and there is no position to choose.

## Main definitions

* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable` gives the next-bit test with a single
  negligible bound for all positions.

## Main results

* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom` gives completeness
  of the test [PS10, Theorem 75.4].
* `TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable` gives the converse.
* `TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable` establishes the test for
  the uniform ensemble.

## Contents

* `Concrete` gives the finite next-bit experiments, hybrids, and advantage bounds.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.2: Definition 75.2, Remark 75.3, Theorem 75.4, Algorithm 76.5.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- **Passing the next-bit test** [PS10, Definition 75.2]: for every non-uniform PPT `A` there
is a negligible `ε` such that for all `n` and all positions `i < ℓ(n)`,
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}] ≤ 1/2 + ε(n)`. The predictor is the machine `A`
activated at parameter `n` on `⟨1^n, t_1 ⋯ t_i⟩` (`A.predictor n i`), which is the convention
of [PS10, Remark 75.3]: `A` receives `1^n` so that its size and running time may be polynomial
in `n` rather than in the possibly short prefix. The quantifier order `∀ A ∃ ε ∀ n ∀ i` is the
text's (one negligible function for all positions).

**Deviation:** `NextBitUnpredictable`: the position ranges over the existing bits `i < ℓ(n)`
(the text's `i ∈ [0, ℓ(n)]` includes the nonexistent bit `t_{ℓ(n)+1}`); the bound is
`≤ 1/2 + ε(n)` instead of the text's strict `<` (equivalent, `nextBitUnpredictable_iff_lt`);
the predictor receives `1^n` [PS10, Remark 75.3] (D5). -/
def Ensemble.NextBitUnpredictable {ℓ : PolyExpr} (X : Ensemble ℓ) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1 / 2 + ε n

/-- **The text's strict form of Definition 75.2** — "there exists a negligible `ε` with
success `< 1/2 + ε(n)` for all `n` and `i`" — is equivalent to the frozen `≤` form
[PS10, Definition 75.2]: one direction is `le_of_lt`, the other replaces `ε(n)` by
`ε(n) + 2^{-n}`. -/
theorem Ensemble.nextBitUnpredictable_iff_lt {ℓ : PolyExpr} (X : Ensemble ℓ) :
    X.NextBitUnpredictable ↔ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) < 1 / 2 + ε n := by
  constructor
  · intro h A
    obtain ⟨ε, hε, hle⟩ := h A
    refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n i => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith [hle n i]
  · intro h A
    obtain ⟨ε, hε, hlt⟩ := h A
    exact ⟨ε, hε, fun n i => (hlt n i).le⟩

/-- Bit `i` of `u` is the head of the suffix `(ofFn u).drop i` — the readout
`polyTimeComputable_headD` of the machines below (`List.head?_drop`, `List.getElem?_ofFn`). -/
private theorem headD_drop_ofFn {ℓ : ℕ} (i : Fin ℓ) (u : Fin ℓ → Bool) :
    ((List.ofFn u).drop i).headD false = u i := by
  rw [List.headD_eq_head?, List.head?_drop, List.getElem?_ofFn]
  simp [i.isLt]

/-- A distinguisher whose coin string is reindexed by a bijection has the same acceptance
probability (`uprob_comp_equiv` on the coin factor of the sample space). -/
private theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (e : ρ ≃ ρ') (D : γ → ρ' → Bool) (D' : γ → ρ → Bool)
    (h : ∀ x r, D x (e r) = D' x r) : acceptProb X D = acceptProb X D' := by
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl σ) e)]
  apply OneWay.uprob_congr
  intro z
  simp [h]

/-! ### Completeness of the next-bit test [PS10, Theorem 75.4] -/

/-- **The next-bit predictor as a machine** [PS10, Algorithm 76.5]: for a distinguisher
machine `D` and signs `flip n`, a non-uniform PPT `A` with coins `ℓ + D.coins` and advice
`⟨D.advice n, [flip n]⟩` such that, at every parameter `n` and every position `i < ℓ(n)`, `A`
on the prefix `t` with coins `(u, c)` (split by `e n`) is exactly the concrete predictor
`nextBitPred (D.distinguisher n (ℓ n)) i (flip n) t (u, c)`: it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `u_{|t|}` or its negation according to the verdict,
negated once more if `flip n`. The position is read off the prefix length `|t| = i`, so only
the sign is hard-wired, and the identity holds at every position (restated so at gate 03c,
finding 2: no choice of position is needed where `ℓ(n) = 0`).

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨D.advice n, [flip n]⟩⟩, r⟩` cuts `r`
into `u := r.take (ℓ n)` and `c := r.drop (ℓ n)` (`polyTimeComputable_pairTakePoly`/
`pairDropPoly ℓ` on `⟨1^n, r⟩`), forms `w := y ++ u.drop |y|` (`pairDropPoly var` on `⟨y, u⟩`,
`PolyTimeComputable.append`), runs `D.output` on `layout 1^n w (D.advice n) c`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), tests the verdict against `[true]`
(`polyTimeComputable_pairEq`), reads `u_{|y|}` as the head of `u.drop |y|` and the sign as the head
of the advice's second component (`polyTimeComputable_headD`), and combines them
(`polyTimeComputable_ite`, `polyTimeComputable_not`, `BinArith.polyTimeComputable_xor`).
`A := ofPolyTime` of it with coins `add ℓ D.coins` and advice bound `2·D.adv + 3`
(`length_pairEncode`); the coin split is `Fin.appendEquiv` composed with `finCongr`, and the
identity is `runAtL_ofPolyTime`, the projection identities of the layout,
`List.take_left'`/`List.drop_left'`, `ofFn_completePrefix` and `headD_drop_ofFn`. -/
private theorem exists_nextBitPredMachine (ℓ : PolyExpr) (D : NUPPT) (flip : ℕ → Bool) :
    ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
      ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
        A.predictor n i t (e n (u, c)) =
          nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n) t (u, c) := by
  -- the coin cut `⟨1^n, r⟩ ↦ u = r.take (ℓ n)`, `c = r.drop (ℓ n)`
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hu : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairTakePoly ℓ).comp hcut using 1
    funext z
    simp
  have hc : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairDropPoly ℓ).comp hcut using 1
    funext z
    simp
  -- the suffix `u.drop |y|` and the completed word `w = y ++ u.drop |y|`
  have hud : PolyTimeComputable fun z =>
      ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop (NUPPT.inArg z).length := by
    convert (polyTimeComputable_pairDropPoly .var).comp
      (NUPPT.polyTimeComputable_inArg.pairEncode hu) using 1
    funext z
    simp
  have hw := NUPPT.polyTimeComputable_inArg.append hud
  -- the call to `D` and its verdict
  have hg := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hw
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice) hc)
  have hgb : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hg.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  -- the bit `u_{|y|}` and the sign
  have hui := polyTimeComputable_headD.comp hud
  have hflip : PolyTimeComputable fun z => [(pairSndD (NUPPT.inAdvice z)).headD false] :=
    polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice)
  have hsel : PolyTimeComputable fun z => [if decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true]) then
        (((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false
      else !(((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false] := by
    convert polyTimeComputable_ite hgb hui (polyTimeComputable_not hui) using 1
    funext z
    split_ifs <;> rfl
  have hF := BinArith.polyTimeComputable_xor hsel hflip
  -- the advice `⟨D.advice n, [flip n]⟩`
  have hadv : ∀ n, (pairEncode (D.advice n) [flip n]).length ≤
      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) (.const 1)).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, List.length_singleton]
    have := D.advice_length n
    omega
  let A := NUPPT.ofPolyTime hF (.add ℓ D.coins) _ (fun n => pairEncode (D.advice n) [flip n]) hadv
  have hlen : ∀ n, A.coinLen n = ℓ.eval n + D.coinLen n := fun n => by
    simp only [A, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTime, PolyExpr.eval_add]
  let e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n := fun n =>
    (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (hlen n).symm) (Equiv.refl Bool))
  refine ⟨A, e, fun n i t u c => ?_⟩
  have hofn : List.ofFn (e n (u, c)) = List.ofFn u ++ List.ofFn c := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (hlen n).symm (Fin.append u c)).symm
  simp only [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
      hofn, nextBitPred_eq]
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.advInput_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inAdvice_eq,
      NUPPT.inCoins_eq,
    NUPPT.runAtL_eq, List.take_left', List.drop_left', ofFn_completePrefix]
  split_ifs <;> cases u i <;> cases flip n <;> rfl

/-- **Completeness of the next-bit test** [PS10, Theorem 75.4]: if the ensemble `{X_n}` over
`{0,1}^{ℓ(n)}` passes the next-bit test, then it is pseudorandom.

**Repair (run-3 audit P2-2):** the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` was dropped
(it is the field `Ensemble.nonempty`; with an empty seed type the experiment has probability
`0`, the ensemble passes the next-bit test vacuously, and the always-accepting distinguisher
has advantage `1`); the frozen shape of DESIGN.md §2.12 is restored.

**Repair (gate 03c, finding 2; ruling G3-7b):** the hypothesis `hℓ : ∀ n, 0 < ℓ.eval n`, which
the text does not have, was dropped; the theorem now applies to every ensemble, `ℓ(0) = 0`
included (e.g. `ℓ = n`, `2n`, `n²`).

**Proof sketch.** By contradiction, as in the text. Fix a distinguisher `D` with
`¬ Negligible (fun n => prgAdv (X_n) (D.distinguisher n (ℓ n)))`
(`Ensemble.pseudorandom_iff_prgAdv`); by `not_negligible_iff_exists_polyExpr` there is a
positive syntactic polynomial `p` with `1/p(n) ≤ prgAdv` for infinitely many `n`. At every
`n` with `ℓ(n) > 0`, `exists_nextBitPred` (with the instance `X.nonempty n`) gives a position
`i_n < ℓ(n)` and a sign `flip_n` with
`1/2 + prgAdv/ℓ(n) ≤ nextBitProb (X_n) i_n (nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n)`;
where `ℓ(n) = 0` put `flip_n := false` (`choose` on "a sign, and a position if `ℓ(n) > 0`").
The predictor machine `A` is `exists_nextBitPredMachine ℓ D flip` (advice
`⟨D.advice n, [flip_n]⟩`, coins `ℓ + D.coins`; on `⟨1^n, t⟩` with coins `u ++ c` it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `xor (if g then u_{|t|} else !u_{|t|}) flip_n`, the
position being read off the prefix length). Its functional identity, at every position `i`,
`A.predictor n i t (e (u, c)) = nextBitPred (D.distinguisher n (ℓ n)) i flip_n t (u, c)`
along the coin split `e : (Fin (ℓ n) → Bool) × D.Coins n ≃ A.Coins n` (`Fin.appendEquiv`)
gives `nextBitProb (X_n) i (A.predictor n i) = nextBitProb (X_n) i (nextBitPred …)`
(`uprob_comp_equiv`). Now `h A` gives a negligible `ε` with `nextBitProb … ≤ 1/2 + ε n` for
all `n, i`. At every `n` of the infinite set, `ℓ(n) > 0`, since at `ℓ(n) = 0` the advantage is
`0 < 1/p(n)` (`prgAdv_eq_zero_of_length_eq_zero`); there
`1/(p(n)(ℓ(n) + 1)) ≤ 1/(p(n) ℓ(n)) ≤ prgAdv/ℓ(n) ≤ ε n`, i.e. `¬ Negligible ε` by
`not_negligible_iff_exists_polyExpr` with the positive polynomial `mul p (ℓ + 1)`, a
contradiction. -/
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (h : X.NextBitUnpredictable) : X.Pseudorandom := by
  rw [Ensemble.pseudorandom_iff_prgAdv]
  intro D
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  -- a sign at every `n`, and a position where `ℓ(n) > 0` (the concrete reduction)
  have hex : ∀ n, ∃ flip : Bool, 0 < ℓ.eval n → ∃ i : Fin (ℓ.eval n),
      1 / 2 + prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n) ≤
        nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i flip) := by
    intro n
    by_cases hn : 0 < ℓ.eval n
    · obtain ⟨i, flip, hif⟩ := exists_nextBitPred hn (X.X n) (D.distinguisher n (ℓ.eval n))
      exact ⟨flip, fun _ => ⟨i, hif⟩⟩
    · exact ⟨false, fun hn' => absurd hn' hn⟩
  choose flip hif using hex
  -- the predictor machine, and its identity with the concrete predictor at every position
  obtain ⟨A, e, hA⟩ := exists_nextBitPredMachine ℓ D flip
  obtain ⟨ε, hε, hbound⟩ := h A
  have hprob : ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) =
      nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n)) := by
    intro n i
    simp only [nextBitProb_eq]
    rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (X.σ n)) (e n))]
    apply OneWay.uprob_congr
    rintro ⟨s, u, c⟩
    simp [hA]
  -- `ε` is not negligible, with the positive polynomial `p · (ℓ + 1)`
  refine (not_negligible_iff_exists_polyExpr.mpr
    ⟨.mul p (.add ℓ (.const 1)), fun n => ?_, fun n₀ => ?_⟩) hε
  · simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
    exact Nat.mul_pos (hp n) (Nat.succ_pos _)
  · obtain ⟨n, hn, hpn⟩ := hinf n₀
    refine ⟨n, hn, ?_⟩
    have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    have h0 : 0 ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) := by
      rw [prgAdv_eq, distAdv_def]
      exact abs_nonneg _
    rw [abs_of_nonneg h0] at hpn
    -- on the infinite set `ℓ(n) > 0`: at `ℓ(n) = 0` the advantage is `0`
    have hℓn : 0 < ℓ.eval n := by
      rcases Nat.eq_zero_or_pos (ℓ.eval n) with hz | hz
      · have hzero := prgAdv_eq_zero_of_length_eq_zero hz (X.X n) (D.distinguisher n (ℓ.eval n))
        have := one_div_pos.mpr hppos
        linarith
      · exact hz
    obtain ⟨i, h1⟩ := hif n hℓn
    have h2 := hbound n i
    rw [hprob n i] at h2
    have hℓpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast hℓn
    have hstep : (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ) ≤
        (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := by
      rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, div_div]
      push_cast
      exact one_div_le_one_div_of_le (mul_pos hppos hℓpos)
        (mul_le_mul_of_nonneg_left (by linarith) hppos.le)
    calc (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ)
        ≤ (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := hstep
      _ ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n : ℝ) := by gcongr
      _ ≤ ε n := by linarith
      _ ≤ |ε n| := le_abs_self _

/-! ### Soundness of the next-bit test -/

/-- **The uniform ensemble passes the next-bit test** (non-vacuity of
[PS10, Definition 75.2]): every predictor succeeds with probability exactly `1/2`, so
`ε := 0` works. -/
theorem Ensemble.uniform_nextBitUnpredictable (ℓ : PolyExpr) :
    (Ensemble.uniform ℓ).NextBitUnpredictable := by
  intro A
  refine ⟨fun _ => 0, negligible_zero, fun n i => ?_⟩
  have hrel : nextBitProb ((Ensemble.uniform ℓ).X n) i (A.predictor n i) =
      nextBitProb (id : (Fin (ℓ.eval n) → Bool) → Fin (ℓ.eval n) → Bool) i (A.predictor n i) := by
    simp only [nextBitProb_eq]
    rw [← uprob_comp_equiv ((Equiv.cast (Ensemble.uniform_σ ℓ n)).prodCongr (Equiv.refl _))]
    refine congrArg uprob (funext fun z => ?_)
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, id_eq,
      Ensemble.uniform_X, Equiv.cast_apply, cast_cast, cast_eq]
  rw [hrel, nextBitProb_id]
  simp

/-- **The next-bit statistical test as a machine**: for a predictor machine `A` and positions
`k n ≤ ℓ(n)`, a non-uniform PPT `Dm` with `A`'s coins and advice `⟨A.advice n, 1^{k n}⟩` which
on `⟨1^n, y⟩` runs `A(1^n, y.take (k n); r)`, reads bit `k n` of `y` and accepts iff the
verdict equals the bit — the untyped form of `nextBitDist (k n) (A.predictor n (k n))`.

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨A.advice n, 1^{k n}⟩⟩, r⟩` cuts
`y` at the unary length of the advice's second component (`polyTimeComputable_pairTakePoly`/
`pairDropPoly var` on `⟨1^{k n}, y⟩`), runs `A.output` on `layout 1^n (y.take (k n)) (A.advice n) r`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), reads the bit as the head of
`y.drop (k n)` (`polyTimeComputable_headD`) and compares twice with `polyTimeComputable_pairEq`
(verdict against `[true]`, then against the bit). `Dm := ofPolyTime` of it with `A.coins` and
advice bound `2·A.adv + 2 + ℓ` (`length_pairEncode`, `hk`); the identity is
`runAtL_ofPolyTime` plus the projection identities of the layout. -/
private theorem exists_nextBitDistMachine {ℓ : PolyExpr} (A : NUPPT) (k : ℕ → ℕ)
    (hk : ∀ n, k n ≤ ℓ.eval n) :
    ∃ Dm : NUPPT, Dm.coins = A.coins ∧ ∀ n (y r : List Bool),
      Dm.runAtL n y r = [decide ([decide (A.runAtL n (y.take (k n)) r = [true])] =
        [(y.drop (k n)).headD false])] := by
  have hkk := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice
  have hpair := hkk.pairEncode NUPPT.polyTimeComputable_inArg
  have hy₁ : PolyTimeComputable fun z =>
      (NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp hpair using 1
    funext z
    simp
  have hb : PolyTimeComputable fun z =>
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false] := by
    convert polyTimeComputable_headD.comp ((polyTimeComputable_pairDropPoly .var).comp hpair)
      using 1
    funext z
    simp
  have ha := A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hy₁
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice)
    NUPPT.polyTimeComputable_inCoins)
  have hx : PolyTimeComputable fun z => [decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] := by
    convert polyTimeComputable_pairEq.comp (ha.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  have hG : PolyTimeComputable fun z => [decide ([decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] =
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false])] := by
    convert polyTimeComputable_pairEq.comp (hx.pairEncode hb) using 1
    funext z
    simp
  have hadv : ∀ n, (pairEncode (A.advice n) (List.replicate (k n) true)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) ℓ).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have := A.advice_length n
    have := hk n
    omega
  refine ⟨NUPPT.ofPolyTime hG A.coins _
    (fun n => pairEncode (A.advice n) (List.replicate (k n) true)) hadv, NUPPT.coins_ofPolyTime ..,
    fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  refine congrArg (fun b : Bool => [b]) (decide_eq_decide.2 ?_)
  refine Iff.of_eq (congrArg₂ (fun a b : Bool => [a] = [b]) (decide_eq_decide.2 ?_) ?_)
  · simp only [NUPPT.advInput_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
      NUPPT.inAdvice_eq, NUPPT.inCoins_eq, NUPPT.runAtL_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]
  · simp only [NUPPT.advInput_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
      NUPPT.inAdvice_eq, NUPPT.inCoins_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]

/-- **Soundness of the next-bit test, asymptotic form** (the converse of
[PS10, Theorem 75.4], implicit in the text's "a pseudorandom distribution needs to pass all
efficiently computable statistical tests", p. 74): a pseudorandom ensemble passes the
next-bit test.

**Proof sketch.** Fix a predictor machine `A` and let
`ε n := max_{i < ℓ n} (nextBitProb (X_n) i (A.predictor n i) − 1/2)` (`0` if `ℓ n = 0`),
attained at some `i_n` (`Finset.exists_max_image`); then `nextBitProb ≤ 1/2 + ε n` for all
`n, i`, and it suffices to show `Negligible ε`. Otherwise `not_negligible_iff_exists_polyExpr`
gives a positive `p` with `1/p(n) ≤ |ε n|` infinitely often. The distinguisher machine `D` is
`exists_nextBitDistMachine A k` with `k n := i_n` (`0` if `ε n` is not attained): advice
`⟨A.advice n, 1^{k n}⟩`, coins `A.coins`; on `⟨1^n, t⟩` it runs `A` on `⟨1^n, t.take (k n)⟩`,
reads bit `k n` of `t` and outputs `[decide (verdict = [bit])]`. At every `n` with `ε n ≠ 0`
(every `n` of the infinite set), `ε n` is attained at `i_n = k n`, and the functional identity
`D.distinguisher n (ℓ n) t (e r) = nextBitDist i_n (A.predictor n i_n) t r` (`ofFn_prefixOf`,
`headD_drop_ofFn`, coins reindexed by `e : A.Coins n ≃ D.Coins n` from `finCongr`) gives, by
`prgAdv_nextBitDist` and `acceptProb_coins_equiv`,
`prgAdv (X_n) (D.distinguisher n (ℓ n)) = |nextBitProb (X_n) i_n (A.predictor n i_n) − 1/2| =
|ε n| ≥ 1/p(n)` — the advantage being an absolute value, no choice between the predictor and
its negation is needed — contradicting `hX D` through `not_negligible_iff_exists_polyExpr`. -/
theorem Ensemble.Pseudorandom.nextBitUnpredictable {ℓ : PolyExpr} {X : Ensemble ℓ}
    (hX : X.Pseudorandom) : X.NextBitUnpredictable := by
  classical
  intro A
  have hmax : ∀ n, ∃ v : ℝ,
      (∀ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 ≤ v) ∧
      (v = 0 ∨ ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = v) := by
    intro n
    rcases isEmpty_or_nonempty (Fin (ℓ.eval n)) with hemp | hne
    · exact ⟨0, fun j => (hemp.false j).elim, Or.inl rfl⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (ℓ.eval n)))
        (fun j => nextBitProb (X.X n) j (A.predictor n j) - 1 / 2) Finset.univ_nonempty
      exact ⟨_, fun j => hj₀ j (Finset.mem_univ j), Or.inr ⟨j₀, rfl⟩⟩
  choose ε hεle hεeq using hmax
  refine ⟨ε, ?_, fun n j => by linarith [hεle n j]⟩
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  let k : ℕ → ℕ := fun n =>
    if h : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n then
      (h.choose : ℕ) else 0
  have hk : ∀ n, k n ≤ ℓ.eval n := by
    intro n
    simp only [k]
    split_ifs with h
    · exact h.choose.isLt.le
    · exact Nat.zero_le _
  obtain ⟨Dm, hc, hDm⟩ := exists_nextBitDistMachine A k hk
  have hlen : ∀ n, A.coinLen n = Dm.coinLen n := fun n => by simp only [NUPPT.coinLen_eq, hc]
  let e : ∀ n, A.Coins n ≃ Dm.Coins n := fun n =>
    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
  have hofn : ∀ n (r : A.Coins n), List.ofFn (e n r) = List.ofFn r := fun n r =>
    (List.ofFn_congr (hlen n) r).symm
  refine (not_negligible_iff_exists_polyExpr.mpr ⟨p, hp, fun n₀ => ?_⟩)
    ((Ensemble.pseudorandom_iff_prgAdv X).mp hX Dm)
  obtain ⟨n, hn, hpn⟩ := hinf n₀
  refine ⟨n, hn, ?_⟩
  have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
  have hε0 : ε n ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hpn
    have := one_div_pos.mpr hppos
    linarith
  have hex : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n :=
    (hεeq n).resolve_left hε0
  obtain ⟨j₀, hkn, hspec⟩ : ∃ j₀ : Fin (ℓ.eval n), k n = j₀ ∧
      nextBitProb (X.X n) j₀ (A.predictor n j₀) - 1 / 2 = ε n :=
    ⟨hex.choose, by simp only [k, dif_pos hex], hex.choose_spec⟩
  have hid : ∀ (t : Fin (ℓ.eval n) → Bool) (r : A.Coins n),
      Dm.distinguisher n (ℓ.eval n) t (e n r) = nextBitDist j₀ (A.predictor n j₀) t r := by
    intro t r
    rw [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hDm, hkn]
    rw [nextBitDist_eq]
    rw [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
      ofFn_prefixOf, headD_drop_ofFn]
    simp
  have hadv : prgAdv (X.X n) (Dm.distinguisher n (ℓ.eval n)) = |ε n| := by
    rw [← hspec, ← prgAdv_nextBitDist (X.X n) j₀ (A.predictor n j₀)]
    simp only [prgAdv_eq, distAdv_def]
    rw [acceptProb_coins_equiv (X.X n) (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid,
      acceptProb_coins_equiv id (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid]
  rw [hadv, abs_of_nonneg (abs_nonneg _)]
  exact hpn

end TCSlib.Cryptography
