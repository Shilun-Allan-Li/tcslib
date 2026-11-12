/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIM-NME′ implies non-malleability: the sampler and the games

Direction SIM ⇒ IND of [PS10, Theorem 174.8] ([PSV07, Corollary 1], at one message). An NM
adversary `A` asks a challenge `⟨m₀, m₁⟩` and outputs ciphertexts. The SIM adversary forwards
`A`'s queries, with the sampler `halfSamp S` whose parameter is `⟨m₀, m₁⟩` and which outputs `m_β`
for its single coin `β` (with the empty history). With the coin `β` fixed, the real experiment's
oracles are those of `Ind_β` (`castImpl_indImpl_abs`), so the experiment `NM_β` is the hybrid
oracle's run with the coin `β` (`accept_nmGame_eq_rImpl`).

## Main definitions

* `NMSim.halfSamp`: the sampler `⟨m₀, m₁⟩ ↦ m_β`; `NMSim.halfCoins`: its coins are one bit.

## Main results

* `NMSim.halfSamp_runAt`, `NMSim.ofFn_drawWith_half`, `NMSim.expect_sample_halfCoins`.
* `NMSim.castImpl_indImpl_abs`: the CCA oracles of `Ind_β` are the hybrid oracle with coin `β`.
* `NMSim.accept_nmGame_eq_rImpl`: `NM_β` as a run against the hybrid oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 1 and Corollary 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
open AdaptiveCPA (castImpl castImpl_eq ofFn_cast ofFn_splitHalf_fst ofFn_splitHalf_snd
  padFin_ofFn_zeroBits expect_simulate_castImpl_toCompOn simulate_eq_of_abs)

variable (S : FixedLengthPKScheme)

/-! ### The sampler `⟨m₀, m₁⟩ ↦ m_β` -/

/-- The sampler's raw function on `⟨⟨⟨1^n, a⟩, α⟩, ρ⟩`: the second half of `a` (from position
`msgLen(n)`) if the first coin is `1`, the first `msgLen(n)` bits otherwise. -/
private def halfFun (z : List Bool) : List Bool :=
  if (NUPPT.inCoins z).headD false then
    (NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)
  else (NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length)

/-- The sampler's raw function is polynomial-time. -/
private theorem polyTimeComputable_halfFun : PolyTimeComputable (halfFun S) := by
  have hpa := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp NUPPT.polyTimeComputable_inCoins)
    (((polyTimeComputable_pairDropPoly S.msgLen).comp hpa).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
    (((polyTimeComputable_pairTakePoly S.msgLen).comp hpa).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])

/-- **The sampler `⟨m₀, m₁⟩ ↦ m_β`**: the uniform machine with one coin `β` that outputs, on the
parameter `a = m₀ ‖ m₁`, its first `msgLen(n)` bits for `β = 0` and the rest for `β = 1`. -/
noncomputable def halfSamp : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1)

/-- The sampler on `y` with coins `ρ` outputs `y.drop msgLen(n)` if `ρ`'s first bit is `1` and
`y.take msgLen(n)` otherwise. -/
theorem halfSamp_runAt (n : ℕ) (y : List Bool) (ρ : (halfSamp S).Coins n) :
    (halfSamp S).runAt n y ρ =
      if (List.ofFn ρ).headD false then y.drop (S.msgLen.eval n) else y.take (S.msgLen.eval n) := by
  have hrun : ∀ y r, (halfSamp S).runAtL n y r =
      halfFun S (pairEncode (pairEncode (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n y r
  rw [NUPPT.runAt_eq, hrun, halfFun, NUPPT.inCoins_eq, NUPPT.inArg_eq, NUPPT.inParam_eq,
    NUPPT.advInput_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- A one-bit string is constant: for `k = 1`, `v = fun _ => ⟦v⟧.headD false`. -/
private theorem eq_const_headD {k : ℕ} (hk : k = 1) (v : Fin k → Bool) :
    v = fun _ => (List.ofFn v).headD false := by
  subst hk
  funext j
  rw [List.ofFn_succ, List.headD_cons, Subsingleton.elim j 0]

/-- **The sampler's coins are one bit:** `(halfSamp S).Coins n ≃ Bool`, reading the first bit. -/
noncomputable def halfCoins (n : ℕ) : (halfSamp S).Coins n ≃ Bool where
  toFun ρ := (List.ofFn ρ).headD false
  invFun β := (NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n).symm
    fun _ => β
  left_inv ρ := by
    set e := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n
    have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
    have hρ : (List.ofFn ρ).headD false = (List.ofFn (e ρ)).headD false := by
      rw [NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    show e.symm (fun _ => (List.ofFn ρ).headD false) = ρ
    rw [hρ, ← eq_const_headD h1 (e ρ), Equiv.symm_apply_apply]
  right_inv β := by
    set e := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n
    have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
    show (List.ofFn (e.symm fun _ => β)).headD false = β
    rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn (polyTimeComputable_halfFun S) (.const 1) n,
      Equiv.apply_symm_apply, List.ofFn_const, h1, List.replicate_one, List.headD_cons]

/-- The bijection reads the first coin bit: `halfCoins S n ρ = ⟦ρ⟧.headD false`. -/
theorem halfCoins_apply (n : ℕ) (ρ : (halfSamp S).Coins n) :
    halfCoins S n ρ = (List.ofFn ρ).headD false := rfl

/-- The coin of `β` has first bit `β`: `⟦(halfCoins S n).symm β⟧.headD false = β`. -/
theorem headD_ofFn_halfCoins_symm (n : ℕ) (β : Bool) :
    (List.ofFn ((halfCoins S n).symm β)).headD false = β :=
  (halfCoins S n).apply_symm_apply β

/-- **The sampler's draw with coin `β`:** for a parameter of `2 · msgLen(n)` bits,
`⟦M(a; β)⟧ = if β then ⟦a⟧.drop msgLen(n) else ⟦a⟧.take msgLen(n)`. -/
theorem ofFn_drawWith_half (n : ℕ) {k : ℕ} (a : Fin k → Bool)
    (hk : k = S.msgLen.eval n + S.msgLen.eval n) (β : Bool) :
    List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n a ((halfCoins S n).symm β)) =
      if β then (List.ofFn a).drop (S.msgLen.eval n) else (List.ofFn a).take (S.msgLen.eval n) := by
  rw [drawWith_eq, halfSamp_runAt, headD_ofFn_halfCoins_symm]
  refine GGMRed.ofFn_padFin_of_length ?_
  cases β <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_take, List.length_drop,
    List.length_ofFn] <;> omega

/-- **Averaging over the sampler's coins** is averaging over `β`:
`𝔼_ρ[g ρ] = (g (coin 0) + g (coin 1)) / 2`. -/
theorem expect_sample_halfCoins (n : ℕ) (g : (halfSamp S).Coins n → ℝ) :
    expect (sample ((halfSamp S).Coins n)) g =
      (g ((halfCoins S n).symm false) + g ((halfCoins S n).symm true)) / 2 := by
  rw [← expect_sample_equiv (halfCoins S n).symm, expect_sample, Fintype.sum_bool,
    Fintype.card_bool]
  ring

/-! ### `Ind_β` is the hybrid oracle with coin `β` -/

/-- **The CCA oracles of `Ind_β` are the hybrid oracle with the sampler's coin `β`** (on T2's lengths
with `pl = 2 · msgLen`, `hl = 0`), once the hybrid's state forgets the recorded parameter:
`castImpl (Ind_β) i x (s.map fst) = (rImpl … (coin β) … i x s).bind fun p => pure (p.1, p.2.map fst)`.

**Proof sketch.** `Dec`: the same availability, refusal and decryption (`indImpl_dec_onSpec_cast`,
`rImpl_dec`), the casts keeping the strings (`ofFn_cast`). A repeated challenge repeats the record
with the empty history. A first challenge encrypts `m_β`, which is the sampler's draw with coin `β`
(`ofFn_drawWith_half`, `ofFn_splitHalf_fst/_snd`). -/
theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List Bool)
    (hist : List Bool → List Bool) (ρ' : (halfSamp S).Coins n) (i : Fin 2)
    (x : (bitSpecAt (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
      (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) :
    castImpl (ins := fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
        (outs := fun i => (snmDout S (.const 0) i).eval n) (S.indImpl atk β n pk sk) i x
        (s.map Prod.fst) =
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x s).bind fun p => .pure (p.1, p.2.map Prod.fst) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hd0 : (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) 0 = S.ctLen.eval n := by
    show (snmDin S _ 0).eval n = _
    rw [snmDin_zero]
  have hd1 : (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) 1 =
      (S.msgLen.add S.msgLen).eval n := by
    show (snmDin S _ 1).eval n = _
    rw [snmDin_one]
  match i, x with
  | 0, x =>
    have hc : cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)) =
        padFin (S.ctLen.eval n) (List.ofFn x) := by
      apply List.ofFn_injective
      rw [ofFn_cast (S.inLens_zero n),
        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0, S.inLens_zero]),
        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])]
    have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])
    rw [castImpl_eq, S.indImpl_dec_onSpec_cast, rImpl_dec, hc, Option.isSome_map, hx]
    by_cases hcond : (FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin (S.ctLen.eval n) (List.ofFn x)))) = true
    · rw [if_pos hcond, if_pos hcond, OracleComp.pure_bind, OracleComp.pure_bind]
      dsimp only
      rw [ofFn_cast (S.outLens_zero n).symm]
    · rw [if_neg hcond, if_neg hcond, OracleComp.pure_bind, OracleComp.pure_bind]
      dsimp only
      rw [padFin_ofFn_zeroBits]
  | 1, x =>
    have hh : ∀ {ℓ : ℕ} (m : Fin ℓ → Bool),
        List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
      List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
    cases s with
    | some ya =>
      obtain ⟨y, a⟩ := ya
      rw [Option.map_some, castImpl_eq, S.indImpl_challenge_repeat_onSpec, OracleComp.pure_bind,
        rImpl_some, OracleComp.pure_bind]
      dsimp only
      rw [ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]
    | none =>
      rw [Option.map_none, castImpl_eq, S.indImpl_challenge_none_onSpec, rImpl_none_lazy,
        OracleComp.bind_assoc, OracleComp.bind_assoc]
      refine congrArg _ (funext fun re => ?_)
      rw [OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind]
      dsimp only
      have hdraw : List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) ((halfCoins S n).symm β)) =
          List.ofFn (if β then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n)
            (padFin (S.inLens n 1) (List.ofFn x)))).2 else (FixedLengthScheme.splitHalf
              (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).1) := by
        have hx : List.ofFn (cast (S.indSpec_challengeDom n)
            (padFin (S.inLens n 1) (List.ofFn x))) =
            List.ofFn (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) := by
          rw [ofFn_cast (S.inLens_one n),
            GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd1, hpl, S.inLens_one]),
            GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd1])]
        rw [ofFn_drawWith_half S n _ hpl]
        cases β
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ofFn_splitHalf_fst, hx]
        · rw [if_pos rfl, if_pos rfl, ofFn_splitHalf_snd, hx]
      have he : encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x))
          (if false = true then ρ' else (halfCoins S n).symm β)) re =
          padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
            (if β then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n)
              (padFin (S.inLens n 1) (List.ofFn x)))).2 else (FixedLengthScheme.splitHalf
                (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).1))) re) := by
        rw [if_neg Bool.false_ne_true, encWith_eq, hdraw]
      rw [he, ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]

/-- **`NM_β` is the hybrid run with the sampler's coin `β`:** the experiment of Definition 172.6
for `A` (budget `q`, `ℓ` ciphertexts) and `D` accepts with the expectation, over the keys, `A`'s
coins and `D`'s coins, of `D`'s verdict on `nmOutput sk (s.map fst) ⟦a⟧` for the run of `A` (on
T2's lengths) against the hybrid oracle with coin `β`, its output `a` and final state `s`.

**Proof sketch.** Transport `A`'s run to T2's lengths (`nmCodec_eq_bitCodec`,
`expect_simulate_castImpl_toCompOn` with `snmDin_eval_inLens`, `snmDout_eval_outLens`) and pass to
the hybrid oracle through the state abstraction `s ↦ s.map fst` (`simulate_eq_of_abs`,
`castImpl_indImpl_abs`). -/
theorem accept_nmGame_eq_rImpl (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (β : Bool)
    (n : ℕ) (hist : List Bool → List Bool) (ρ' : (halfSamp S).Coins n) :
    accept (S.nmGame atk A q ℓ D β n) =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (A.Coins n)) fun r =>
      expect (sample (D.Coins n)) fun rD =>
        expect (simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n
            (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
            ((halfCoins S n).symm β) ρ' none)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q
            (pairFstD (S.gen.runAt n [] rg)) r) none)
          fun p => if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
            (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true
            then 1 else 0 := by
  rw [accept_eq, S.nmGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun rD => ?_)
  have h2 : (fun res : (Fin (ℓ * S.ctLen.eval n) → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (D.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) rD)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)
        (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, S.nmCodec_eq_bitCodec, h2]
  refine (expect_simulate_castImpl_toCompOn (snmDin_eval_inLens S n) (snmDout_eval_outLens S n)
    rfl (S.indImpl atk β n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))) A n q
    _ r none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)).symm.trans ?_
  have habs := simulate_eq_of_abs _ _ (Option.map Prod.fst)
    (fun i x s => castImpl_indImpl_abs S atk β n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) hist ρ' i x s)
    (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
      (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q
      (pairFstD (S.gen.runAt n [] rg)) r) none
  rw [Option.map_none] at habs
  rw [habs, expect_bind]
  simp only [expect_pure]

/-! ### The SIM adversary -/

open NMCCA2 (fwdHandler fwdHandler_finRun fwdHandler_finCall fwdHandler_advIn
  simulate_fwdHandler_impl fields_finInput polyTimeComputable_finFields finA)

/-- The SIM adversary's finalization round: output the adversary's output, `⟨[true], a⟩`. -/
private def copyFin (w : List Bool) : List Bool := pairEncode [true] (finA w)

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_copyFin : PolyTimeComputable copyFin :=
  (polyTimeComputable_const [true]).pairEncode polyTimeComputable_finFields.2.2.2.1

/-- The adversary's input is the reduction input. -/
private theorem polyTimeComputable_copyAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairSndD ctx) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The SIM adversary's handler** (on the real experiment's oracles with parameter length `pl`
and history length `hl`): it forwards every query (`NMCCA2.fwdHandler`), runs the adversary on the
reduction input, asks nothing in finalization, and outputs the adversary's `outLen(n)`-bit
output. -/
def copyHandler (pl hl outLen : PolyExpr) :
    InteractiveHandler 2 (snmDin S pl) (snmDout S hl) 2 (snmDin S pl) (snmDout S hl) :=
  fwdHandler (snmDin S pl) (snmDout S hl) (.const 0) (fun ctx => pairFstD (pairSndD ctx))
    polyTimeComputable_copyAdvIn outLen (.const 0) copyFin polyTimeComputable_copyFin

/-- The adversary runs on the reduction input: `(copyHandler S pl hl outLen).advInput n z ω = z`. -/
theorem copyHandler_advInput (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) :
    (copyHandler S pl hl outLen).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [copyHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The SIM adversary outputs `outLen(n)` bits: `(copyHandler S pl hl outLen).outLen = outLen`. -/
theorem copyHandler_outLen (pl hl outLen : PolyExpr) :
    (copyHandler S pl hl outLen).outLen = outLen := by
  rw [copyHandler, NMCCA2.fwdHandler_outLen]

/-- **The handler forwards** (`simulate_fwdHandler_impl`). -/
theorem simulate_copyHandler_impl (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
    (s : Fin ((copyHandler S pl hl outLen).stateLen.eval n) → Bool) :
    simulate ((copyHandler S pl hl outLen).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (snmDin S pl) (snmDout S hl) (.const 0) _ polyTimeComputable_copyAdvIn
    outLen (.const 0) copyFin polyTimeComputable_copyFin n z ω c s

/-- **The finalization outputs the adversary's output** (of `outLen(n)` bits), asking nothing:
`H.finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem copyHandler_finish (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
    (s : Fin ((copyHandler S pl hl outLen).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (hd : d = outLen.eval n) :
    (copyHandler S pl hl outLen).finish n z ω s a =
      .pure (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) := by
  have hfin : (copyHandler S pl hl outLen).finRun = copyFin := by
    funext w
    rw [copyHandler, fwdHandler_finRun]
  have hfc : (copyHandler S pl hl outLen).finCall = .const 0 := by
    rw [copyHandler, fwdHandler_finCall]
  have hol := copyHandler_outLen S pl hl outLen
  rw [InteractiveHandler.finish_eq, hfc, PolyExpr.eval_const]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ ((copyHandler S pl hl outLen).finRun _) = _
  rw [hfin, copyFin, (fields_finInput _ _ _ _ _ _).2.2.2.1]
  have hw : List.ofFn (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) =
      List.ofFn a := GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hol, hd])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-- **The SIM adversary's run is the adversary's run.** Let `B` be T2's machine for
`copyHandler S pl hl outLen` (coin bijection `φ`). Against any oracle `O` and from any state `s₀`,
`B`'s run on `pk` with coins `φ (ω, r)` is `A`'s run on `pk` with coins `r`, its output read at
`outLen(n)` bits. -/
theorem simulate_copyHandler_machine (A B : NUPPT) (q dα pl hl outLen : PolyExpr) (n : ℕ)
    (hd : dα.eval n = outLen.eval n)
    (φ : (Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((copyHandler S pl hl outLen).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (dα.eval n)) n (q.eval n) ((copyHandler S pl hl outLen).advInput n z ω) r)
          ((copyHandler S pl hl outLen).init n)).bind
          (fun res => (copyHandler S pl hl outLen).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n) (fun j => (snmDout S hl j).eval n)
          ((copyHandler S pl hl outLen).outLen.eval n)) n
          (q.eval n * (copyHandler S pl hl outLen).perCall.eval n +
            (copyHandler S pl hl outLen).finCall.eval n) z (φ (ω, r)))
    {σ : Type} (O : QueryImpl (bitSpecAt (snmDin S pl) (snmDout S hl) n) σ unifSpec) (s₀ : σ)
    (pk : List Bool) (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
    (r : A.Coins n) :
    simulate O (B.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n)
        (fun j => (snmDout S hl j).eval n) ((copyHandler S pl hl outLen).outLen.eval n)) n
        (q.eval n * (copyHandler S pl hl outLen).perCall.eval n +
          (copyHandler S pl hl outLen).finCall.eval n) pk (φ (ω, r))) s₀ =
      (simulate O (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n)
          (fun i => (snmDout S hl i).eval n) (dα.eval n)) n (q.eval n) pk r) s₀).bind fun p =>
        .pure (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn p.1), p.2) := by
  rw [← hφ, copyHandler_advInput, simulate_copyHandler_impl, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, copyHandler_finish S pl hl outLen n pk ω _ _ hd]
  rw [simulate_bind]
  simp only [simulate_pure]

/-! ### The distinguishers -/

/-- `z ↦ (g z).take msgLen(|1^n|)` for the parameter slot `1^n` of a machine input. -/
private theorem polyTimeComputable_takeMsg {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => (g z).take (S.msgLen.eval (NUPPT.inParam z).length) :=
  ((polyTimeComputable_pairTakePoly S.msgLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `z ↦ (g z).drop msgLen(|1^n|)` for the parameter slot `1^n` of a machine input. -/
private theorem polyTimeComputable_dropMsg {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => (g z).drop (S.msgLen.eval (NUPPT.inParam z).length) :=
  ((polyTimeComputable_pairDropPoly S.msgLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `D''`'s raw function: on the view `y`, whether its first two `msgLen(n)`-bit blocks differ. -/
private def halfFunD (z : List Bool) : List Bool :=
  [!decide ((NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length) =
    ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
      (S.msgLen.eval (NUPPT.inParam z).length))]

/-- `D''`'s raw function is polynomial-time. -/
private theorem polyTimeComputable_halfFunD : PolyTimeComputable (halfFunD S) :=
  polyTimeComputable_not ((polyTimeComputable_pairEq.comp
    ((polyTimeComputable_takeMsg S NUPPT.polyTimeComputable_inArg).pairEncode
      (polyTimeComputable_takeMsg S (polyTimeComputable_dropMsg S
        NUPPT.polyTimeComputable_inArg)))).congr fun z => by
          simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])

/-- **The distinguisher `D''`:** the uniform machine without coins accepting a view whose
parameter `⟨m₀, m₁⟩` (its first `2 · msgLen(n)` bits) has `m₀ ≠ m₁`. -/
noncomputable def halfDist : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_halfFunD S) (.const 0)

/-- `D''` accepts `y` iff its first two `msgLen(n)`-bit blocks differ:
`(halfDist S).distinguisherL n y ρ = !decide (y.take L = (y.drop L).take L)`. -/
theorem halfDist_distinguisherL (n : ℕ) (y : List Bool) (ρ : (halfDist S).Coins n) :
    (halfDist S).distinguisherL n y ρ =
      !decide (y.take (S.msgLen.eval n) = (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) := by
  have hrun : ∀ y r, (halfDist S).runAtL n y r =
      halfFunD S (pairEncode (pairEncode (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform (polyTimeComputable_halfFunD S) (.const 0) n y r
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hrun, halfFunD, NUPPT.inArg_eq, NUPPT.inParam_eq,
    NUPPT.advInput_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  cases decide (y.take (S.msgLen.eval n) = (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) <;>
    decide

/-- The tails of the entries: each `msgLen(n) + 2`-bit chunk without its first bit (the `COPY`
flag), on `⟨⟨1^n, []⟩, entries⟩`. -/
def entryTails : List Bool → List Bool :=
  chunkMap (S.msgLen.add (.const 2)) fun _ ch => ch.drop 1

/-- `entryTails S = chunkMap (msgLen + 2) (fun _ ch => ch.drop 1)`. -/
theorem entryTails_eq : entryTails S = chunkMap (S.msgLen.add (.const 2)) fun _ ch => ch.drop 1 :=
  rfl

/-- The tails of the entries are polynomial-time. -/
theorem polyTimeComputable_entryTails : PolyTimeComputable (entryTails S) :=
  polyTimeComputable_chunkMap _ (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

variable (D : NUPPT)

/-- `D'`'s raw function on `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with the view `y = a₀ ‖ a₁ ‖ m ‖ entries`
(`msgLen(n)` bits each for `a₀`, `a₁`, `m`): `0` if `a₀ = a₁`, and otherwise whether `D`'s verdict
(advice `α`, coins `ρ`) on the entries' tails equals `[m = a₁]`. -/
private def tailFun (z : List Bool) : List Bool :=
  if decide ((NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length) =
      ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
        (S.msgLen.eval (NUPPT.inParam z).length)) then [false]
  else [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (entryTails S (pairEncode (pairEncode (NUPPT.inParam z) [])
        ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
          (S.msgLen.eval (NUPPT.inParam z).length)).drop (S.msgLen.eval (NUPPT.inParam z).length))))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)) = [true]) ==
    decide ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
        (S.msgLen.eval (NUPPT.inParam z).length)).take (S.msgLen.eval (NUPPT.inParam z).length) =
      ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
        (S.msgLen.eval (NUPPT.inParam z).length))]

/-- `D'`'s raw function is polynomial-time. -/
private theorem polyTimeComputable_tailFun : PolyTimeComputable (tailFun S D) := by
  have hy := NUPPT.polyTimeComputable_inArg
  have hu := NUPPT.polyTimeComputable_inParam
  have hd1 := polyTimeComputable_dropMsg S hy
  have hd2 := polyTimeComputable_dropMsg S hd1
  have hd3 := polyTimeComputable_dropMsg S hd2
  have ha0 := polyTimeComputable_takeMsg S hy
  have ha1 := polyTimeComputable_takeMsg S hd1
  have hm := polyTimeComputable_takeMsg S hd2
  have heq : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
      PolyTimeComputable fun z => [decide (f z = g z)] := fun hf hg =>
    (polyTimeComputable_pairEq.comp (hf.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hconv : PolyTimeComputable fun z => entryTails S (pairEncode (pairEncode
      (NUPPT.inParam z) []) ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
        (S.msgLen.eval (NUPPT.inParam z).length)).drop (S.msgLen.eval (NUPPT.inParam z).length))) :=
    (polyTimeComputable_entryTails S).comp ((hu.pairEncode (polyTimeComputable_const [])).pairEncode
      hd3)
  have hv := heq (D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu hconv
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    (polyTimeComputable_const [true])
  have hw := heq hm ha1
  refine polyTimeComputable_ite (heq ha0 ha1) (polyTimeComputable_const [false]) ?_
  have key : ∀ v w : Bool, (if v = true then [w] else [!w]) = [v == w] := by decide
  exact (polyTimeComputable_ite hv hw (polyTimeComputable_not hw)).congr fun z => by
    rw [Function.comp_apply]
    exact key _ _

/-- **The distinguisher `D'`** built from `D`, with `D`'s coins and advice: on a view
`a₀ ‖ a₁ ‖ m ‖ entries` it outputs `0` if `a₀ = a₁`, and otherwise whether `D`'s verdict on the
entries' tails (the `COPY` flags dropped, so a copy reads as `⊥`) equals `[m = a₁]`. -/
noncomputable def tailDist : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_tailFun S D) D.coins D.adv D.advice D.advice_length

/-- `D'` has `D`'s coins. -/
theorem tailDist_coins : (tailDist S D).coins = D.coins := rfl

/-- **`D'`'s verdict** on a view `y`, with `D`'s coins `rD` carried over: with `L = msgLen(n)`,
`0` if `y`'s first two `L`-bit blocks are equal, and otherwise `[D(entryTails (y.drop 3L)) =
[true]] == [third block = second block]`. -/
theorem tailDist_distinguisherL (n : ℕ) (y : List Bool) (rD : D.Coins n) :
    (tailDist S D).distinguisherL n y (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) =
      if decide (y.take (S.msgLen.eval n) =
          (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) then false
      else (D.distinguisherL n (entryTails S (pairEncode (pairEncode (List.replicate n true) [])
          (((y.drop (S.msgLen.eval n)).drop (S.msgLen.eval n)).drop (S.msgLen.eval n)))) rD ==
        decide (((y.drop (S.msgLen.eval n)).drop (S.msgLen.eval n)).take (S.msgLen.eval n) =
          (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n))) := by
  have hlay : pairEncode (pairEncode (NUPPT.advInput n y) (D.advice n)) (List.ofFn rD) =
      NUPPT.layout (List.replicate n true) y (D.advice n) (List.ofFn rD) := by
    rw [NUPPT.layout_eq, NUPPT.advInput_eq]
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_coinsCongr, tailDist, NUPPT.runAtL_ofPolyTime, tailFun,
    hlay]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout, List.length_replicate]
  rw [← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]
  split
  · rfl
  · generalize D.distinguisherL n _ rD = v
    cases v <;> simp

/-! ### The distinguishers on the views -/

/-- The four blocks of a view `A ‖ M ‖ E` with `|A| = 2L`, `|M| = L`. -/
private theorem blocks_append (L : ℕ) (A M E : List Bool) (hA : A.length = L + L)
    (hM : M.length = L) :
    (A ++ M ++ E).take L = A.take L ∧ ((A ++ M ++ E).drop L).take L = A.drop L ∧
      (((A ++ M ++ E).drop L).drop L).take L = M ∧ (((A ++ M ++ E).drop L).drop L).drop L = E := by
  have hd : (A.drop L).length = L := by rw [List.length_drop]; omega
  rw [List.append_assoc]
  refine ⟨List.take_append_of_le_length (by omega), ?_, ?_, ?_⟩
  · rw [List.drop_append_of_le_length (by omega), List.take_left' hd]
  · rw [List.drop_append_of_le_length (by omega), List.drop_left' hd, List.take_left' hM]
  · rw [List.drop_append_of_le_length (by omega), List.drop_left' hd, List.drop_left' hM]

/-- **`D'` on a view `A ‖ M ‖ E`** (`|A| = 2·msgLen(n)`, `|M| = msgLen(n)`): `0` if the halves of
`A` are equal, and otherwise `[D(entryTails E) = 1] == [M = second half of A]`. -/
theorem tailDist_blocks (n : ℕ) (A M E : List Bool)
    (hA : A.length = S.msgLen.eval n + S.msgLen.eval n) (hM : M.length = S.msgLen.eval n)
    (rD : D.Coins n) :
    (tailDist S D).distinguisherL n (A ++ M ++ E)
        (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) =
      if decide (A.take (S.msgLen.eval n) = A.drop (S.msgLen.eval n)) then false
      else (D.distinguisherL n (entryTails S (pairEncode (pairEncode (List.replicate n true) [])
        E)) rD == decide (M = A.drop (S.msgLen.eval n))) := by
  obtain ⟨h1, h2, h3, h4⟩ := blocks_append _ A M E hA hM
  rw [tailDist_distinguisherL, h1, h2, h3, h4]

/-- **`D''` on a view `A ‖ M ‖ E`:** whether the halves of `A` differ. -/
theorem halfDist_blocks (n : ℕ) (A M E : List Bool)
    (hA : A.length = S.msgLen.eval n + S.msgLen.eval n) (hM : M.length = S.msgLen.eval n)
    (ρ : (halfDist S).Coins n) :
    (halfDist S).distinguisherL n (A ++ M ++ E) ρ =
      !decide (A.take (S.msgLen.eval n) = A.drop (S.msgLen.eval n)) := by
  obtain ⟨h1, h2, -, -⟩ := blocks_append _ A M E hA hM
  rw [halfDist_distinguisherL, h1, h2]

/-- An entry without its `COPY` flag: `⊥ = 0` for a copy, `Dec`'s answer otherwise. -/
theorem entryL_drop_one (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    (entryL S n sk copy c).drop 1 =
      if copy then List.replicate (S.msgLen.eval n + 1) false
      else List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c)))) := by
  rw [entryL_eq]
  cases copy <;> rfl

/-- **The entries' tails are the decrypted entries** (`chunkMap_flatten`; every entry has
`msgLen(n) + 2` bits). -/
theorem entryTails_entries (n : ℕ) (sk : List Bool) (es : List (Bool × List Bool)) :
    entryTails S (pairEncode (pairEncode (List.replicate n true) [])
        (es.map fun e => entryL S n sk e.1 e.2).flatten) =
      (es.map fun e => (entryL S n sk e.1 e.2).drop 1).flatten := by
  have hlen : (S.msgLen.add (.const 2)).eval n = S.msgLen.eval n + 2 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  rw [entryTails_eq, chunkMap_flatten _ _ n [] _ (fun ch hch => ?_) (by rw [hlen]; omega),
    List.map_map]
  · rfl
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hch
    rw [hlen, entryL_eq]
    cases e.1 <;> simp

/-- **The experiment's output is the entries' tails:** for an output string `w` of `ℓ` ciphertexts,
`nmOutput sk s' w` is the concatenation of the tails of the entries `entryL … [ciphertext i is
the challenge] (ciphertext i)`. -/
theorem nmOutput_eq_entryTails (n ℓ : ℕ) (sk : List Bool) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (w : List Bool) (hw : w.length = ℓ * S.ctLen.eval n) :
    S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) w) =
      ((List.range ℓ).map fun i => (entryL S n sk
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
        (chunkAt (S.ctLen.eval n) i w)).drop 1).flatten := by
  rw [S.nmOutput_eq]
  congr 1
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range, entryL_drop_one, S.nmDecrypt_eq]
  have hc : List.ofFn (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
      rw [List.length_ofFn] at h₁; exact h₁⟩) = chunkAt (S.ctLen.eval n) i w := by
    rw [S.ofFn_nthCt, GGMRed.ofFn_padFin_of_length hw, chunkAt_eq]
  have hcopy : (s' = some (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
      rw [List.length_ofFn] at h₁; exact h₁⟩)) ↔
      s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w) := by
    rw [← hc]
    cases s' with
    | none => simp
    | some c => simp [List.ofFn_inj]
  by_cases h : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)
  · rw [if_pos (hcopy.2 h), decide_eq_true h, if_pos rfl, ofFn_zeroBits]
  · rw [if_neg (fun h' => h (hcopy.1 h')), decide_eq_false h, if_neg Bool.false_ne_true, hc]

/-! ### The real experiment against `NM_0`, `NM_1` -/

/-- `D'`'s indicator on a view with parameter `A` and message `m_β`, as a function of `D`'s verdict
`t`: `[m₀ ≠ m₁] · [t = β]`. -/
private theorem tail_indicator (A : List Bool) (L : ℕ) (t β : Bool) :
    (if (if decide (A.take L = A.drop L) then false
      else (t == decide ((if β then A.drop L else A.take L) = A.drop L))) = true then (1 : ℝ)
      else 0) =
      if A.take L ≠ A.drop L then (if β then (if t then 1 else 0) else 1 - (if t then 1 else 0))
      else 0 := by
  by_cases hb : A.take L = A.drop L
  · simp [hb]
  · cases β <;> cases t <;> simp [hb]

/-- `D''`'s indicator on a view with parameter `A`: `[m₀ ≠ m₁]`. -/
private theorem half_indicator (A : List Bool) (L : ℕ) :
    (if (!decide (A.take L = A.drop L)) = true then (1 : ℝ) else 0) =
      if A.take L ≠ A.drop L then 1 else 0 := by
  by_cases hb : A.take L = A.drop L <;> simp [hb]

section RealIdentity

variable (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (n : ℕ) (hist : List Bool → List Bool)
  (pk sk : List Bool) (r : A.Coins n) (ρ' : (halfSamp S).Coins n)

/-- **The run of `A` against the hybrid oracle with the sampler's coin `β`** (the real experiment of
the SIM adversary, and `NM_β`): `simulate (rImpl … false … (coin β) ρ' none) (A's run) none`. -/
noncomputable abbrev runB (β : Bool) :
    ProbComp ((Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) :=
  simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
      ((halfCoins S n).symm β) ρ' none)
    (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
      (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q pk r) none

/-- `runB … β = simulate (rImpl … false … (coin β) ρ' none) (A.toCompOn … n q pk r) none`. -/
theorem runB_eq (β : Bool) :
    runB S atk A q ℓ n hist pk sk r ρ' β =
      simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
          ((halfCoins S n).symm β) ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
          (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q pk r) none := rfl

/-- The bad event of the coupling: the recorded parameter `⟨m₀, m₁⟩` has `m₀ ≠ m₁` (never for the
empty state, whose parameter reads `0`). -/
private def badHalves (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
    (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) : Prop :=
  (List.ofFn ((s.map Prod.snd).getD (zeroBits _))).take (S.msgLen.eval n) ≠
    (List.ofFn ((s.map Prod.snd).getD (zeroBits _))).drop (S.msgLen.eval n)

private instance : DecidablePred (badHalves S n) := fun _ => instDecidableNot

/-- **The coupling of the two coins:** `𝔼[G · 1_{m₀ = m₁}]` is the same with the sampler's coin
`0` and `1` (`expect_eq_until_bad`): the oracles agree while the recorded parameter has equal
halves, and a bad parameter stays recorded. -/
private theorem expect_runB_good (G : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) → ℝ) :
    expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else G p) =
      expect (runB S atk A q ℓ n hist pk sk r ρ' true)
        (fun p => if badHalves S n p.2 then 0 else G p) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hh : ∀ {ℓ' : ℕ} (m : Fin ℓ' → Bool),
      List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
  have hnone : ¬ badHalves S n none := by
    unfold badHalves
    intro h
    apply h
    rw [Option.map_none, Option.getD_none, ofFn_zeroBits, hpl, List.take_replicate,
      List.drop_replicate]
    congr 1
    omega
  have hkeep : ∀ (β : Bool) i x y a,
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x (some (y, a))).AllOutputs
        fun ys => ys.2 = some (y, a) := by
    intro β i x y a
    match i with
    | 0 =>
      rw [rImpl_dec]
      split <;> exact OracleComp.allOutputs_pure.2 rfl
    | 1 => exact OracleComp.allOutputs_pure.2 rfl
  have hstick : ∀ (β : Bool) i x s, badHalves S n s →
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x s).AllOutputs fun ys => badHalves S n ys.2 := by
    intro β i x s hs
    cases s with
    | none => exact absurd hs hnone
    | some ya => exact (hkeep β i x ya.1 ya.2).mono fun ys h => h ▸ hs
  refine expect_eq_until_bad (badHalves S n) (fun i x s hs g => ?_) (hstick false) (hstick true) _
    G hnone
  match i, s with
  | 0, s => rw [rImpl_dec, rImpl_dec]
  | 1, some (y, a) => rw [rImpl_some, rImpl_some, hh, hh]
  | 1, none =>
    rw [rImpl_none_lazy, rImpl_none_lazy, expect_bind, expect_bind]
    refine congrArg _ (funext fun re => ?_)
    rw [rImpl_none_eager, rImpl_none_eager, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      expect_pure, expect_pure]
    by_cases hb : badHalves S n (some (default, padFin ((S.msgLen.add S.msgLen).eval n)
      (List.ofFn x)))
    · have hb' : ∀ y, badHalves S n (some (y, padFin ((S.msgLen.add S.msgLen).eval n)
          (List.ofFn x))) := fun y => hb
      dsimp only
      rw [if_pos (hb' _), if_pos (hb' _)]
    · have heq : drawWith (halfSamp S) (S.msgLen.eval n) n (padFin ((S.msgLen.add S.msgLen).eval n)
          (List.ofFn x)) ((halfCoins S n).symm false) = drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) ((halfCoins S n).symm true) := by
        apply List.ofFn_injective
        rw [ofFn_drawWith_half S n _ hpl, ofFn_drawWith_half S n _ hpl, if_neg Bool.false_ne_true,
          if_pos rfl]
        simpa [badHalves] using hb
      rw [heq]

/-- **The real identity** at fixed keys and coins: for the views of the SIM adversary's real
experiment with coin `β`, `2 · avg_β 𝔼[D'] − avg_β 𝔼[D''] = 𝔼_1[D(NM)] − 𝔼_0[D(NM)]`, where the
last two are `NM_1` and `NM_0`.

**Proof sketch.** On the views, `D'` is `[m₀ ≠ m₁] · [D(NM) = β]` and `D''` is `[m₀ ≠ m₁]`
(`tailDist_blocks`, `halfDist_blocks`, `ofFn_drawWith_half`, `entryTails_entries`,
`nmOutput_eq_entryTails`). By the coupling (`expect_runB_good`) the good parts of `D(NM)` and of `1`
have the same expectation under both coins; the identity is then linear algebra. -/
theorem real_identity (D : NUPPT) (rD : D.Coins n) (ρ'' : (halfDist S).Coins n) :
    (expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
        if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
          ((halfCoins S n).symm false) (List.ofFn p.1) p.2)
          (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then 1 else 0) +
      expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
        if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
          ((halfCoins S n).symm true) (List.ofFn p.1) p.2)
          (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then 1 else 0)) -
      (expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
          if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
            ((halfCoins S n).symm false) (List.ofFn p.1) p.2) ρ'' = true then 1 else 0) +
        expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
          if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
            ((halfCoins S n).symm true) (List.ofFn p.1) p.2) ρ'' = true then 1 else 0)) / 2 =
      expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
        if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
          (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0) -
      expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
        if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
          (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  set v : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) →
      ℝ := fun p => if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
        (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0 with hv
  -- The views, block by block.
  have hview : ∀ (β : Bool) (p : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))),
      ((if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm β) (List.ofFn p.1) p.2)
        (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then (1 : ℝ) else 0) =
        if badHalves S n p.2 then (if β then v p else 1 - v p) else 0) ∧
      ((if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm β) (List.ofFn p.1) p.2) ρ'' = true then (1 : ℝ) else 0) =
        if badHalves S n p.2 then 1 else 0) := by
    intro β p
    have hw : (List.ofFn p.1).drop (ℓ * S.ctLen.eval n) = [] := by
      rw [List.drop_eq_nil_iff, List.length_ofFn]
    have hA : (List.ofFn ((p.2.map Prod.snd).getD (zeroBits _))).length =
        S.msgLen.eval n + S.msgLen.eval n := by rw [List.length_ofFn, hpl]
    have hM : (List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n
        ((p.2.map Prod.snd).getD (zeroBits _)) ((halfCoins S n).symm β))).length =
        S.msgLen.eval n := List.length_ofFn
    have hes : ((List.range ℓ).map fun i => entryL S n sk
        (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
        (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))) =
        (((List.range ℓ).map fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))).map
          fun e : Bool × List Bool => entryL S n sk e.1 e.2) := by
      rw [List.map_map]
      rfl
    rw [realView_eq, hw, List.append_nil, tailDist_blocks S D n _ _ _ hA hM,
      halfDist_blocks S n _ _ _ hA hM, ofFn_drawWith_half S n _ hpl, hes, entryTails_entries,
      List.map_map]
    have hnm : ((List.range ℓ).map ((fun e : Bool × List Bool => (entryL S n sk e.1 e.2).drop 1) ∘
        fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1)))).flatten =
        S.nmOutput sk (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1)) := by
      rw [nmOutput_eq_entryTails S n ℓ sk _ _ List.length_ofFn, Option.map_map]
      rfl
    rw [hnm]
    exact ⟨tail_indicator _ _ _ _, half_indicator _ _⟩
  -- The coupling, for `D(NM)` and for `1`.
  have hgv := expect_runB_good S atk A q ℓ n hist pk sk r ρ' v
  have hg1 := expect_runB_good S atk A q ℓ n hist pk sk r ρ' (fun _ => 1)
  have hsplit : ∀ (β : Bool) (f : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) →
      ℝ), expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then f p
        else 0) = expect (runB S atk A q ℓ n hist pk sk r ρ' β) f -
          expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then 0
            else f p) := by
    intro β f
    rw [← expect_sub]
    refine congrArg _ (funext fun p => ?_)
    split <;> ring
  simp only [fun β p => (hview β p).1, fun β p => (hview β p).2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hsub0 : expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p => 1 - v p) =
      1 - expect (runB S atk A q ℓ n hist pk sk r ρ' false) v := by
    rw [expect_sub, expect_const]
  have hsub0' : expect (runB S atk A q ℓ n hist pk sk r ρ' false)
      (fun p => if badHalves S n p.2 then 0 else 1 - v p) =
      expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else 1) -
      expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else v p) := by
    rw [← expect_sub]
    refine congrArg _ (funext fun p => ?_)
    split <;> ring
  rw [hsplit false (fun p => 1 - v p), hsplit true v, hsplit false (fun _ => 1),
    hsplit true (fun _ => 1), hsub0, hsub0', expect_const, expect_const, hgv, hg1]
  ring

end RealIdentity

/-- The ideal identity on an abstract parameter `A` and verdict `t`. -/
private theorem ideal_key (A : List Bool) (L : ℕ) (t : Bool) :
    ((if (if decide (A.take L = A.drop L) then false
        else (t == decide ((if false = true then A.drop L else A.take L) = A.drop L))) = true
        then (1 : ℝ) else 0) +
      if (if decide (A.take L = A.drop L) then false
        else (t == decide ((if true = true then A.drop L else A.take L) = A.drop L))) = true
        then 1 else 0) =
      if (!decide (A.take L = A.drop L)) = true then 1 else 0 := by
  by_cases hb : A.take L = A.drop L
  · simp [hb]
  · cases t <;> simp [hb]

/-- **The ideal identity, pointwise:** on the ideal experiment's views with the two coins, `D'`
accepts with indicator sum equal to `D''`'s (whatever the simulator's output and state): when
`m₀ ≠ m₁`, exactly one coin makes `[D(…) = 1] == [m = m₁]` hold, since `m = m_β`. -/
theorem ideal_identity (n ℓ : ℕ) (sk : List Bool) (w : List Bool)
    (sa : Option (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) (rD : D.Coins n)
    (ρ'' : (halfDist S).Coins n) (hw : w.length = ℓ * (S.ctLen.eval n + 1)) :
    ((if (tailDist S D).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm false) w sa) (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true
        then 1 else 0 : ℝ) +
      if (tailDist S D).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm true) w sa) (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true
        then 1 else 0) =
      if (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm false) w sa) ρ'' = true then 1 else 0 := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hA : (List.ofFn (sa.getD (zeroBits _))).length = S.msgLen.eval n + S.msgLen.eval n := by
    rw [List.length_ofFn, hpl]
  have hM : ∀ β, (List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n (sa.getD (zeroBits _))
      ((halfCoins S n).symm β))).length = S.msgLen.eval n := fun _ => List.length_ofFn
  have hdrop : w.drop (ℓ * (S.ctLen.eval n + 1)) = [] := by rw [List.drop_eq_nil_iff, hw]
  rw [idealView_eq, idealView_eq, hdrop, List.append_nil, List.append_nil,
    tailDist_blocks S D n _ _ _ hA (hM false), tailDist_blocks S D n _ _ _ hA (hM true),
    halfDist_blocks S n _ _ _ hA (hM false), ofFn_drawWith_half S n _ hpl,
    ofFn_drawWith_half S n _ hpl]
  exact ideal_key _ _ _

end TCSlib.Cryptography.Composability.NMSim
