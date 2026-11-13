/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-malleability implies SIM-NME′ under CPA: the NM games are the hybrids

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message). For the NM
adversary `B` (T2's machine of `nmParams`, with `M`'s advice hard-wired) and the distinguisher
`recDist S pl r X`, the experiment `NM_b` accepts with the probability of the hybrid `H_b`
(`hybAcc … b …`) whenever `msgLen(n) > 0` (`exists_nmAdversary`). With `H_false` the real
experiment and `H_true` the ideal one (`Simulator.lean`), the SIM advantage is `B`'s NM advantage.

## Main definitions

None: this module only proves results. `B`'s handler parameters `nmParams` and the distinguisher
`recDist` are defined in `Reduction.lean` and `Recover.lean`.

## Main results

* `NMSim.recView_nmOut`: the view read back from `B`'s NM output is the hybrid's view.
* `NMSim.nmRun_eq`: one run of `NM_b` is one run of `H_b`.
* `NMSim.exists_nmAdversary`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme) (samp : NUPPT) (pl hl : PolyExpr)
  (hist : List Bool → List Bool) (hist_poly : PolyTimeComputable hist) (r sl : PolyExpr)

/-! ### The view -/

section View

variable (n : ℕ)

/-- **The NM adversary's recorded parameter** is the hybrid's: `stParam` of the abstracted state is
`⟦a⟧` for the challenge on `a`, and `0^{pl}` without a challenge. -/
theorem stParam_nmAbs (ρ ρ' : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1) =
      List.ofFn ((s.map Prod.snd).getD (zeroBits _)) := by
  have hs : ((PolyExpr.const 1).add (S.ctLen.add hl)).eval n =
      1 + (S.ctLen.eval n + hl.eval n) := by
    rw [PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_const]
  cases s with
  | none =>
    rw [nmAbs_none, ofFn_chalState_none, stParam_eq, List.drop_replicate, chalHandler_stateLen_eval,
      hs, Option.map_none, Option.getD_none, ofFn_zeroBits]
    congr 1
    omega
  | some ya =>
    obtain ⟨y, a⟩ := ya
    rw [nmAbs_some, ofFn_chalState_some, stParam_eq, hs, Option.map_some, Option.getD_some,
      Nat.add_comm 1, List.drop_succ_cons,
      List.drop_left' (by rw [List.length_append, List.length_ofFn, List.length_ofFn])]

/-- **The NM adversary's copy flags are the hybrid's copy test:** for the abstracted state `st` and
every string `c`, `[flag ∧ c = y] = [c is the hybrid's recorded challenge]`. -/
theorem flag_nmAbs (ρ ρ' : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (c : List Bool) :
    ((List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1).headD false &&
      decide (c = ((List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1).drop 1).take
        (S.ctLen.eval n))) = decide ((s.map Prod.fst).map List.ofFn = some c) := by
  cases s with
  | none =>
    rw [nmAbs_none, headD_ofFn_chalState]
    simp
  | some ya =>
    obtain ⟨y, a⟩ := ya
    rw [nmAbs_some, ofFn_chalState_some, List.headD_cons, List.drop_one, List.tail_cons,
      List.append_assoc, List.take_left' List.length_ofFn]
    simp only [Bool.true_and, Option.map_some, Option.some.injEq, decide_eq_decide]
    exact eq_comm

/-- **The view read back from the NM adversary's output is the hybrid's view** (under generated
keys, `msgLen(n) > 0`): for the hybrid's final state `s` and `A`'s output `a`, `recView` of the
decryptions of `B`'s output (on the abstracted state, the input `⟨pk, M.advice n⟩` and the seed
`ρ ‖ ρ̃ ‖ re`) is `realView` of `a` and `s`.

**Proof sketch.** `recView_nmOutL`, with the copy flags `flag_nmAbs`, the parameter `stParam_nmAbs`
and the message `M(a; ρ)` read from the seed (`nmSeed_ofFn`). -/
theorem recView_nmOut (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n) (ρ ρ' : samp.Coins n)
    (re : S.enc.Coins n) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)))
    (a : List Bool) (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    recView S pl r (List.replicate n true) (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
        ((nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).2.map Prod.fst)
        (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (List.ofFn (padFin
          ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).outLen.eval n)
          (nmOutL S samp r n (pairEncode (List.replicate n true)
            (pairEncode (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
              (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
                (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1)))) a
            (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))
            (finMsg S samp n
              (pairSndD (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n)))
              (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
              (stParam S hl n
                (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1)))))))) =
      realView S samp pl n (r.eval n) (pairSndD (S.gen.runAt n [] rg)) ρ a s := by
  have hω := nmSeed_ofFn S samp pl hl hist hist_poly r sl n ρ ρ' re
  have haP :
      (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1)).length =
      pl.eval n := by
    rw [stParam_nmAbs, List.length_ofFn]
  have hmP : (finMsg S samp n
      (pairSndD (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n)))
      (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
      (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))).length =
      S.msgLen.eval n := by
    rw [finMsg_eq, EnsembleLemmas.length_padL]
  have hlen := length_nmOutL S samp pl r sl n
    (pairEncode (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
      (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
        (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))) a _ _ ha haP hmP
  rw [← nmParams_outLen_eval S samp pl hl hist hist_poly r sl n] at hlen
  rw [ofFn_padFin_of_length hlen, nmAbs_snd_fst,
    recView_nmOutL S pl r sl samp n rg hL (s.map Prod.fst) _ _ _ a _ _
      (pairFstD_pairEncode _ _) re
      (by rw [hω, PolyExpr.eval_add, ← List.append_assoc, List.drop_left' (by
        rw [List.length_append, length_ofFn_coins, length_ofFn_coins])]) ha haP hmP
      (flag_nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s),
    realView_eq, stParam_nmAbs, finMsg_eq, pairSndD_pairEncode, hω,
    List.take_left' (length_ofFn_coins samp n ρ), drawWith_eq, ofFn_padFin_eq_padL,
    samp.runAt_eq, samp.runAtL_eq_output_layout]

end View

/-! ### `NM_b` is the hybrid `H_b` -/

section Games

variable (A : NUPPT) (q : PolyExpr)

/-- **One run of `NM_b` is one run of the hybrid `H_b`** (under generated keys, `msgLen(n) > 0`):
let `B₀` be T2's machine of the NM adversary's handler (coin bijection `φ`). For the input
`⟨pk, M.advice n⟩` and coins `φ (ρ ‖ ρ̃ ‖ re, rA)`, the law of `recDist X`'s verdict over `B₀`'s run
against `NM_b`'s oracles is the law of `X`'s verdict on `realView` over `A`'s run (coins `rA`)
against `rImpl … b … ρ ρ̃ none`.

**Proof sketch.** Transport the output length (`expect_toCompOn_outLen`); T2's equation; the
finalization asks nothing (`nmFinish`); the composition of the two simulations is the hybrid's
run through the abstraction (`simulate_comp`, `simulate_eq_of_abs`, `nmComp_abs`); the views agree
(`recDist_distinguisherL`, `recView_nmOut`). -/
theorem nmRun_eq (B₀ : NUPPT) (n : ℕ)
    (φ : (Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool) ×
      A.Coins n ≃ B₀.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool)
      (rA : A.Coins n),
      (simulate ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (((r.mul S.ctLen).add sl).eval n)) n (q.eval n)
            ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).advInput n z ω) rA)
          ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).init n)).bind
          (fun res => (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finish n z ω
            res.2 res.1) =
        B₀.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n)
          ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).outLen.eval n)) n
          (q.eval n * (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall.eval n +
            (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall.eval n) z (φ (ω, rA)))
    (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n)
    (rA : A.Coins n) (b : Bool) (ρ'' : (halfSamp S).Coins n) (X : NUPPT) (rX : X.Coins n) :
    ProbComp.expect (simulate (rImpl S .cpa false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0)
          (fun _ => []) n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
          ((halfCoins S n).symm b) ρ'' none)
        (B₀.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n) ((nmLen S pl r sl).eval n * S.ctLen.eval n)) n
          (q.eval n * (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall.eval n +
            (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall.eval n)
          (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
          (φ (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re, rA))) none)
        (fun p => if (recDist S pl r X).distinguisherL n
          (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
          (p.2.map Prod.fst) (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (List.ofFn p.1)))
          (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0) =
      ProbComp.expect (simulate (rImpl S .cpa b samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) ρ ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r.eval n * S.ctLen.eval n + sl.eval n)) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) rA)
          none)
        (fun p => if X.distinguisherL n (realView S samp pl n (r.eval n)
          (pairSndD (S.gen.runAt n [] rg)) ρ (List.ofFn p.1) p.2) rX = true then 1 else 0) := by
  have hct := ctLen_pos S n rg re hL
  have hdα : ((r.mul S.ctLen).add sl).eval n = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hfin : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool)
      (st : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).stateLen.eval n) → Bool)
      (a : Fin (((r.mul S.ctLen).add sl).eval n) → Bool),
      (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finish n z ω st a =
        .pure (padFin _ (nmOutL S samp r n (pairEncode (List.replicate n true)
          (pairEncode z (pairEncode (List.ofFn ω) (List.ofFn st)))) (List.ofFn a)
          (stParam S hl n (List.ofFn st)) (finMsg S samp n (pairSndD z) (List.ofFn ω)
            (stParam S hl n (List.ofFn st))))) :=
    fun z ω st a => nmFinish S samp pl hl hist hist_poly r sl n z ω st a hdα hct
  refine (expect_toCompOn_outLen _ B₀ n _ _ _ none
    (nmParams_outLen_eval S samp pl hl hist hist_poly r sl n).symm
    (fun p => if (recDist S pl r X).distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
      (p.2.map Prod.fst) (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) p.1))
      (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0)).trans ?_
  rw [← hφ, nmParams_advInput, chalHandler_init, simulate_bind, simulate_comp,
    ← nmAbs_none S samp pl hl hist hist_poly r sl n ρ ρ',
    Games.simulate_eq_of_abs _ _ _
      (nmComp_abs S samp pl hl hist hist_poly r sl n _ _ ρ ρ' re b ρ''),
    OracleComp.bind_assoc, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, hfin, simulate_pure]
  rw [ProbComp.expect_bind]
  simp only [ProbComp.expect_pure]
  refine (expect_toCompOn_outLen _ A n (q.eval n) _ rA none hdα fun p =>
    if (recDist S pl r X).distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
      ((nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).2.map Prod.fst)
      (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (List.ofFn (padFin _ (nmOutL S samp r n
        (pairEncode (List.replicate n true)
          (pairEncode (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
            (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
              (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).1)))) p.1
        (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).1))
        (finMsg S samp n (pairSndD (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n)))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
          (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).1))))))))
      (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0).trans ?_
  refine congrArg _ (funext fun p => ?_)
  rw [recDist_distinguisherL, recView_nmOut S samp pl hl hist hist_poly r sl n rg hL ρ ρ' re p.2 _
    (by rw [List.length_ofFn])]

include hist_poly in
/-- **The NM adversary exists:** for the sampler `samp` (parameter length `pl`, history `hist` of
length `hl`), the adversary `A` and the polynomials `q`, `r`, `sl`, there are a machine `B` and a
budget `qB` such that for every distinguisher `X`, every `n` with `msgLen(n) > 0` and every `b`,
`NM_b(B, recDist X)` (budget `qB`, `nmLen` ciphertexts, under CPA) accepts with the probability of
the hybrid `H_b`.

**Proof sketch.** `B₀` is T2's machine of the NM adversary's handler and `B` hard-wires
`M.advice n` (`exists_withAdviceOn`). Reindex `B`'s coins as `(ρ ‖ ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`,
`seedEquivPoly`, `seedEquiv`, `expect_sample_prod`) and the distinguisher's as `X`'s; pointwise
this is
`nmRun_eq`, which does not read `re` (`expect_const`). -/
theorem exists_nmAdversary : ∃ (B : NUPPT) (qB : PolyExpr), ∀ (X : NUPPT) (n : ℕ) (b : Bool),
    0 < S.msgLen.eval n →
      accept (S.nmGame .cpa B (qB.eval n) ((nmLen S pl r sl).eval n) (recDist S pl r X) b n) =
        hybAcc S .cpa b samp pl hl hist A (q.eval n) (r.eval n) (sl.eval n) X n := by
  obtain ⟨B₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
    (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) ((r.mul S.ctLen).add sl)
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl))
  obtain ⟨B, hc, hB⟩ := NMCCA2.exists_withAdviceOn B₀ samp.advice samp.adv samp.advice_length
  refine ⟨B, (q.mul (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall).add
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall, fun X n b hL => ?_⟩
  obtain ⟨φ, hφ⟩ := hT2 n
  have hK : ((q.mul (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall).add
      (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall).eval n =
      q.eval n * (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall.eval n +
        (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  rw [accept_nmGame_eq_rImpl S .cpa B _ _ (recDist S pl r X) b n (fun _ => [])
    ((halfCoins S n).symm false), hybAcc_eq, hK]
  refine congrArg _ (funext fun rg => ?_)
  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr hc n)]
  simp only [hB]
  rw [← ProbComp.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
    ← ProbComp.expect_sample_equiv
      (seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ => ?_)
  rw [← ProbComp.expect_sample_equiv (seedEquiv (A := samp) (B := S.enc) rfl n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ' => ?_)
  refine Eq.trans ?_ (ProbComp.expect_const (ProbComp.sample (S.enc.Coins n)) _)
  refine congrArg _ (funext fun re => congrArg _ (funext fun rA => ?_))
  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr (recDist_coins S pl r X).symm n)]
  refine congrArg _ (funext fun rX => ?_)
  rw [← nmSeed_eq]
  exact nmRun_eq S samp pl hl hist hist_poly r sl A q B₀ n φ hφ rg hL ρ ρ' re rA b _ X rX

end Games

end TCSlib.Cryptography.Composability.NMSim
