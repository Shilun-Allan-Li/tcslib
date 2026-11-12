/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Single-bit security gives CPA security of the padded scheme

The claim after [PS10, Definition 171.5]: a single-bit secure public-key scheme, padded to fixed
length (`BitPublicKeyScheme.padded`, `Encryption.PublicKey.OracleSecurity`), is CPA-secure in the
oracle game `FixedLengthPKScheme.indGame`.

Under CPA the adversary's view is `pk`, its coins and the padded challenge. Only the first
challenge query uses coins, so the encryption coins may be sampled in advance
(`expect_simulate_indImpl_cpa`). The distinguisher answers every challenge with its own padded
ciphertext and outputs the adversary's bit, corrected by the first challenge pair; it is T1's
machine for the recording handler (`OracleSecurity.RecordHandler`). The two advantages are equal
at every `n` (`padded_cpa_advantage_eq`). The deterministic run and first-challenge congruence
are `OracleSecurity.ChallengeSim`'s.

## Main results

* `expect_simulate_indImpl_cpa`: eager challenge coins under CPA.
* `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: single-bit security gives CPA security of
  the padded scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### From ensemble security to CPA -/

section PaddedCPA

open ChallengeSim ProbComp

/-- The reduction's challenge answer, read from its context `⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩`: the padding
`padCt L(n) c` of the ciphertext it received. -/
private def cpaAns (L : PolyExpr) (ctx : List Bool) : List Bool :=
  padCt (L.eval (pairFstD ctx).length) (pairSndD (pairFstD (pairSndD ctx)))

/-- The challenge answer is polynomial-time (as `padEncFun`). -/
private theorem polyTimeComputable_cpaAns (L : PolyExpr) : PolyTimeComputable (cpaAns L) := by
  have hc : PolyTimeComputable fun ctx => pairSndD (pairFstD (pairSndD ctx)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have h := hc.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((hc.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp polyTimeComputable_pairFstD)))
  convert h using 1
  funext ctx
  simp [cpaAns, padCt_eq, Function.comp_apply, length_pairEncode]

/-- On the context `⟨1^n, ⟨z, ω⟩⟩` the challenge answer is `padCt L(n) (pairSndD z)`. -/
private theorem cpaAns_seedIn (L : PolyExpr) (n : ℕ) (z ω : List Bool) :
    cpaAns L (seedIn n z ω) = padCt (L.eval n) (pairSndD z) := by
  simp only [cpaAns, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The selected half of a two-bit challenge query, as a list, is its bit `0` or `1`. -/
private theorem ofFn_splitHalf_bit {k : ℕ} (hk : k = 1) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      [(List.ofFn mm).getD (if b then 1 else 0) false] := by
  subst hk
  cases b <;> simp [FixedLengthScheme.splitHalf_fst, FixedLengthScheme.splitHalf_snd,
    List.ofFn_succ]

/-- **Eager challenge coins under CPA.** Simulating the oracles of `Ind_b` from the state `s` has,
for every `G`, the expectation of first sampling the encryption coins `re` and then running the
deterministic oracles whose challenge `mm` is answered with `Enc(⟨pk, m_b⟩; re)`, the halves and the
recorded ciphertext read through `indSpec_challengeDom` and `indSpec_challengeRng`:
`𝔼[G ∘ fst] (simulate (indImpl .cpa b n pk sk) c s) = 𝔼_{re} G (chRun g_re c s).1`.

**Proof sketch.** `ChallengeSim.expect_simulate_eager` with `d = ctLen(n)` (`outLens_one`), the
cast `indSpec_challengeRng`, and the oracle equations `indImpl_dec_onSpec` (with `decOpen_cpa`),
`indImpl_challenge_repeat_onSpec` and `indImpl_challenge_none_onSpec`: decryption queries are
answered all-`false`, a repeated challenge repeats the record, and the first challenge samples the
coins and records the encryption. -/
theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    expect (simulate (S.indImpl .cpa b n pk sk) c s) (fun p => G p.1) =
      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).2
            else (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).1))) re)
          c (s.map (cast (S.indSpec_challengeRng n).symm))).1 :=
  expect_simulate_eager (S.outLens_one n) (S.indSpec_challengeRng n).symm _ _
    (fun x s => by
      rw [S.indImpl_dec_onSpec]
      simp only [FixedLengthScheme.decOpen_cpa, Bool.false_and, Bool.false_eq_true, if_false])
    (fun mm C => S.indImpl_challenge_repeat_onSpec .cpa b n pk sk mm C)
    (fun mm => S.indImpl_challenge_none_onSpec .cpa b n pk sk mm) G c s

/-- **The exact identity of step 4.** Let `B` be the machine of T1 for the recording handler
with challenge answer `cpaAns L` (with its coin bijection `φ`). At every `n`, `A`'s CPA advantage
against the padded scheme equals `B`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`. Game `b` samples `rg`, `A`'s coins `r` and (eagerly,
`expect_simulate_indImpl_cpa`) encryption coins `re`; by first-challenge congruence (`chRun_congr`)
its output is `A`'s bit `F(w)` when the challenge is answered with `w = padCt L(n) (Enc(m_b; re))`,
where `(m₀, m₁)` is `A`'s first challenge query (`firstQ`), or `F` of anything without one. On
`z = ⟨pk, Enc(β; re)⟩`, T1 and `simulate_recHandler_init` show that `B` with coins `φ (ω, r)` runs
`A` with the same answers `padCt L(n) (Enc(β; re))` and outputs the post-processed bit
(`recOut_init`, `recOut_recorded`), after transporting the run between the two equal codecs
(`chRun_toCompOn_transport`). Rearranging the samples (`expect_sample_prod`, `_comm`, `_equiv`
along `φ` and `padEnc_coins`, `_unique` for the empty seed), both differences of acceptance
rates become `𝔼_{rg, r}` of a pointwise difference, which agree by `expect_indicator_sub`. -/
private theorem padded_cpa_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (B : NUPPT) (n : ℕ)
    (φ : (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool) ×
      A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool)
      (r : A.Coins n),
      ∃ (a : Fin ((PolyExpr.const 1).eval n) → Bool)
        (s : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).stateLen.eval n) → Bool),
        simulate ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).impl n z ω)
            (A.toCompOn (bitCodec (fun i => (recDin L i).eval n) (fun i => (recDout L i).eval n)
              ((PolyExpr.const 1).eval n)) n (q.eval n)
              ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n z ω) r)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).init n) = .pure (a, s) ∧
          B.runAt n z (φ (ω, r)) =
            (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).result n z ω s a) :
    advantage ((S.padded L hL hmsg).indGame .cpa A (q.eval n) false n)
        ((S.padded L hL hmsg).indGame .cpa A (q.eval n) true n) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (B.distinguisherL n) := by
  -- Notation: the game's computation, the padded ciphertexts, and `A`'s bit.
  set S' := S.padded L hL hmsg with hS'
  let comp : S.gen.Coins n → A.Coins n → OracleComp (S'.indSpec n) (Fin 1 → Bool) :=
    fun rg r => A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r
  let W : Bool → S.gen.Coins n → S.enc.Coins n → List Bool := fun β rg re =>
    padCt (L.eval n) (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re)
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  -- The two codecs have equal lengths.
  have hins : (fun i => (recDin L i).eval n) = S'.inLens n := by
    funext i
    match i with
    | 0 => rw [recDin_zero, FixedLengthPKScheme.inLens_zero, BitPublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [recDin_one, FixedLengthPKScheme.inLens_one, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
  have houts : (fun i => (recDout L i).eval n) = S'.outLens n := by
    funext i
    match i with
    | 0 =>
      rw [recDout_zero, FixedLengthPKScheme.outLens_zero, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
    | 1 => rw [recDout_one, FixedLengthPKScheme.outLens_one, BitPublicKeyScheme.padded_ctLen]
  -- Step 4, game side: eager coins, first-challenge congruence, and the coin transport.
  have hG : ∀ b : Bool, accept (S'.indGame .cpa A (q.eval n) b n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if F rg r ((firstQ (comp rg r)).elim []
                fun l => W (l.getD (if b then 1 else 0) false) rg re) = true then 1 else 0 := by
    intro b
    rw [accept_eq, FixedLengthPKScheme.indGame_eq, prob_bind]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine (expect_simulate_indImpl_cpa S' b n _ _
      (fun a => ProbComp.prob (.pure (a 0)) (· = true)) (comp rg r) none).trans ?_
    rw [← expect_sample_equiv (NUPPT.coinsCongr (padEnc_coins S.enc L) n)]
    refine congrArg _ (funext fun re' => ?_)
    rw [prob_pure]
    congr 2
    refine congrArg (fun p : (Fin 1 → Bool) × Option (Fin (S'.ctLen.eval n) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => ?_)
    rw [hmm, Option.elim_some]
    exact (runAt_padEnc S.enc_uniform L n _ re').trans (by
      rw [ofFn_splitHalf_bit (by rw [BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const])]
      rfl)
  -- Step 4, distinguisher side: T1, the handler's simulation, and the codec transport.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool),
      B.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (ω, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false) := by
    intro β rg r re ω
    obtain ⟨a, s, hsim, hrun⟩ := hφ (S.pkEncDist n β (rg, re)) ω r
    have hadv :
        (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
          (S.pkEncDist n β (rg, re)) ω =
        pairFstD (S.gen.runAt n [] rg) := by
      rw [PolyHandler.advInput_eq, recHandler_advIn, recAdvIn_eq, seedIn_eq,
        BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode, pairFstD_pairEncode,
        pairFstD_pairEncode]
    have hans : cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω)) = W β rg re := by
      rw [cpaAns_seedIn, BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode]
    have hw : (cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω))).length =
        L.eval n := by
      rw [hans]
      exact length_padCt (hL n rg β re)
    obtain ⟨s', hsim', hs'⟩ := simulate_recHandler_init L (polyTimeComputable_cpaAns L) n
      (S.pkEncDist n β (rg, re)) ω hw _
    rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
    obtain ⟨rfl, rfl⟩ := hsim'
    obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport hins houts (PolyExpr.eval_const 1 n)
      A n (q.eval n) ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
        (S.pkEncDist n β (rg, re)) ω) r (W β rg re)
    rw [hadv] at h₁ h₂ hs'
    rw [h₂] at hs'
    rw [NUPPT.distinguisherL_eq, hrun, PolyHandler.result_eq, recHandler_out]
    have ha : List.ofFn (chRun (fun _ => cpaAns L (seedIn n (S.pkEncDist n β (rg, re))
        (List.ofFn ω))) (A.toCompOn (bitCodec (fun i => (recDin L i).eval n)
          (fun i => (recDout L i).eval n) ((PolyExpr.const 1).eval n)) n (q.eval n)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
              (S.pkEncDist n β (rg, re)) ω) r) none).1 =
        [F rg r (W β rg re)] := by
      rw [hans, hadv, h₁, List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [ha]
    cases hq : firstQ (comp rg r) with
    | none =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = none := hq
      rw [hq', Option.elim_none] at hs'
      rw [hs', recOut_init, Option.elim_none]
      decide
    | some l =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = some l := hq
      have hl : l.length = 2 := by
        rw [length_of_firstQ_eq_some _ hq', FixedLengthPKScheme.inLens_one,
          BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
      obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
      rw [hq', Option.elim_some] at hs'
      rw [hs', recOut_recorded, Option.elim_some]
      simp only [List.headD_cons, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
        and_true, Bool.decide_eq_true]
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (B.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if ((firstQ (comp rg r)).elim false fun l =>
              (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false)) = true
            then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    haveI : Unique (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) →
        Bool) := by
      rw [recHandler_seedLen, PolyExpr.eval_const]
      infer_instance
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_unique]
    refine congrArg _ (funext fun r => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re]
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hG false, hG true, hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none =>
    simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    have hl : l.length = 2 := by
      rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
        BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
    obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
    simp only [Option.elim_some, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
      if_false, if_true]
    exact expect_indicator_sub (fun β re => F rg r (W β rg re)) m₀ m₁

/-- **Single-bit security gives CPA security** for a padded single-bit scheme.

**Proof sketch.**
1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
   seeing `pk`. Only the first challenge query uses coins, so the encryption coins may be sampled
   in advance (`expect_simulate_indImpl_cpa`); then `A`'s bit depends on the challenge answer only
   through its value at `A`'s first challenge query `(m₀, m₁)`, which itself does not depend on
   that answer (`ChallengeSim.chRun_congr`).
2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
   on `⟨pk, c⟩` runs `A` on `pk`, answers every challenge with `padCt L c` and every `Dec` query
   with `⊥`, records `A`'s first challenge `(m₀, m₁)`, and outputs `A`'s bit, flipped when
   `(m₀, m₁) = (1, 0)` and replaced by `0` when `m₀ = m₁` or no challenge was asked. T1
   (`Games.exists_handlerMachine`, for the handler `ChallengeSim.recHandler`) makes `D` a
   machine, whose output is exactly this bit (`ChallengeSim.simulate_recHandler_init`).
3. Fixing `pk` and `A`'s coins, the case split on `(m₀, m₁)` gives the same difference of
   acceptance rates on both sides (`ChallengeSim.expect_indicator_sub`); so `A`'s CPA advantage
   equals `D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩` at every `n`
   (`padded_cpa_advantage_eq`), which is negligible (`BitPublicKeyScheme.singleBitSecure_iff`). -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Step 3: the distinguisher `D` is T1's machine for the recording handler.
  obtain ⟨B, hB⟩ := exists_handlerMachine A q (recDin L) (recDout L) (.const 1)
    (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L))
  refine ⟨_, (BitPublicKeyScheme.singleBitSecure_iff S).1 h B, fun n => le_of_eq ?_⟩
  -- Step 4: the advantages are equal.
  obtain ⟨φ, hφ⟩ := hB n
  exact padded_cpa_advantage_eq L hL hmsg A q B n φ hφ

end PaddedCPA

end TCSlib.Cryptography.Composability
