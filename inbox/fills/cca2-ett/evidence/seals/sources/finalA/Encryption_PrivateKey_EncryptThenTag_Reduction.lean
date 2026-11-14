/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Reduction: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean` (PolyExpr.eval open). -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
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
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Reduction: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tag-key PRF reduction for the encrypt-then-tag scheme

The reduction of [PS10, Theorem 170.4], step 1, as a next-query oracle machine at parameter `2n`:
the budget cap of the adversary (`exists_capMachine`), the input-free companion
(`Games.exists_toCompOn_of_toComp`), T2 (`Games.exists_interactiveHandlerMachine`) applied to the
handler `dHandler` with the budget `q(2n)`, T4 (`Games.exists_toOracleAdversary_of_bitCodec`) at
the length `2n`, and the parameter halving (`exists_halfMachine`). Its acceptance probability at
parameter `2n` against any function `g` on `2n` bits is the acceptance probability of the CCA2
experiment with `f_{k₁}` and `g` (`exists_tagReduction`).

The proof answers the handler's outer queries by `g` (`gOuter`) and composes the two
implementations (`QueryImpl.comp`). Each composed call, from the encoded state `dState j o`, is the
call of `ettTape` from `((o, T), j)` with the handler's tapes in advance (`comp_dAbs`), as long as
`j` is below the number `q(2n)` of tapes; the capped adversary asks at most `q(n) ≤ q(2n)` queries,
so this holds along every run (`Games.simulate_eq_of_abs_bounded`). Drawing the seed uniformly
gives the key and fresh nonces (`expect_ettTape`).

## Main definitions

* `ETTGame.gOuter`: the outer oracle answering with `g`.
* `ETTGame.dAbs`: the handler's state as a function of `ettTape`'s state.

## Main results

* `ETTGame.comp_dAbs`: one composed call is a call of `ettTape`.
* `ETTGame.exists_tagReduction`: the reduction.
* `ETTGame.prfAdv_eq_expect`: the PRF advantage as expectations.
* `ETTGame.exists_tagStep`: step 1, the gap to the random tag function is a PRF advantage at `2n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book p. 170).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### The outer oracle and the composed calls -/

/-- **The outer oracle answering with `g`:** a query `x` is answered `g x`, lengths adjusted. -/
noncomputable def gOuter (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    QueryImpl (bitSpecAt tagOut tagOut n) Unit unifSpec :=
  QueryImpl.ofComp fun _ x => .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))))

/-- `gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
theorem gOuter_apply (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (i : Fin 1)
    (x : (bitSpecAt tagOut tagOut n).dom i) (s : Unit) :
    gOuter n g i x s = .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))), s) := by
  rw [gOuter, QueryImpl.ofComp_apply, OracleComp.pure_bind]

section Composed

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))
  (q : PolyExpr) (b : Bool) (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
  (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)

/-- The handler's state and the (trivial) outer state, as functions of `ettTape`'s state. -/
def dAbs (s : St n (ettCt.eval n) × ℕ) :
    (Fin ((dHandler q E hE b).stateLen.eval n) → Bool) × Unit :=
  (dHState q E hE b n s.2 s.1.1, ())

/-- `dAbs q E hE b n s = (dHState q E hE b n s.2 s.1.1, ())`. -/
theorem dAbs_eq (s : St n (ettCt.eval n) × ℕ) : dAbs E hE q b n s = (dHState q E hE b n s.2 s.1.1, ()) :=
  rfl

/-- The tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`). -/
noncomputable def dTapes : ℕ → Fin n → Bool :=
  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W)

/-- `dTapes q n W = extTape (blocks (q n) n W)`. -/
theorem dTapes_eq : dTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W) :=
  rfl

/-- Below `q(n)`, the extended tapes are the tapes: `dTapes q n W j = dTape q n W j hj`. -/
theorem dTapes_of_lt (j : ℕ) (hj : j < q.eval n) : dTapes q n W j = dTape q n W j hj := by
  rw [dTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, dTape_eq]

/-- Reading the answer of `g` to a pair `r ‖ c₁` with `|r| = |c₁| = n` through the outer oracle:
`⟦padFin _ ⟦g (padFin (2n) ⟦padFin _ (r ++ c₁)⟧)⟧⟧ = tagL g r c₁`. -/
private theorem gOuter_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
    List.ofFn (padFin ((tagOut 0).eval n) (List.ofFn (g (padFin (2 * n)
      (List.ofFn (padFin ((tagOut 0).eval n) (r ++ c))))))) = tagL g r c := by
  have h2 : (tagOut 0).eval n = 2 * n := by rw [tagOut_eq, tagLen_eval]
  have e1 : List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
    ofFn_padFin_of_length (by rw [List.length_append, hr, hc, h2]; omega)
  rw [e1, ofFn_padFin_of_length (by rw [List.length_ofFn, h2]), tagL_eq, pairV_eq]

include hFE in
/-- **One composed call is a call of `ettTape` with the tapes in advance:** from the encoded state
`dState j o` with `j < q(n)`, the handler composed with `gOuter g` answers as `ettTape` with pad
function `f_k` and tag function `g` and the tapes `dTapes W` from `((o, T), j)`, both
deterministic, with the new state abstracted; the counter grows by one.

**Proof sketch.** By the oracle, the record, the refusal test and well-formedness: encryption and a
first challenge ask `g` at `r ‖ c₁` (`dHandler_impl_enc`, `dHandler_impl_challenge_none`); a
well-formed decryption that is not refused asks `g` at its pair (`dHandler_impl_dec_wf`); the
other calls answer directly. The outer oracle answers `g` (`gOuter_apply`, `gOuter_pair`), and the
answers are `ettStep`'s (`ettStep_enc`, …, `decAnsW_eq`). -/
theorem comp_dAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
    (s : St n (ettCt.eval n) × ℕ) (hs : s.2 < q.eval n) :
    ∃ (y : (bitSpecAt ettDin ettDout n).rng i) (s' : St n (ettCt.eval n) × ℕ),
      ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n (F n k)
          g b (dTapes q n W) i x s = .pure (y, s') ∧ s'.2 ≤ s.2 + 1 ∧
      (gOuter n g).comp ((dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W))) i x
          (dAbs E hE q b n s) = .pure (y, dAbs E hE q b n s') := by
  obtain ⟨⟨o, T⟩, j⟩ := s
  have hj : j < q.eval n := hs
  refine ⟨(ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g false b (dTapes q n W j) i x (o, T)).1,
    ((ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g false b (dTapes q n W j) i x (o, T)).2, j + 1),
    ettTape_apply (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g b (dTapes q n W) i x (o, T) j, le_rfl, ?_⟩
  rw [dTapes_of_lt q n W j hj, QueryImpl.comp_apply, dAbs_eq]
  simp only
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    rw [dHandler_impl_enc q E hE b F hFE n z k W x j o hj, simulate_query, gOuter_apply,
      OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, ettStep_enc, dAbs_eq,
      gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hx), ← encW_eq]
  | 1, x =>
    rw [ettStep_dec, decAnsW_eq]
    by_cases href : refW o (List.ofFn x) = true
    · rw [dHandler_impl_dec_ref q E hE b n z k W x j o hj href, simulate_pure,
        OracleComp.pure_bind, dAbs_eq]
      simp only [href, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    · rw [Bool.not_eq_true] at href
      by_cases hwf : wfW n (List.ofFn x) = true
      · have hwf' := hwf
        rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
        rw [dHandler_impl_dec_wf q E hE b F hFE n z k W x j o hj href hwf, simulate_query,
          gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, dAbs_eq,
          gOuter_pair n g hwf'.1 hwf'.2, validW_eq, hwf, href]
        simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true, decide_eq_true_eq]
        by_cases ht : tagL g (wR (List.ofFn x)) (wC (List.ofFn x)) = wT (List.ofFn x)
        · rw [if_pos ht, if_pos ht.symm]
        · rw [if_neg ht, if_neg (Ne.symm ht)]
      · rw [Bool.not_eq_true] at hwf
        rw [dHandler_impl_dec_nwf q E hE b n z k W x j o hj href hwf, simulate_pure,
          OracleComp.pure_bind, dAbs_eq, validW_eq, hwf]
        simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
  | 2, x =>
    cases o with
    | some c =>
      rw [dHandler_impl_challenge_some q E hE b n z k W x j c hj, simulate_pure,
        OracleComp.pure_bind, ettStep_challenge_some, dAbs_eq]
    | none =>
      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
        have hx : (List.ofFn x).length = n + n := by
          rw [List.length_ofFn]
          show (ettDin 2).eval n = n + n
          rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
        rw [AdaptiveCPA.msgOf_eq]
        cases b <;> simp [hx]
      rw [dHandler_impl_challenge_none q E hE b F hFE n z k W x j hj, simulate_query,
        gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        ettStep_challenge_none, dAbs_eq,
        gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hmsg), ← encW_eq]

end Composed

/-! ### The reduction -/

/-- The budget `q(2n)` of the handler's adversary: `(q.subst tagLen).eval n = q(2n)`. -/
theorem eval_subst_tagLen (q : PolyExpr) (n : ℕ) : (q.subst tagLen).eval n = q.eval (2 * n) := by
  rw [PolyExpr.eval_subst, tagLen_eval]

/-- **The experiment does not see the output width:** for `d = d'`, the expected first output bit
of the run through `bitCodec ins outs d` and through `bitCodec ins outs d'` agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem expect_ettImpl_outLen {ins outs : Fin 3 → ℕ} {c n : ℕ} {d d' : ℕ} (hd : d = d')
    (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (rej b : Bool) (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d') n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hd
  rfl

section Reduction

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

include hE hFE in
/-- **The tag-key PRF reduction** [PS10, Theorem 170.4, step 1]: for a machine adversary `A` with
budget `q` and a challenge bit `b`, there is a next-query machine `D` such that, at every `n` and
for every function `g` on `2n` bits, `D` at parameter `2n` with budget `q(2n)` accepts against `g`
with the probability that `A` outputs `1` in the CCA2 experiment with `f_k` (`k` a uniform `n`-bit
key) and `g` in place of `f_{k₂}` (the oracles `ettImpl … false b`, on the lengths `ettDin`,
`ettDout`):
`𝔼_c [D^g(2n; c) = 1] = 𝔼_k 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f_k g false b) (A …) ∅]`.

**Proof sketch.** `D` is the halving (`exists_halfMachine`) of T4 at length `2n` applied to T2's
machine `B` for `dHandler` with budget `q(2n)` and the input-free companion of the capped adversary
(`exists_capMachine`). Its coins at `2n` are, through the halving and the bijections of T4, T2, the
companion and the cap, a seed `(k, W)` and `A`'s coins `r` (`expect_sample_equiv`,
`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed seed and coins, T4 and T2 turn
`D`'s run against `g` into the evaluation, with `g`, of the reduction; evaluation is simulation
with `gOuter g` (`simulate_ofComp_pure`), which composes with the handler (`simulate_bind`,
`simulate_comp`, `dHandler_finish`); along the adversary's run (at most `q(2n)` queries) the
composite is `ettTape` with the tapes of `W` (`simulate_eq_of_abs_bounded`, `comp_dAbs`). Drawing
`W` uniformly gives fresh nonces (`expect_ettTape`), and the capped adversary at budget `q(2n)` is
`A` at budget `q(n)` (`exists_capMachine`). Widths are transported by
`eval_toOracleAdversary_len`, `PRFGame.ofFn_evalFn_toCompOn` and `expect_ettImpl_outLen`. -/
theorem exists_tagReduction (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
      expect (sample (D.Coins (2 * n)))
          (fun c => if (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)) c).eval g = true
            then (1 : ℝ) else 0) =
        expect (sample (Fin n → Bool)) fun k => expect (sample (A.Coins n)) fun r =>
          expect (simulate (ettImpl (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
              (ettCt.eval n) n (F n k) g false b)
              (A.toComp (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) 1) n
                (q.eval n) r) (none, []))
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A₁, hA₁c, hA₁⟩ := exists_capMachine A q
  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A₁
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ (q.subst tagLen) ettDin ettDout tagOut
    tagOut (.const 1) (dHandler (q.subst tagLen) E hE b)
  obtain ⟨B', -, hB'⟩ := exists_toOracleAdversary_of_bitCodec B tagLen tagLen
  obtain ⟨D, hD⟩ := exists_halfMachine B'
  refine ⟨D, fun n g => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hB' n
  have hq₂ : (q.subst tagLen).eval n = q.eval (2 * n) := eval_subst_tagLen q n
  have hQ : (q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
      (dHandler (q.subst tagLen) E hE b).finCall.eval n = q.eval (2 * n) := by
    rw [dHandler_perCall, dHandler_finCall, PolyExpr.eval_const, PolyExpr.eval_const, hq₂]
    ring
  have hout : (dHandler (q.subst tagLen) E hE b).outLen.eval n = 1 := by
    rw [dHandler_outLen, PolyExpr.eval_const]
  have hle : q.eval n ≤ (q.subst tagLen).eval n := by
    rw [hq₂]
    exact q.eval_mono (by omega)
  -- `D`'s coins at `2n` are `B'`'s at `n`, then a seed and `A`'s coins.
  rw [hD n (2 * n) (2 * n) (q.eval (2 * n)) g, ← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂,
    ChallengeSim.expect_sample_prod, expect_sample_comm, ← expect_sample_equiv φ₀,
    ← expect_sample_equiv (NUPPT.coinsCongr hA₁c n)]
  conv_rhs => rw [expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  rw [← expect_sample_equiv (dHSeed (q.subst tagLen) E hE b n), ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun k => ?_)
  -- One run of `D` is the reduction evaluated with `g`.
  have hrun : ∀ W : Fin ((q.subst tagLen).eval n * n) → Bool,
      (if (B'.toOracleAdversary n (2 * n) (2 * n) (q.eval (2 * n))
          (φ₄ (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W),
            φ₀ (NUPPT.coinsCongr hA₁c n r))))).eval g = true then (1 : ℝ) else 0) =
      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n (F n k) g b (dTapes (q.subst tagLen) n W))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro W
    have key : ∀ v : Fin 1 → Bool, (if v 0 = true then (1 : ℝ) else 0) =
        if (List.ofFn v).headD false = true then 1 else 0 := fun v => by
      rw [headD_ofFn_one]
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => tagLen.eval n)
        (fun _ => tagLen.eval n) ((dHandler (q.subst tagLen) E hE b).outLen.eval n)) n
        ((q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
          (dHandler (q.subst tagLen) E hE b).finCall.eval n)
        [] (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W), φ₀ (NUPPT.coinsCongr hA₁c n r))) :=
      hφ₂ [] (dHSeed (q.subst tagLen) E hE b n (k, W)) (φ₀ (NUPPT.coinsCongr hA₁c n r))
    rw [eval_toOracleAdversary_len B' n _ _ (tagLen_eval n), hφ₄, ← hQ, key,
      PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ [] _, ← h2, dHandler_advInput]
    have hev : simulate (gOuter n g) ((simulate ((dHandler (q.subst tagLen) E hE b).impl n []
        (dHSeed (q.subst tagLen) E hE b n (k, W)))
        (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
          (φ₀ (NUPPT.coinsCongr hA₁c n r)))
        ((dHandler (q.subst tagLen) E hE b).init n)).bind
        (fun res => (dHandler (q.subst tagLen) E hE b).finish n []
          (dHSeed (q.subst tagLen) E hE b n (k, W)) res.2 res.1)) () = _ :=
      simulate_ofComp_pure _ _ _
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, dHandler_finish, simulate_pure, expect_pure]
    rw [dHandler_init_hstate, show (dHState (q.subst tagLen) E hE b n 0 none, ()) =
        dAbs E hE (q.subst tagLen) b n ((none, []), 0) from
          (dAbs_eq E hE (q.subst tagLen) b n ((none, []), 0)).symm,
      simulate_eq_of_abs_bounded _ _ (dAbs E hE (q.subst tagLen) b n) (fun s => s.2)
        ((q.subst tagLen).eval n)
        (fun i x s hs => comp_dAbs F E hE hFE (q.subst tagLen) b n g [] k W i x s hs) _
        ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
        (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    refine congrArg _ (funext fun p => ?_)
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])]
  simp only [hrun, dTapes_eq]
  rw [expect_sample_equiv (EnsembleLemmas.blocks ((q.subst tagLen).eval n) n) (fun T =>
      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n (F n k) g b (AdaptiveCPA.extTape T))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_ettTape _ _ _ _ _ _ _ ((q.subst tagLen).eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
      ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
    hφ₀, hA₁ n _ _ _ _ _ hle]
  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n) _ _ _ _ A _ r

/-- **The PRF advantage as expectations** (PRFGame overlap: `prfAdv_prfReduction`, re-derived here
in general form from the published readers): for an oracle adversary `A'` on `m`-bit strings,
`prfAdv F A' = |𝔼_k 𝔼_c [A'(c)^{F k} = 1] − 𝔼_R 𝔼_c [A'(c)^R = 1]|`.

**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
key (resp. the function table) and the coins (`Bridge.acceptProb_eq`, `accept_eq`,
`Bridge.acceptGame_eq`, `prob_bind`, `oracleDist_apply`, `randomFunction_apply`). -/
theorem prfAdv_eq_expect {m : ℕ} (Fm : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool))
    {ρ : Type} [Fintype ρ] [Nonempty ρ] (A' : OracleAdversary ρ (Fin m → Bool) (Fin m → Bool)) :
    prfAdv Fm A' =
      |expect (sample (Fin m → Bool))
          (fun k => expect (sample ρ) fun c => if (A' c).eval (Fm k) = true then (1 : ℝ) else 0) -
        expect (sample ((Fin m → Bool) → (Fin m → Bool)))
          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]

include hE hFE in
/-- **Step 1 of [PS10, Thm 170.4]: the tag key becomes a random function.** For a machine
adversary `A` with budget `q` and a challenge bit `b` there is a next-query machine `D` such that at
every `n` the gap between the experiments with the tag functions `f_{k₂}` (`k₂` a uniform `2n`-bit
key) and a uniform random function on `2n` bits, the pad function being `f_{k₁}`, is the PRF
advantage of `D` at parameter `2n` with budget `q(2n)`.

**Proof sketch.** `exists_tagReduction` gives `D` and its acceptance probability against every `g`;
`prfAdv_eq_expect` writes the advantage as the gap between the averages over `k₂` and over the
function table; exchange the averages with the key `k₁` (`expect_sample_comm`). -/
theorem exists_tagStep (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ n : ℕ,
      |(expect (sample (Fin n → Bool)) fun k => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
            (F n k) (F (2 * n) k₂) false b A (q.eval n)) -
        (expect (sample (Fin n → Bool)) fun k =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k) R false b A (q.eval n))| =
        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
  obtain ⟨D, hD⟩ := exists_tagReduction F E hE hFE A q b
  refine ⟨D, fun n => ?_⟩
  rw [prfAdv_eq_expect]
  simp only [hD n, ettAcc_eq]
  rw [expect_sample_comm (α := Fin n → Bool) (β := Fin (2 * n) → Bool),
    expect_sample_comm (α := Fin n → Bool) (β := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))]

end Reduction

end TCSlib.Cryptography.Composability.ETTGame
