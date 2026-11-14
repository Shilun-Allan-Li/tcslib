/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.CPAHandler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_CPAReduction: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean` (PolyExpr.eval open). -/
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
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_CPAReduction: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CPA reduction for the encrypt-then-tag scheme

Step 3 of [PS10, Theorem 170.4]: the experiment that rejects fresh decryption queries, with a
uniform random tag function, is the CPA experiment of the §3.9 scheme against a machine adversary
`B` (`exists_cpaStep`). `B` is T2 (`Games.exists_interactiveHandlerMachine`) applied to the handler
`bHandler` (through the input-free companion `Games.exists_toCompOn_of_toComp`), run on the empty
input (`NUPPT.exists_comp`).

The proof composes the handler with the CPA oracles `PRFGame.fImpl` (`QueryImpl.comp`). Each
composed call, from the encoded state `bState j L o` and the CPA record of `o`, has the law of the
call of the lazy experiment with the tapes in advance (`ettLazyTape`) from `((o, L), j)`
(`comp_bAbs`), as long as `j` is below the number `q(n)` of tapes and the table has at most `j`
entries of `n`-bit messages (`bInv`, kept by every call, `ettLazyTape_bInv`); the adversary asks
at most `q(n)` queries, so this holds along every run (`expect_simulate_abs_inv`). Drawing the
seed uniformly gives fresh tapes (`expect_ettLazyTape`), and the lazy experiment is the rejecting
experiment with a uniform random tag function (`expect_ettImpl_lazy`).

## Main definitions

* `ETTGame.cpaRec`: the CPA record `⟨r, c₁⟩` of a CCA2 record `⟨r, ⟨c₁, t⟩⟩`.
* `ETTGame.bAbs`, `bInv`, `bTapes`: the abstraction, the invariant and the tapes.

## Main results

* `ETTGame.comp_bAbs`: one composed call has the law of a call of `ettLazyTape`.
* `ETTGame.ettLazyTape_bInv`: the calls of `ettLazyTape` keep the invariant.
* `ETTGame.exists_cpaStep`: step 3, the rejecting experiment with a random tag function is a CPA
  experiment of the §3.9 scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.PRFGame (pkDin pkDout ctP fImpl atkOf qRed ctOf)

/-! ### The abstraction -/

/-- **The CPA record** of a CCA2 record `c = ⟨r, ⟨c₁, t⟩⟩`: the pair `⟨r, c₁⟩` at `3n + 2` bits. -/
def cpaRec (n : ℕ) (c : Fin (ettCt.eval n) → Bool) : Fin (ctP.eval n) → Bool :=
  padFin _ (pairEncode (wR (List.ofFn c)) (wC (List.ofFn c)))

/-- `cpaRec n c = padFin _ ⟨wR ⟦c⟧, wC ⟦c⟧⟩`. -/
theorem cpaRec_eq (n : ℕ) (c : Fin (ettCt.eval n) → Bool) :
    cpaRec n c = padFin _ (pairEncode (wR (List.ofFn c)) (wC (List.ofFn c))) := rfl

/-- **The abstraction:** the handler's state `bState j L o` and the CPA record of `o`, as functions
of the lazy experiment's state `(o, L)` with the counter `j`. -/
def bAbs (q : PolyExpr) (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
    (Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool) :=
  (bHState q n s.2 s.1.2 s.1.1, s.1.1.map (cpaRec n))

/-- `bAbs q n ((o, L), j) = (bHState q n j L o, o.map (cpaRec n))`. -/
theorem bAbs_eq (q : PolyExpr) (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
    bAbs q n s = (bHState q n s.2 s.1.2 s.1.1, s.1.1.map (cpaRec n)) := rfl

/-- **The invariant:** the table has at most one entry per query, each with an `n`-bit message. -/
def bInv (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) : Prop :=
  s.1.2.length ≤ s.2 ∧ ∀ e ∈ s.1.2, e.2.2.length = n

/-- `bInv n ((o, L), j) ↔ |L| ≤ j ∧ every message of `L` has `n` bits`. -/
theorem bInv_iff (n : ℕ) (s : LSt n (ettCt.eval n) × ℕ) :
    bInv n s ↔ s.1.2.length ≤ s.2 ∧ ∀ e ∈ s.1.2, e.2.2.length = n := Iff.rfl

section Composed

variable (q : PolyExpr) (b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (z : List Bool)
  (W : Fin (q.eval n * (2 * n)) → Bool)

/-- The tag tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`). -/
noncomputable def bTapes : ℕ → Fin (2 * n) → Bool :=
  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) (2 * n) W)

/-- `bTapes q n W = extTape (blocks (q n) (2n) W)`. -/
theorem bTapes_eq : bTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) (2 * n) W) :=
  rfl

/-- Below `q(n)`, the extended tapes are the tapes: `bTapes q n W j = bTapeOf q n W j hj`. -/
theorem bTapes_of_lt (j : ℕ) (hj : j < q.eval n) : bTapes q n W j = bTapeOf q n W j hj := by
  rw [bTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, bTapeOf_eq]

/-- The CPA ciphertext of an `n`-bit message as a list: `⟦padFin _ (ctOf r m (f r))⟧ = ⟨r, m ⊕ f(r)⟩`. -/
private theorem ofFn_ctOf {k : ℕ} (hk : k = ctP.eval n) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) :
    List.ofFn (padFin k (ctOf r m (f r))) = pairEncode (List.ofFn r) (maskL f r m) := by
  rw [ofFn_padFin_of_length (by rw [PRFGame.length_ctOf r hm, hk, PRFGame.ctP_eval]),
    PRFGame.ctOf_eq, maskL_eq]

/-- The pair read from a CPA ciphertext is the pair of the encryption:
`bKeyOf n (padFin _ (ctOf r m (f r))) = pairV n ⟦r⟧ (maskL f r m)`. -/
private theorem bKeyOf_ctOf {k : ℕ} (hk : k = ctP.eval n) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) :
    bKeyOf n (padFin k (ctOf r m (f r))) = pairV n (List.ofFn r) (maskL f r m) := by
  rw [bKeyOf_eq, ofFn_ctOf n f hk r hm, pairFstD_pairEncode, pairSndD_pairEncode, pairV_eq]

/-- **One composed call has the law of a call of the lazy experiment with tapes in advance:** from
`bAbs ((o, L), j)` with the invariant and `j < q(n)`, the handler composed with the CPA oracles
with pad function `f` gives every function `g` of the answer and the state the expectation that
the call of `ettLazyTape` with the tapes `bTapes W` from `((o, L), j)` gives it, with the new state
abstracted.

**Proof sketch.** By the oracle and the record: encryption and a first challenge ask the CPA
oracle, which draws `r` and answers `⟨r, m ⊕ f(r)⟩` (`PRFGame.fImpl_enc`,
`PRFGame.fImpl_challenge_none`); the handler reads the pair `r ‖ (m ⊕ f(r))` (`bKeyOf_ctOf`) and
tags it as `lazyStep` does (`bHandler_impl_enc`, `bHandler_impl_challenge_none`), and the recorded
CPA challenge is the CPA record of the CCA2 record. Decryption and a repeated challenge answer
directly in both (`bHandler_impl_dec`, `bHandler_impl_challenge_some`), and the lazy experiment's
nonce is not read (`expect_const`). -/
theorem comp_bAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
    (s : LSt n (ettCt.eval n) × ℕ) (hP : bInv n s) (hs : s.2 < q.eval n)
    (g : (bitSpecAt ettDin ettDout n).rng i ×
      ((Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool)) → ℝ) :
    expect ((fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n
        (atkOf false) b f).comp ((bHandler q).impl n z (bHSeed q n W)) i x (bAbs q n s)) g =
      expect (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
        (ettCt.eval n) n f b (bTapes q n W) i x s) fun p => g (p.1, bAbs q n p.2) := by
  obtain ⟨⟨o, L⟩, j⟩ := s
  obtain ⟨hL, hm⟩ := hP
  have hj : j < q.eval n := hs
  have hLq : L.length ≤ q.eval n := le_trans hL hj.le
  rw [QueryImpl.comp_apply, bAbs_eq, ettLazyTape_eq, tapeImpl_apply, ettLazyK_eq,
    bTapes_of_lt q n W j hj]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, expect_bind, expect_pure]
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    have hx' : List.ofFn (padFin ((pkDin 0).eval n) (List.ofFn x)) = List.ofFn x :=
      ofFn_padFin_of_length (by rw [hx, PRFGame.pkDin_zero, PolyExpr.eval_var])
    rw [bHandler_impl_enc q n z W x j L o hj hLq hm, simulate_query, PRFGame.fImpl_enc]
    simp only [OracleComp.bind_assoc, OracleComp.pure_bind, simulate_pure, expect_bind, expect_pure]
    refine congrArg _ (funext fun r => ?_)
    have hk : (fun i => (pkDout i).eval n) 0 = ctP.eval n := by
      show (pkDout 0).eval n = ctP.eval n
      rw [PRFGame.pkDout_zero]
    rw [lazyStep_enc, bAbs_eq, hx', ofFn_ctOf n f hk r hx, bKeyOf_ctOf n f hk r hx,
      pairFstD_pairEncode, pairSndD_pairEncode]
  | 1, x =>
    rw [bHandler_impl_dec q n z W x j L o hj hLq hm, simulate_pure]
    simp only [expect_pure, lazyStep_dec, bAbs_eq, expect_const]
  | 2, x =>
    cases o with
    | some c =>
      rw [bHandler_impl_challenge_some q n z W x j L c hj hLq hm, simulate_pure]
      simp only [expect_pure, lazyStep_challenge_some, bAbs_eq, expect_const]
    | none =>
      have hxx : (List.ofFn x).length = n + n := by
        rw [List.length_ofFn]
        show (ettDin 2).eval n = n + n
        rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
      have hx' : List.ofFn (padFin ((pkDin 2).eval n) (List.ofFn x)) = List.ofFn x :=
        ofFn_padFin_of_length (by rw [hxx, PRFGame.pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
        rw [AdaptiveCPA.msgOf_eq]
        cases b <;> simp [hxx]
      rw [bHandler_impl_challenge_none q n z W x j L hj hLq hm, simulate_query, Option.map_none,
        PRFGame.fImpl_challenge_none]
      simp only [OracleComp.bind_assoc, OracleComp.pure_bind, simulate_pure, expect_bind,
        expect_pure]
      refine congrArg _ (funext fun r => ?_)
      have hk : (fun i => (pkDout i).eval n) 2 = ctP.eval n := by
        show (pkDout 2).eval n = ctP.eval n
        rw [PRFGame.pkDout_two]
      have hlen : (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x))))).getD (bTapeOf q n W j hj)))).length =
          ettCt.eval n := by
        rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn,
          length_maskL f r hmsg, List.length_ofFn, ettCt_eval]
        omega
      have hrec : cpaRec n (padFin (ettCt.eval n) (ctW (List.ofFn r)
          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn ((tagOf ((none, L) : LSt n (ettCt.eval n)) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn x))))).getD (bTapeOf q n W j hj))))) =
          padFin (ctP.eval n) (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r)) := by
        rw [cpaRec_eq, ofFn_padFin_of_length hlen, wR_ctW, wC_ctW, PRFGame.ctOf_eq, maskL_eq]
      rw [lazyStep_challenge_none, bAbs_eq, hx', ofFn_ctOf n f hk r hmsg, bKeyOf_ctOf n f hk r hmsg,
        pairFstD_pairEncode, pairSndD_pairEncode]
      simp only [Option.map_some, hrec]

/-- **The calls of the lazy experiment keep the invariant** and raise the counter by one: an
encryption adds one entry with the `n`-bit message; the other calls keep the table. -/
theorem ettLazyTape_bInv (T : ℕ → Fin (2 * n) → Bool) (i : Fin 3)
    (x : (bitSpecAt ettDin ettDout n).dom i) (s : LSt n (ettCt.eval n) × ℕ) (hP : bInv n s) :
    (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n f b T
      i x s).AllOutputs fun p => bInv n p.2 ∧ p.2.2 ≤ s.2 + 1 := by
  obtain ⟨⟨o, L⟩, j⟩ := s
  obtain ⟨hL, hm⟩ := hP
  rw [ettLazyTape_eq, tapeImpl_apply, ettLazyK_eq, OracleComp.bind_assoc]
  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ => ?_
  rw [OracleComp.pure_bind]
  refine OracleComp.allOutputs_pure.2 ⟨?_, le_rfl⟩
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    rw [lazyStep_enc, bInv_iff]
    refine ⟨by simp only [List.length_cons]; exact Nat.succ_le_succ hL, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hx
    · exact hm e he
  | 1, x =>
    rw [lazyStep_dec]
    exact ⟨Nat.le_succ_of_le hL, hm⟩
  | 2, x =>
    cases o with
    | some c =>
      rw [lazyStep_challenge_some]
      exact ⟨Nat.le_succ_of_le hL, hm⟩
    | none =>
      rw [lazyStep_challenge_none]
      exact ⟨Nat.le_succ_of_le hL, hm⟩

end Composed

/-! ### The reduction -/

/-- **Step 3 of [PS10, Thm 170.4]: the rejecting experiment with a random tag function is a CPA
experiment of the §3.9 scheme.** For a machine adversary `A` with budget `q` there is a machine
`B` such that, for every challenge bit `b`, every `n` and every pad function `f` on `n` bits, the
average over a uniform random tag function `R` of `A`'s acceptance probability in the experiment
that rejects fresh decryption queries is `B`'s acceptance probability in the CPA experiment with
pad function `f` (the oracles `PRFGame.fImpl`, on the lengths `pkDin`, `pkDout`) with budget
`qRed q`.

**Proof sketch.** `B` runs T2's machine for `bHandler` and the input-free companion of `A` on the
empty input (`NUPPT.exists_comp` with `pre = ⟨[], ·⟩`). Its coins are, through the bijections of
the companion, T2 and the seed, the tapes `W` and `A`'s coins `r` (`expect_sample_equiv`,
`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed `W` and `r`, T2 turns `B`'s run
against the CPA oracles into the handler's simulation of `A` composed with them (`simulate_bind`,
`simulate_comp`, `bHandler_finish`); along `A`'s run (at most `q(n)` queries) it has the law of
`ettLazyTape` with the tapes of `W` (`expect_simulate_abs_inv`, `comp_bAbs`, `ettLazyTape_bInv`).
Drawing `W` gives fresh tapes (`expect_ettLazyTape`), and the lazy experiment from the empty state
is the rejecting experiment averaged over `R` (`expect_ettImpl_lazy`; the empty tag table writes
nothing). Widths are transported by `Games.expect_toCompOn_outLen` and `expect_ettImpl_outLen`. -/
theorem exists_cpaStep (A : NUPPT) (q : PolyExpr) :
    ∃ B : NUPPT, ∀ (b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
      expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) (fun R =>
          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n f R
            true b A (q.eval n)) =
        expect (sample (B.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf false) b f)
              (B.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                ((qRed q).eval n) r) none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ q ettDin ettDout pkDin pkDout (.const 1)
    (bHandler q)
  obtain ⟨B', hc, -, -, hB'⟩ := NUPPT.exists_comp B
    (pre := fun y => pairEncode [] y) (post := id)
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id) polyTimeComputable_id
  refine ⟨B', fun b n f => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  have hQ : q.eval n * (bHandler q).perCall.eval n + (bHandler q).finCall.eval n =
      (qRed q).eval n := by
    rw [bHandler_perCall, bHandler_finCall, PRFGame.qRed_eval]
  have hout : (bHandler q).outLen.eval n = 1 := by rw [bHandler_outLen, PolyExpr.eval_const]
  -- `B'` on the empty input history is `B` on the input `[]`.
  have hB'B : ∀ r : B.Coins n,
      B'.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
          ((qRed q).eval n) (NUPPT.coinsCongr hc.symm n r) =
        B.toCompOn (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
          ((qRed q).eval n) [] r := by
    intro r
    rw [NUPPT.toComp_eq, NUPPT.toCompOn_eq]
    congr 1
    funext hist
    rw [NUPPT.runAt_coinsCongr, hB', id_eq, ← NUPPT.runAt_eq]
  -- `B'`'s coins are a tape word and `A`'s coins.
  rw [← expect_sample_equiv (NUPPT.coinsCongr hc.symm n)]
  simp only [hB'B]
  rw [← expect_sample_equiv φ₂, ChallengeSim.expect_sample_prod,
    ← expect_sample_equiv (bHSeed q n)]
  conv_rhs => rw [expect_sample_comm]
  rw [← expect_sample_equiv φ₀]
  simp only [ettAcc_eq]
  rw [expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  -- One run of `B'` is the handler's simulation of `A`, composed with the CPA oracles.
  have hrun : ∀ W : Fin (q.eval n * (2 * n)) → Bool,
      expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf false) b f)
          (B.toCompOn (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
            ((qRed q).eval n) [] (φ₂ (bHSeed q n W, φ₀ r))) none)
          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
        expect (simulate (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            (ettCt.eval n) n f b (bTapes q n W))
            (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
              ((PolyExpr.const 1).eval n)) n (q.eval n) [] (φ₀ r)) ((none, []), 0))
          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro W
    rw [expect_toCompOn_outLen _ B n _ [] _ none hout.symm
        (fun p => if p.1.headD false = true then (1 : ℝ) else 0), ← hQ,
      ← hφ₂ [] (bHSeed q n W) (φ₀ r), bHandler_advInput, simulate_bind, simulate_comp,
      OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, bHandler_finish, simulate_pure, expect_pure]
    rw [bHandler_init_hstate, show ((bHState q n 0 [] none, none) :
        (Fin ((bHandler q).stateLen.eval n) → Bool) × Option (Fin (ctP.eval n) → Bool)) =
        bAbs q n ((none, []), 0) from rfl,
      expect_simulate_abs_inv _ _ (bAbs q n) (bInv n) (fun s => s.2) (q.eval n)
        (fun i x s hP hs g => comp_bAbs q b n f [] W i x s hP hs g)
        (fun i x s hP _ => ettLazyTape_bInv b n f _ i x s hP) _ (q.eval n)
        (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
        ⟨le_rfl, fun e he => absurd he List.not_mem_nil⟩ (Nat.zero_add _).le]
    refine congrArg _ (funext fun p => ?_)
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, bHandler_outLen])]
  simp only [hrun, bTapes_eq]
  have hi0 : (fun i => (ettDin i).eval n) 0 = n := by
    show (ettDin 0).eval n = n
    rw [ettDin_zero, PolyExpr.eval_var]
  have hi2 : (fun i => (ettDin i).eval n) 2 = n + n := by
    show (ettDin 2).eval n = n + n
    rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
  rw [expect_sample_equiv (EnsembleLemmas.blocks (q.eval n) (2 * n)) (fun T =>
      expect (simulate (ettLazyTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n f b (AdaptiveCPA.extTape T))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) [] (φ₀ r)) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_ettLazyTape _ _ _ _ _ _ (q.eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
      (q.eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
    ← expect_ettImpl_lazy _ _ _ n f b (ettCt_eval n) hi0 hi2
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _ (none, [])
      (lInv_nil n f none)]
  refine congrArg _ (funext fun R => ?_)
  have htbl : ovr (tagTbl ((none, []) : LSt n (ettCt.eval n))) R = R := by
    rw [tagTbl_none_nil, ovr_nil]
  rw [htbl, hφ₀, keysL_nil]
  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n).symm _ _ _ _ A _ r

end TCSlib.Cryptography.Composability.ETTGame
