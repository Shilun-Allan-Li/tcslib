/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Transfer: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean`. -/
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
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Transfer: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From the CCA2 experiment to the experiment with a pad and a tag function

Generic transfer lemmas for step 1 of [PS10, Theorem 170.4]: a fixed-length private-key scheme
whose encryption with a key is `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩` with `c₁ = m ⊕ f(r)` and a uniform nonce `r`,
and whose decryption answers `⟨1, c₁ ⊕ f(r)⟩` on valid words (`validW g`) and `⊥` otherwise, has,
call by call, the oracles `ettImpl … f g false b` of the CCA2 experiment
(`expect_indImpl_ettImpl`); so the experiment `IND_b` is the experiment with `f` and `g`, averaged
over the key (`accept_indGame_eq`).

## Main results

* `ETTGame.expect_indImpl_ettImpl`: one call of `IND_b` has the law of `ettImpl`.
* `ETTGame.accept_indGame_eq`: the CCA2 experiment as the experiment with a pad and a tag
  function.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-- The challenge record of the experiment's state: `stRec s = s.1`. -/
def stRec {n d : ℕ} (s : St n d) : Option (Fin d → Bool) := s.1

/-- `stRec s = s.1`. -/
theorem stRec_eq {n d : ℕ} (s : St n d) : stRec s = s.1 := rfl

section Transfer

variable (S : FixedLengthScheme) (b : Bool) (n : ℕ) (key : List Bool)
  (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))

/-- **One call of `IND_b` under CCA2 with the key `key` has the law of `ettImpl` with `f` and `g`**,
for every function `G` of the answer and the record, for a scheme `S` whose encryption with `key`
is `encW f g` with the nonce `ν re` of a bijection `ν` (`henc`), whose decryption is `decL f` on
valid words and `⊥` otherwise (`hdec`), with `(6n + 4)`-bit ciphertexts:
`𝔼[G] (S.indImpl .cca2 b n key i x (stRec s)) = 𝔼[G ∘ (id × stRec)] (ettImpl … f g false b i x s)`.

**Proof sketch.** By the oracle (the `_onSpec` readers). Encryption and the first challenge
sample the coins of `Enc`, which are the nonce (`expect_sample_equiv ν`), and encrypt as `encW`;
the selected half is `msgOf` (`ofFn_splitHalf_fst`, `_snd`). Decryption refuses the record
(`refW`) and otherwise answers `decAnsW`; its coins and the experiment's nonce are unused
(`expect_const`). A repeated challenge returns the record. -/
theorem expect_indImpl_ettImpl (hct : S.ctLen.eval n = 6 * n + 4)
    (ν : S.enc.Coins n ≃ (Fin n → Bool))
    (henc : ∀ (m : Fin n → Bool) (re : S.enc.Coins n),
      List.ofFn (S.encryptAt n key m re) = encW f g (ν re) (List.ofFn m))
    (hdec : ∀ (w : List Bool) (rd : S.dec.Coins n),
      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
          (S.dec.runAt n (pairEncode key w) rd))) =
        if validW g w = true then decL f w else List.replicate (n + 1) false)
    (i : Fin 3) (x : (S.indSpec n).dom i) (s : St n (S.ctLen.eval n))
    (G : (S.indSpec n).rng i × Option (Fin (S.ctLen.eval n) → Bool) → ℝ) :
    expect (S.indImpl .cca2 b n key i x (stRec s)) G =
      expect (ettImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n f g false b i x s)
        (fun p => G (p.1, stRec p.2)) := by
  have hlenEnc : ∀ (r : Fin n → Bool) {m : List Bool}, m.length = n →
      (encW f g r m).length = S.ctLen.eval n := fun r m hm => by rw [length_encW f g r hm, hct]
  rw [ettImpl_apply, expect_bind]
  match i, x with
  | 0, m =>
    rw [S.indImpl_enc_onSpec, expect_bind, ← expect_sample_equiv ν]
    refine congrArg _ (funext fun re => ?_)
    rw [expect_pure, expect_pure, ettStep_enc, stRec_eq, stRec_eq]
    have hm : List.ofFn (cast (S.indSpec_encDom n) m) = List.ofFn m :=
      ofFn_cast (S.inLens_zero n) _ m
    have hm' : cast (S.indSpec_encDom n) m = padFin n (List.ofFn m) :=
      List.ofFn_injective (by rw [hm, ofFn_padFin_of_length (by
        rw [List.length_ofFn, S.inLens_zero])])
    have hmn : (List.ofFn m).length = n := by rw [List.length_ofFn, S.inLens_zero]
    congr 2
    refine List.ofFn_injective ?_
    rw [ofFn_cast (S.outLens_zero n).symm _ _, hm', henc, ofFn_padFin_of_length hmn,
      ofFn_padFin_of_length (by rw [hlenEnc _ hmn, S.outLens_zero])]
  | 1, c =>
    rw [S.indImpl_dec_onSpec, FixedLengthScheme.decOpen_cca2, Bool.true_and]
    have hc : List.ofFn (cast (S.indSpec_decDom n) c) = List.ofFn c :=
      ofFn_cast (S.inLens_one n) _ c
    have href : (!decide (s.1 = some (cast (S.indSpec_decDom n) c))) =
        !refW s.1 (List.ofFn c) := by
      obtain ⟨o, T⟩ := s
      cases o with
      | none => simp [refW_none]
      | some c' =>
        rw [refW_some]
        simp only [Option.some.injEq]
        congr 1
        exact decide_eq_decide.2 ⟨fun h => by rw [h, hc],
          fun h => List.ofFn_injective (h.trans hc.symm)⟩
    simp only [expect_pure, ettStep_dec, stRec_eq]
    rw [expect_const]
    by_cases hr : refW s.1 (List.ofFn c) = true
    · rw [if_neg (by rw [href, hr]; exact Bool.false_ne_true), expect_pure, decAnsW_eq,
        if_neg (by rw [hr]; simp), padFin_nil]
    · rw [Bool.not_eq_true] at hr
      rw [if_pos (by rw [href, hr]; rfl), expect_bind]
      refine (congrArg _ (funext fun rd => ?_)).trans (expect_const _ _)
      rw [expect_pure]
      congr 2
      refine List.ofFn_injective ?_
      rw [ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAnsW_eq, hr]
      simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true]
      by_cases hv : validW g (List.ofFn c) = true
      · rw [if_pos hv, if_pos hv]
        have hlen : (decL f (List.ofFn c)).length = S.outLens n 1 := by
          rw [validW_eq, Bool.and_eq_true, wfW_eq, Bool.and_eq_true, decide_eq_true_eq,
            decide_eq_true_eq] at hv
          rw [decL_eq, List.length_cons, List.length_zipWith, List.length_ofFn, hv.1.2,
            Nat.min_self, S.outLens_one]
        rw [ofFn_padFin_of_length hlen]
      · rw [if_neg hv, if_neg hv, padFin_nil, ofFn_zeroBits, S.outLens_one]
  | 2, mm =>
    have hmm : List.ofFn (cast (S.indSpec_challengeDom n) mm) = List.ofFn mm :=
      ofFn_cast (S.inLens_two n) _ mm
    have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
      have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, S.inLens_two]
      rw [AdaptiveCPA.msgOf_eq]
      cases b <;> simp [this]
    have hsel : (if b then (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).1) =
        padFin n (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
      refine List.ofFn_injective ?_
      rw [ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
      cases b
      · exact FixedLengthScheme.ofFn_splitHalf_fst _
      · exact FixedLengthScheme.ofFn_splitHalf_snd _
    obtain ⟨o, T⟩ := s
    cases o with
    | some c =>
      rw [stRec_eq, S.indImpl_challenge_repeat_onSpec, expect_pure]
      simp only [expect_pure, ettStep_challenge_some, stRec_eq]
      rw [expect_const]
      congr 2
      refine List.ofFn_injective ?_
      rw [ofFn_cast (S.outLens_two n).symm _ _,
        ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
    | none =>
      rw [stRec_eq, S.indImpl_challenge_none_onSpec, expect_bind, ← expect_sample_equiv ν]
      refine congrArg _ (funext fun re => ?_)
      simp only [expect_pure, ettStep_challenge_none, stRec_eq]
      have henc' : List.ofFn (S.encryptAt n key (if b then (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).1) re) =
          encW f g (ν re) (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
        rw [hsel, henc, ofFn_padFin_of_length hmsg]
      congr 2
      · refine List.ofFn_injective ?_
        rw [ofFn_cast (S.outLens_two n).symm _ _, henc',
          ofFn_padFin_of_length (by rw [hlenEnc _ hmsg, S.outLens_two])]
      · congr 1
        refine List.ofFn_injective ?_
        rw [henc', ofFn_padFin_of_length (hlenEnc _ hmsg)]

/-- **The CCA2 experiment is the experiment with a pad and a tag function** (step 1 of
[PS10, Thm 170.4], transfer): for a scheme `S` whose encryption with the key generated from the
coins `rg` is `encW (fk rg) (gk rg)` with nonces `ν re`, and whose decryption is `decL (fk rg)` on
valid words for `gk rg` and `⊥` otherwise, with `(6n + 4)`-bit ciphertexts,
`Pr[IND_b = 1] = 𝔼_{rg} 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … (fk rg) (gk rg) false b) …]`.

**Proof sketch.** `FixedLengthScheme.indGame_eq` and `accept_eq`; for each key and coins, the
oracles of `IND_b` have the laws of `ettImpl` through the record (`expect_indImpl_ettImpl`,
`expect_simulate_abs` with a constant counter); the game's codec is a bit codec
(`FixedLengthScheme.indCodec_eq_bitCodec`) and its bit is the head of the output
(`headD_ofFn_one`). -/
theorem accept_indGame_eq (A : NUPPT) (Q : ℕ) (hct : S.ctLen.eval n = 6 * n + 4)
    (fk : S.gen.Coins n → (Fin n → Bool) → (Fin n → Bool))
    (gk : S.gen.Coins n → (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (ν : S.enc.Coins n ≃ (Fin n → Bool))
    (henc : ∀ (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      List.ofFn (S.encryptAt n (S.gen.runAt n [] rg) m re) =
        encW (fk rg) (gk rg) (ν re) (List.ofFn m))
    (hdec : ∀ (rg : S.gen.Coins n) (w : List Bool) (rd : S.dec.Coins n),
      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
          (S.dec.runAt n (pairEncode (S.gen.runAt n [] rg) w) rd))) =
        if validW (gk rg) w = true then decL (fk rg) w else List.replicate (n + 1) false) :
    accept (S.indGame .cca2 A Q b n) =
      expect (sample (S.gen.Coins n)) fun rg => expect (sample (A.Coins n)) fun r =>
        expect (simulate (ettImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n (fk rg) (gk rg)
            false b) (A.toComp (bitCodec (S.inLens n) (S.outLens n) 1) n Q r) (none, []))
          (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  rw [accept_eq, FixedLengthScheme.indGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, FixedLengthScheme.indCodec_eq_bitCodec]
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
    funext res
    rw [prob_pure, headD_ofFn_one]
  rw [h1]
  exact expect_simulate_abs _ _ stRec (fun _ => 0) (Q + 1)
    (fun i x s _ G => expect_indImpl_ettImpl S b n _ (fk rg) (gk rg) hct ν (henc rg) (hdec rg)
      i x s G)
    (fun i x s _ => (OracleComp.allOutputs_true _).mono fun _ _ => Nat.zero_le _)
    _ Q (A.toComp_costBoundedBy _ n Q r) (none, []) (by simp) _

end Transfer

end TCSlib.Cryptography.Composability.ETTGame
