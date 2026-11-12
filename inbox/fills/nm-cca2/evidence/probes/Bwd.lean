import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

open AdaptiveCPA NMCCA2 ProbComp ChallengeSim

/-! ### (⇐) The non-malleability adversary built from a CCA2 adversary -/

/-- A two-block concatenation: for `k = 2`, `(List.ofFn f).flatten = f 0 ++ f 1`. -/
private theorem flatten_ofFn_two {k : ℕ} (hk : k = 2) (f : Fin k → List Bool) :
    (List.ofFn f).flatten = f ⟨0, by omega⟩ ++ f ⟨1, by omega⟩ := by
  subst hk
  simp [List.ofFn_succ]

/-- **The distinguisher recovers the guess.** Let the reduction output the ciphertexts
`c₁ = encCt … g true` (an encryption of `g^m`) and `c₂ = encCt … g false` (of `(¬g)^m`) under a
generated key, with `m = msgLen(n) > 0`. Then for every recorded challenge `st`, the distinguisher's
verdict on the experiment's output `S.nmOutput sk st (c₁ ‖ c₂)` is `g`.

**Proof sketch.** By correctness `c₁` decrypts to `g^m` and `c₂` to `(¬g)^m` (`S.correct`, with
`S.enc_length` for the padding), so `c₁ ≠ c₂` (their messages differ at bit `0`), and `st` copies
at most one of them. If `st ≠ some c₁` the first decryption is valid (`guessBit_valid`); otherwise
the first is `⊥` and the second valid (`guessBit_refused`). -/
private theorem guessDist_nmOutput (n : ℕ) (hm : 0 < S.msgLen.eval n) (rg : S.gen.Coins n)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (g : Bool)
    (st : Option (Fin (S.ctLen.eval n) → Bool)) (ρ : guessDist.Coins n) :
    guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) st
      (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n)
        (encCt S n (pairFstD (S.gen.runAt n [] rg)) ω g true ++
          encCt S n (pairFstD (S.gen.runAt n [] rg)) ω g false))) ρ = g := by
  set pk := pairFstD (S.gen.runAt n [] rg)
  set sk := pairSndD (S.gen.runAt n [] rg)
  set c₁ := encCt S n pk ω g true
  set c₂ := encCt S n pk ω g false
  have h2 : (PolyExpr.const 2).eval n = 2 := PolyExpr.eval_const _ _
  -- The honest ciphertexts and their decryptions.
  have hc : ∀ β, encCt S n pk ω g β = S.enc.runAt n (pairEncode pk (List.ofFn
      fun _ : Fin (S.msgLen.eval n) => if β then g else !g)) (encTape S n ω β) := fun β => by
    rw [encCt_eq, EnsembleLemmas.padL_eq, List.take_append_of_le_length (by rw [S.enc_length]),
      List.take_of_length_le (by rw [S.enc_length])]
  have hlen : ∀ β, (encCt S n pk ω g β).length = S.ctLen.eval n := fun β => by
    rw [encCt_eq, EnsembleLemmas.length_padL]
  have hdec : ∀ β, decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (encCt S n pk ω g β))) =
      some fun _ => if β then g else !g := fun β => by
    rw [hc]
    exact S.correct n _ rg (encTape S n ω β)
  -- The two blocks of the output.
  set W := padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) (c₁ ++ c₂)
  have hW : List.ofFn W = c₁ ++ c₂ := GGMRed.ofFn_padFin_of_length (by
    rw [List.length_append, hlen, hlen, h2]; omega)
  have hblk : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool), (i : ℕ) = (if β then 0 else 1) →
      List.ofFn (S.nthCt W i) = encCt S n pk ω g β := by
    intro i β hi
    rw [ofFn_nthCt, hW, hi]
    cases β
    · rw [if_neg Bool.false_ne_true, Nat.one_mul, List.drop_left' (hlen true),
        List.take_of_length_le (by rw [hlen])]
    · rw [if_pos rfl, Nat.zero_mul, List.drop_zero, List.take_left' (hlen true)]
  have hdecB : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool),
      (i : ℕ) = (if β then 0 else 1) →
      decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn (S.nthCt W i)))) =
        some fun _ => if β then g else !g := fun i β hi => by
    rw [hblk i β hi]
    exact hdec β
  -- The output is the two decryptions.
  have i₀ : (0 : ℕ) < (PolyExpr.const 2).eval n := by rw [h2]; omega
  have i₁ : (1 : ℕ) < (PolyExpr.const 2).eval n := by rw [h2]; omega
  have hout : S.nmOutput sk st W = List.ofFn (S.nmDecrypt sk st (S.nthCt W ⟨0, i₀⟩)) ++
      List.ofFn (S.nmDecrypt sk st (S.nthCt W ⟨1, i₁⟩)) := by
    rw [nmOutput_eq]
    exact flatten_ofFn_two h2 _
  -- The two ciphertexts differ.
  have hne : S.nthCt W ⟨0, i₀⟩ ≠ S.nthCt W ⟨1, i₁⟩ := by
    intro h
    have e := (hdecB ⟨0, i₀⟩ true rfl).symm.trans (h ▸ hdecB ⟨1, i₁⟩ false rfl)
    have := congrFun (Option.some.inj e) ⟨0, hm⟩
    simp at this
  rw [guessDist_distinguisherL, hout]
  by_cases hs : st = some (S.nthCt W ⟨0, i₀⟩)
  · have hs' : st ≠ some (S.nthCt W ⟨1, i₁⟩) := fun h => hne (Option.some.inj (hs.symm.trans h))
    rw [S.nmDecrypt_eq, S.nmDecrypt_eq, if_pos hs, if_neg hs', hdecB ⟨1, i₁⟩ false rfl]
    simpa only [if_neg Bool.false_ne_true] using guessBit_refused hm g
  · rw [S.nmDecrypt_eq, if_neg hs, hdecB ⟨0, i₀⟩ true rfl]
    simpa only [if_pos rfl] using guessBit_valid hm g _


/-- **The reduction's experiment is the CCA2 game.** Let `B` be T2's machine for the handler
`encHandler S` (with its coin bijection `φ` at `n`), and `msgLen(n) > 0`. Then `B`'s experiment
`NM_b` with two output ciphertexts and the distinguisher `guessDist` accepts with the probability
of `A`'s CCA2 game `Ind_b`.

**Proof sketch.** Fix the keys. `B`'s coins are the handler's seed `ω` and `A`'s coins `r` (`φ`,
`expect_sample_equiv`, `expect_sample_prod`). For fixed `ω`, `r` and the distinguisher's coins,
transport `B`'s run to T2's codec (`nmCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`) and
replace it by the reduction (T2's equation `hφ`). The handler forwards
(`simulate_encHandler_impl`), so the run is `A`'s run against the CCA2 oracles, after which the
finalization outputs the two ciphertexts and keeps the recorded challenge (`simulate_bind`,
`encHandler_finish`). Whatever that challenge is, `guessDist` outputs `A`'s guess
(`guessDist_nmOutput`). Transport `A`'s run back to the game's codec (`indCodec_eq_bitCodec`). The
result does not depend on `ω` or on the distinguisher's coins (`expect_const`). -/
private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
    (hm : 0 < S.msgLen.eval n)
    (φ : (Fin ((encHandler S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((encHandler S).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((encHandler S).advInput n z ω) r)
          ((encHandler S).init n)).bind
          (fun res => (encHandler S).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((encHandler S).outLen.eval n)) n
          (q.eval n * (encHandler S).perCall.eval n + (encHandler S).finCall.eval n) z (φ (ω, r)))
    (b : Bool) :
    accept (S.nmGame .cca2 B
        (q.eval n * (encHandler S).perCall.eval n + (encHandler S).finCall.eval n)
        ((PolyExpr.const 2).eval n) guessDist b n) =
      accept (S.indGame .cca2 A (q.eval n) b n) := by
  have hd1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
  have hd2 : (encHandler S).outLen.eval n = (PolyExpr.const 2).eval n * S.ctLen.eval n := by
    rw [encHandler_outLen, PolyExpr.eval_add, PolyExpr.eval_const]
    omega
  rw [accept_eq, accept_eq, S.nmGame_eq, S.indGame_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind, ← expect_sample_equiv φ, expect_sample_prod]
  refine (congrArg _ (funext fun ω => ?_)).trans (expect_const _ _)
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  refine (congrArg _ (funext fun ρ => ?_)).trans (expect_const _ _)
  -- The reduction's side: transport to T2's codec and unfold the reduction.
  have h2 : (fun res : (Fin ((PolyExpr.const 2).eval n * S.ctLen.eval n) → Bool) ×
      Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (guessDist.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
        else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, nmCodec_eq_bitCodec, h2]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd2 _ B n _ _ _
    none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
      else 0)).symm.trans ?_
  rw [← hφ, encHandler_advInput, simulate_encHandler_impl, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, encHandler_finish]
  rw [simulate_bind, expect_bind]
  simp only [simulate_pure, expect_pure]
  -- The game's side: transport `A`'s run to T2's codec.
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if p.1.headD false = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [headD_ofFn_one]
  rw [prob_bind, indCodec_eq_bitCodec, h1]
  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _
    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if p.1.headD false = true then (1 : ℝ) else 0))
  refine congrArg _ (funext fun p => ?_)
  -- Pointwise: the distinguisher outputs `A`'s guess.
  have hw : List.ofFn (padFin ((encHandler S).outLen.eval n)
      (encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
        encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false)) =
      encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
        encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false :=
    GGMRed.ofFn_padFin_of_length (by
      rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
        EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
  dsimp only
  rw [hw, guessDist_nmOutput S n hm]

/-- **(⇐) of Theorem 175.9: CCA2 non-malleability implies CCA2 security**
[PS10, Theorem 175.9].

**Proof sketch.** Given `A` with budget `q`, T2 (`Games.exists_interactiveHandlerMachine`) makes
the handler `encHandler S` a machine `B`, with budget `q · 1 + 0`. Non-malleability for `B`, two
output ciphertexts and `guessDist` gives a negligible bound. At `n` with `msgLen(n) > 0`, `A`'s
CCA2 advantage equals that experiment's advantage (`accept_nmGame_encRed`). At `msgLen(n) = 0` the
two CCA2 games coincide (`indImpl_eq_of_msgLen_eq_zero`), so `A`'s advantage is `0`. -/
theorem indSecure_cca2_of_nmSecure_cca2 (h : S.NMSecure .cca2) : S.INDSecure .cca2 := by
  rw [INDSecure_iff]
  intro A q
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
    (acDout S) (.const 1) (encHandler S)
  obtain ⟨ε, hε, hbound⟩ := (S.NMSecure_iff .cca2).1 h B
    ((q.mul (encHandler S).perCall).add (encHandler S).finCall) (.const 2) guessDist
  refine ⟨ε, hε, fun n => ?_⟩
  have hn := hbound n
  by_cases hm : S.msgLen.eval n = 0
  · have hg : S.indGame .cca2 A (q.eval n) false n = S.indGame .cca2 A (q.eval n) true n := by
      rw [S.indGame_eq, S.indGame_eq]
      simp only [indImpl_eq_of_msgLen_eq_zero S .cca2 n _ _ hm]
    rw [hg, advantage_self]
    exact (advantage_nonneg _ _).trans hn
  · obtain ⟨φ, hφ⟩ := hB n
    have key := fun b => accept_nmGame_encRed S A B q n (Nat.pos_of_ne_zero hm) φ hφ b
    rw [PolyExpr.eval_add, PolyExpr.eval_mul] at hn
    rw [advantage_eq, ← key false, ← key true, ← advantage_eq]
    exact hn

theorem iff_test : S.INDSecure .cca2 ↔ S.NMSecure .cca2 :=
  ⟨S.nmSecure_cca2_of_indSecure_cca2, S.indSecure_cca2_of_nmSecure_cca2⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability
