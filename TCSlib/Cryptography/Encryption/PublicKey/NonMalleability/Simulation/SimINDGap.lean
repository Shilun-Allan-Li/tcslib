/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIM-NME′ implies non-malleability: the advantage

Direction SIM ⇒ IND of [PS10, Theorem 174.8] ([PSV07, Corollary 1], at one message). With the
sampler `halfSamp S` (parameter `⟨m₀, m₁⟩`, output `m_β`), the SIM adversary `A'` of T2's handler
`copyHandler` and any simulator, the distinguishers `D' = tailDist S D` and `D'' = halfDist S`
satisfy, at every `n`,
* in the real experiment, `2·Pr[D' = 1] − Pr[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`
  (`real_gap`);
* in the ideal experiment, `2·Pr[D' = 1] = Pr[D'' = 1]` (`ideal_gap`).

So `NM`'s advantage is at most `2·adv(D') + adv(D'')`.

## Main results

* `NMSim.realAcc_copyHandler`: the SIM adversary's real experiment is `A`'s.
* `NMSim.real_gap`, `NMSim.ideal_gap`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Corollary 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

variable (S : FixedLengthPKScheme)

/-! ### Linear algebra of expectations -/

/-- Changing a machine's output length along `d = d'` keeps the law of its output as a list. -/
private theorem expect_toCompOn_outLen {k : ℕ} {ins outs : Fin k → ℕ} {σ : Type}
    (O : QueryImpl (bitSpec ins outs) σ unifSpec) (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (s : σ) {d d' : ℕ} (hd : d = d') (G : List Bool × σ → ℝ) :
    expect (simulate O (A.toCompOn (bitCodec ins outs d) n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (A.toCompOn (bitCodec ins outs d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  subst hd
  rfl

/-- The pointwise identity `2·((A₀ + A₁)/2) − (B₀ + B₁)/2 = C₁ − C₀` passes to expectations. -/
private theorem lin_expect {α : Type} (c : ProbComp α) (A₀ A₁ B₀ B₁ C₀ C₁ : α → ℝ)
    (h : ∀ x, 2 * ((A₀ x + A₁ x) / 2) - (B₀ x + B₁ x) / 2 = C₁ x - C₀ x) :
    2 * ((expect c A₀ + expect c A₁) / 2) - (expect c B₀ + expect c B₁) / 2 =
      expect c C₁ - expect c C₀ := by
  have hC : expect c (fun x => C₁ x - C₀ x) =
      expect c (fun x => (A₀ x + A₁ x) - 2⁻¹ * (B₀ x + B₁ x)) :=
    congrArg _ (funext fun x => by linarith [h x])
  rw [← expect_sub, hC, expect_sub, expect_const_mul, expect_add, expect_add]
  ring

/-- `2·f − g = h₁ − h₀` pointwise passes to expectations. -/
private theorem lin_expect' {α : Type} (c : ProbComp α) (f g h₀ h₁ : α → ℝ)
    (h : ∀ x, 2 * f x - g x = h₁ x - h₀ x) :
    2 * expect c f - expect c g = expect c h₁ - expect c h₀ := by
  rw [← expect_const_mul, ← expect_sub, ← expect_sub]
  exact congrArg _ (funext h)

/-- **The coupling in expectation:** if `T₀(e c) + T₁(e c) − (H₀ b + H₁ b)/2 = V₁ c − V₀ c` for all
`c`, `b`, then `2·((𝔼T₀ + 𝔼T₁)/2) − (𝔼H₀ + 𝔼H₁)/2 = 𝔼V₁ − 𝔼V₀` (uniform samples; `e` a bijection). -/
private theorem lin_sample {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [Fintype γ] [Nonempty γ] (T₀ T₁ : α → ℝ) (H₀ H₁ : β → ℝ) (V₀ V₁ : γ → ℝ) (e : γ ≃ α)
    (h : ∀ c b, T₀ (e c) + T₁ (e c) - (H₀ b + H₁ b) / 2 = V₁ c - V₀ c) :
    2 * ((expect (sample α) T₀ + expect (sample α) T₁) / 2) -
        (expect (sample β) H₀ + expect (sample β) H₁) / 2 =
      expect (sample γ) V₁ - expect (sample γ) V₀ := by
  obtain ⟨c₀⟩ := (inferInstance : Nonempty γ)
  obtain ⟨b₀⟩ := (inferInstance : Nonempty β)
  have hH : expect (sample β) (fun b => H₀ b + H₁ b) =
      expect (sample β) (fun _ => 2 * (T₀ (e c₀) + T₁ (e c₀) - (V₁ c₀ - V₀ c₀))) :=
    congrArg _ (funext fun b => by linarith [h c₀ b])
  have hT : expect (sample γ) (fun c => T₀ (e c) + T₁ (e c) - (V₁ c - V₀ c)) =
      expect (sample γ) (fun _ => (H₀ b₀ + H₁ b₀) / 2) :=
    congrArg _ (funext fun c => by linarith [h c b₀])
  rw [expect_sub, expect_add, expect_sub, expect_const,
    expect_sample_equiv e T₀, expect_sample_equiv e T₁] at hT
  rw [expect_add, expect_const] at hH
  linarith [h c₀ b₀]

/-! ### The real experiment -/

/-- **The SIM adversary's real experiment is `A`'s:** for T2's machine `A'` of
`copyHandler S pl hl outL` (coin bijection `φ`, budget `K`), with `A`'s output length `dα(n) =
outL(n) = r·ctLen(n) + sl`, the real acceptance rate of `A'` is that of `A`'s run (on T2's
lengths) against the same oracle.

**Proof sketch.** Reindex `A'`'s coins by `φ` (`expect_sample_equiv`, `expect_sample_prod`), replace
`A'`'s run by `A`'s (`simulate_copyHandler_machine`), and drop the unread seed (`expect_const`). -/
theorem realAcc_copyHandler (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A A' : NUPPT) (q dα outL : PolyExpr) (K r sl : ℕ) (X : NUPPT)
    (n : ℕ) (hd : dα.eval n = outL.eval n) (hr : outL.eval n = r * S.ctLen.eval n + sl)
    (hK : K = q.eval n * (copyHandler S pl hl outL).perCall.eval n +
      (copyHandler S pl hl outL).finCall.eval n)
    (φ : (Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool) × A.Coins n ≃ A'.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((copyHandler S pl hl outL).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (dα.eval n)) n (q.eval n) ((copyHandler S pl hl outL).advInput n z ω) r)
          ((copyHandler S pl hl outL).init n)).bind
          (fun res => (copyHandler S pl hl outL).finish n z ω res.2 res.1) =
        A'.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n) (fun j => (snmDout S hl j).eval n)
          ((copyHandler S pl hl outL).outLen.eval n)) n
          (q.eval n * (copyHandler S pl hl outL).perCall.eval n +
            (copyHandler S pl hl outL).finCall.eval n) z (φ (ω, r))) :
    realAcc S atk samp pl hl hist A' K r sl X n =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (samp.Coins n)) fun ρ =>
      expect (sample (A.Coins n)) fun rA =>
      expect (sample (X.Coins n)) fun rX =>
      expect (simulate (rImpl S atk false samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (dα.eval n)) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := by
  subst hK
  rw [realAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  rw [← expect_sample_equiv φ, expect_sample_prod]
  refine Eq.trans ?_
    (expect_const (sample (Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool)) _)
  refine congrArg _ (funext fun ω => congrArg _ (funext fun rA => congrArg _ (funext fun rX => ?_)))
  have hout : r * S.ctLen.eval n + sl = (copyHandler S pl hl outL).outLen.eval n := by
    rw [copyHandler_outLen, hr]
  refine (expect_toCompOn_outLen _ A' n _ _ _ none hout fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ p.1 p.2) rX =
      true then (1 : ℝ) else 0).trans ?_
  rw [simulate_copyHandler_machine S A A' q dα pl hl outL n hd φ hφ, expect_bind]
  refine congrArg _ (funext fun p => ?_)
  rw [expect_pure]
  dsimp only
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, copyHandler_outLen, hd])]

/-- **The SIM adversary's handler** for an NM adversary with `ℓ` output ciphertexts: `copyHandler` on
the real experiment's oracles with the parameter `⟨m₀, m₁⟩` (`pl = msgLen + msgLen`), the empty
history and `ℓ·ctLen + 0` output bits (`r = ℓ`, `sl = 0`). -/
def simHandler (ℓ : PolyExpr) :
    InteractiveHandler 2 (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) 2
      (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) :=
  copyHandler S (S.msgLen.add S.msgLen) (.const 0) ((ℓ.mul S.ctLen).add (.const 0))

/-- `simHandler S ℓ = copyHandler S (msgLen + msgLen) 0 (ℓ·ctLen + 0)`. -/
theorem simHandler_eq (ℓ : PolyExpr) :
    simHandler S ℓ = copyHandler S (S.msgLen.add S.msgLen) (.const 0) ((ℓ.mul S.ctLen).add (.const 0)) :=
  rfl

/-- **The real experiment with the sampler `⟨m₀, m₁⟩ ↦ m_β`** is the average over `β` of `A`'s runs
`runB … β` (with any `ρ'`), the views read with the coin `β`. -/
private theorem realAcc_half (atk : Attack) (A A' : NUPPT) (q ℓ : PolyExpr) (K : ℕ) (X : NUPPT)
    (n : ℕ) (ρ' : (halfSamp S).Coins n)
    (hK : K = q.eval n * (simHandler S ℓ).perCall.eval n + (simHandler S ℓ).finCall.eval n)
    (φ : (Fin ((simHandler S ℓ).seedLen.eval n) → Bool) × A.Coins n ≃ A'.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((simHandler S ℓ).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((simHandler S ℓ).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) ((ℓ.mul S.ctLen).eval n)) n (q.eval n)
            ((simHandler S ℓ).advInput n z ω) r)
          ((simHandler S ℓ).init n)).bind
          (fun res => (simHandler S ℓ).finish n z ω res.2 res.1) =
        A'.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n)
          ((simHandler S ℓ).outLen.eval n)) n
          (q.eval n * (simHandler S ℓ).perCall.eval n +
            (simHandler S ℓ).finCall.eval n) z (φ (ω, r))) :
    realAcc S atk (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) A' K (ℓ.eval n)
        ((PolyExpr.const 0).eval n) X n =
      expect (sample (S.gen.Coins n)) fun rg =>
        ((expect (sample (A.Coins n)) fun r => expect (sample (X.Coins n)) fun rX =>
          expect (runB S atk A (q.eval n) (ℓ.eval n) n (fun _ => []) (pairFstD (S.gen.runAt n [] rg))
            (pairSndD (S.gen.runAt n [] rg)) r ρ' false) fun p =>
            if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
              (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm false) (List.ofFn p.1) p.2) rX =
              true then 1 else 0) +
        (expect (sample (A.Coins n)) fun r => expect (sample (X.Coins n)) fun rX =>
          expect (runB S atk A (q.eval n) (ℓ.eval n) n (fun _ => []) (pairFstD (S.gen.runAt n [] rg))
            (pairSndD (S.gen.runAt n [] rg)) r ρ' true) fun p =>
            if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
              (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm true) (List.ofFn p.1) p.2) rX =
              true then 1 else 0)) / 2 := by
  have hd : (ℓ.mul S.ctLen).eval n = ((ℓ.mul S.ctLen).add (.const 0)).eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const, Nat.add_zero]
  have hr : ((ℓ.mul S.ctLen).add (.const 0)).eval n =
      ℓ.eval n * S.ctLen.eval n + (PolyExpr.const 0).eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hlen : (ℓ.mul S.ctLen).eval n = ℓ.eval n * S.ctLen.eval n := PolyExpr.eval_mul _ _ _
  rw [realAcc_copyHandler S atk _ _ _ _ A A' q (ℓ.mul S.ctLen) _ K _ _ X n hd hr hK φ hφ]
  refine congrArg _ (funext fun rg => ?_)
  rw [expect_sample_halfCoins]
  have hβ : ∀ β : Bool,
      (expect (sample (A.Coins n)) fun rA => expect (sample (X.Coins n)) fun rX =>
        expect (simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0)
            (fun _ => []) n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
            ((halfCoins S n).symm β) ((halfCoins S n).symm β) none)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) ((ℓ.mul S.ctLen).eval n)) n (q.eval n)
            (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
          if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm β) (List.ofFn p.1) p.2) rX =
            true then 1 else 0) =
      expect (sample (A.Coins n)) fun r => expect (sample (X.Coins n)) fun rX =>
        expect (runB S atk A (q.eval n) (ℓ.eval n) n (fun _ => []) (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) r ρ' β) fun p =>
          if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm β) (List.ofFn p.1) p.2) rX =
            true then 1 else 0 := by
    intro β
    refine congrArg _ (funext fun rA => congrArg _ (funext fun rX => ?_))
    rw [runB_eq, rImpl_false_coins S atk _ _ _ _ n _ _ _ _ ρ']
    exact expect_toCompOn_outLen _ A n _ _ rA none hlen fun p =>
      if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
        (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm β) p.1 p.2) rX = true
        then (1 : ℝ) else 0
  rw [← hβ false, ← hβ true]

/-- **The real experiment, `D'` against `D''`:** for the SIM adversary `A'` (T2's machine of
`simHandler S ℓ`, budget `K`),
`2·Pr_real[D' = 1] − Pr_real[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`.

**Proof sketch.** Both acceptance rates are averages over `β` of `A`'s runs `runB … β`
(`realAcc_half`), and `NM_β` is the run with coin `β` (`accept_nmGame_eq_rImpl`). Pointwise in
the keys, `A`'s coins and the distinguishers' coins this is `real_identity`; it passes to the
expectations (`lin_expect'`, `lin_expect`, `lin_sample`, with `D`'s coins carried to `D'`'s). -/
theorem real_gap (atk : Attack) (A A' : NUPPT) (q ℓ : PolyExpr) (K : ℕ) (D : NUPPT) (n : ℕ)
    (hK : K = q.eval n * (simHandler S ℓ).perCall.eval n + (simHandler S ℓ).finCall.eval n)
    (φ : (Fin ((simHandler S ℓ).seedLen.eval n) → Bool) × A.Coins n ≃ A'.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((simHandler S ℓ).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((simHandler S ℓ).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) ((ℓ.mul S.ctLen).eval n)) n (q.eval n)
            ((simHandler S ℓ).advInput n z ω) r)
          ((simHandler S ℓ).init n)).bind
          (fun res => (simHandler S ℓ).finish n z ω res.2 res.1) =
        A'.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n)
          ((simHandler S ℓ).outLen.eval n)) n
          (q.eval n * (simHandler S ℓ).perCall.eval n +
            (simHandler S ℓ).finCall.eval n) z (φ (ω, r))) :
    2 * realAcc S atk (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) A' K (ℓ.eval n)
        ((PolyExpr.const 0).eval n) (tailDist S D) n -
      realAcc S atk (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) A' K (ℓ.eval n)
        ((PolyExpr.const 0).eval n) (halfDist S) n =
      accept (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) -
        accept (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n) := by
  rw [realAcc_half S atk A A' q ℓ K _ n ((halfCoins S n).symm false) hK φ hφ,
    realAcc_half S atk A A' q ℓ K _ n ((halfCoins S n).symm false) hK φ hφ,
    accept_nmGame_eq_rImpl S atk A (q.eval n) (ℓ.eval n) D true n (fun _ => [])
      ((halfCoins S n).symm false),
    accept_nmGame_eq_rImpl S atk A (q.eval n) (ℓ.eval n) D false n (fun _ => [])
      ((halfCoins S n).symm false)]
  refine lin_expect' _ _ _ _ _ fun rg => ?_
  refine lin_expect _ _ _ _ _ _ _ fun r => ?_
  refine lin_sample _ _ _ _ _ _ (NUPPT.coinsCongr (tailDist_coins S D).symm n) fun rD ρ'' => ?_
  exact real_identity S atk A (q.eval n) (ℓ.eval n) n (fun _ => []) _ _ r _ D rD ρ''

/-! ### The ideal experiment -/

/-- `D''` reads only the parameter: on the ideal experiment's views it ignores the sampler's
coin. -/
private theorem halfDist_idealView_coin (n r : ℕ) (sk w : List Bool)
    (sa : Option (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) (ρ'' : (halfDist S).Coins n)
    (β : Bool) :
    (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r sk
        ((halfCoins S n).symm β) w sa) ρ'' =
      (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r sk
        ((halfCoins S n).symm false) w sa) ρ'' := by
  have hA : (List.ofFn (sa.getD (zeroBits _))).length = S.msgLen.eval n + S.msgLen.eval n := by
    rw [List.length_ofFn, PolyExpr.eval_add]
  rw [idealView_eq, idealView_eq, List.append_assoc (List.ofFn _ ++ List.ofFn _),
    List.append_assoc (List.ofFn _ ++ List.ofFn _), halfDist_blocks S n _ _ _ hA List.length_ofFn,
    halfDist_blocks S n _ _ _ hA List.length_ofFn]

/-- **The ideal experiment, `D'` against `D''`:** for every simulator,
`2·Pr_ideal[D' = 1] = Pr_ideal[D'' = 1]`.

**Proof sketch.** With the empty history the oracle ignores the sampler's coin (`histImpl_coins`),
so the coin `β` can be drawn after the simulator's run (`expect_sample_comm`,
`expect_sample_halfCoins`). Pointwise, `D'(β = 0) + D'(β = 1) = D''` (`ideal_identity`), and `D''`
ignores `β` (`halfDist_idealView_coin`). -/
theorem ideal_gap (Sim D : NUPPT) (r n : ℕ) :
    2 * idealAcc S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) Sim r
        ((PolyExpr.const 0).eval n) (tailDist S D) n =
      idealAcc S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) Sim r
        ((PolyExpr.const 0).eval n) (halfDist S) n := by
  have hhl : (PolyExpr.const 0).eval n = 0 := PolyExpr.eval_const _ _
  have hI : ∀ X : NUPPT, idealAcc S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => [])
      Sim r ((PolyExpr.const 0).eval n) X n =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (Sim.Coins n)) fun rS =>
      expect (sample (X.Coins n)) fun rX =>
      expect (simulate (histImpl S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) n
          ((halfCoins S n).symm false))
        (Sim.toCompOn (bitCodec (fun _ => (S.msgLen.add S.msgLen).eval n)
          (fun _ => (PolyExpr.const 0).eval n) (r * (S.ctLen.eval n + 1) + (PolyExpr.const 0).eval n))
          n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
        2⁻¹ * ((if X.distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm false) (List.ofFn p.1) p.2) rX =
            true then 1 else 0) +
          (if X.distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm true) (List.ofFn p.1) p.2) rX =
            true then 1 else 0)) := by
    intro X
    rw [idealAcc_eq]
    refine congrArg _ (funext fun rg => ?_)
    rw [expect_sample_comm]
    refine congrArg _ (funext fun rS => ?_)
    rw [expect_sample_comm]
    refine congrArg _ (funext fun rX => ?_)
    rw [expect_sample_halfCoins, histImpl_coins S _ _ _ _ n ((halfCoins S n).symm true)
      ((halfCoins S n).symm false) hhl, ← expect_add, div_eq_inv_mul, ← expect_const_mul]
  rw [hI, hI, ← expect_const_mul]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_const_mul]
  refine congrArg _ (funext fun rS => ?_)
  symm
  refine Eq.trans (congrArg _ (funext fun ρ'' => ?_)) (expect_const (sample _) _)
  rw [← expect_sample_equiv (NUPPT.coinsCongr (tailDist_coins S D).symm n), ← expect_const_mul]
  symm
  refine Eq.trans (congrArg _ (funext fun rD => ?_)) (expect_const (sample _) _)
  rw [← expect_const_mul]
  refine congrArg _ (funext fun p => ?_)
  have hw : (List.ofFn p.1).length = r * (S.ctLen.eval n + 1) := by
    rw [List.length_ofFn, hhl, Nat.add_zero]
  have hid := ideal_identity S D n r (pairSndD (S.gen.runAt n [] rg)) (List.ofFn p.1) p.2 rD ρ'' hw
  rw [halfDist_idealView_coin S n r _ _ _ ρ'' true]
  linarith

end TCSlib.Cryptography.Composability.NMSim
