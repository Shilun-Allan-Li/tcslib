/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction machine's acceptance and the simulator with drawn exponents

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). Fix the group described by `d = desc(κ, r)`, the
Decision BDH tuple `(g, X, Y, Z, T)` and the coins `ρ` of an adversary `A'` run through the handler
codec on the empty input. `runAccept … ρ U` is the indicator that `A'` outputs `1` when its
queries are answered by `drawStep` with the exponent of the `j`-th query read from a tape `U j`
(`ETTGame.tapeImpl`). Then:
* the machine of the handler theorem T1 for `handler` accepts the Decision BDH string with the
  average of `runAccept` over its coins and the tape of drawn exponents `j ↦ draw (block j)`
  (`expect_handlerMachine`);
* the simulator with fresh uniform exponents per query (`ETTGame.freshImpl` of `drawStep`), read
  on the game's oracle lengths (`Games.castImpl`), outputs `1` with the average of `runAccept`
  over a uniform tape of `q(κ)` exponents (`expect_castImpl_freshImpl`): coins in advance have
  the law of fresh coins (`ETTGame.expect_simulate_tapeImpl`);
* the two averages differ by at most `q(κ) · (1/2)^n` (`abs_expect_runAccept_sub_le`, from
  `abs_expect_draws_sub_le`: `runAccept` has values `0` and `1`, the run being deterministic).

## Main definitions

* `BB1Machine.runAccept` — the indicator of output `1` of the run with a tape of exponents.

## Main results

* `BB1Machine.runAccept_eq_zero_or_one`.
* `BB1Machine.expect_handlerMachine`, `BB1Machine.expect_castImpl_freshImpl`,
  `BB1Machine.abs_expect_runAccept_sub_le`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability TCSlib.Cryptography.Candidates

namespace BB1Machine

variable (G : BilinearGen) (ℓ : PolyExpr) (b : Bool) (q : PolyExpr) (A' : NUPPT) (κ : ℕ)
  (r : G.gen.Coins κ) (g X Y Z : (G.group κ (G.desc κ r)).G) (T : (G.group κ (G.desc κ r)).GT)

/-- **The run with a tape of exponents accepts**: `1` if `A'` (coins `ρ`, empty input, budget
`q(κ)`, the handler's codec) outputs the bit `1` when its queries are answered by `drawStep` with
the exponent of the `j`-th query read from the tape `U` (`ETTGame.tapeImpl`, extended beyond
`q(κ)` by `AdaptiveCPA.extTape`), from the empty state, and `0` otherwise (as an expectation). -/
noncomputable def runAccept (ρ : A'.Coins κ)
    (U : Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order) : ℝ :=
  ProbComp.expect (simulate (ETTGame.tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
      (drawStep G ℓ b κ (G.desc κ r) g X Y Z T) (AdaptiveCPA.extTape U))
      (A'.toCompOn (bitCodec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)
        ((PolyExpr.const 1).eval κ)) κ (q.eval κ) [] ρ) ((none, none), 0))
    fun p => if List.ofFn p.1 = [true] then 1 else 0

/-- `runAccept … ρ U` is the expectation of `[⟦output⟧ = [1]]` over the run of `A'` against
`drawStep` with the tape `extTape U`. -/
theorem runAccept_eq (ρ : A'.Coins κ)
    (U : Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order) :
    runAccept G ℓ b q A' κ r g X Y Z T ρ U =
      ProbComp.expect (simulate (ETTGame.tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
          (drawStep G ℓ b κ (G.desc κ r) g X Y Z T) (AdaptiveCPA.extTape U))
          (A'.toCompOn (bitCodec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)
            ((PolyExpr.const 1).eval κ)) κ (q.eval κ) [] ρ) ((none, none), 0))
        fun p => if List.ofFn p.1 = [true] then 1 else 0 :=
  rfl

/-- **The run with a tape is deterministic**, so `runAccept` is `0` or `1`
(`exists_simulate_tape_eq_pure`). -/
theorem runAccept_eq_zero_or_one (ρ : A'.Coins κ)
    (U : Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order) :
    runAccept G ℓ b q A' κ r g X Y Z T ρ U = 0 ∨ runAccept G ℓ b q A' κ r g X Y Z T ρ U = 1 := by
  obtain ⟨a, st, h⟩ := exists_simulate_tape_eq_pure G ℓ b κ (G.desc κ r) g X Y Z T
    (AdaptiveCPA.extTape U)
    (A'.toCompOn (bitCodec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)
      ((PolyExpr.const 1).eval κ)) κ (q.eval κ) [] ρ) ((none, none), 0)
  rw [runAccept_eq, h, ProbComp.expect_pure]
  by_cases ha : List.ofFn a = [true]
  · exact Or.inr (if_pos ha)
  · exact Or.inl (if_neg ha)

variable (O : G.Ops) (H : ArithmeticFP)

/-- **The machine of T1 accepts with the average of `runAccept` over drawn exponents**: if `B` with
the coin bijection `φ` realizes the handler `handler … b q` for `A'` (the conclusion of T1,
`Games.exists_handlerMachine`), then `B` accepts the Decision BDH string of `(g, X, Y, Z, T)` with
probability `𝔼_{ρ} 𝔼_{V} runAccept ρ (j ↦ draw (V j))`, `V` uniform over `q(κ)` blocks of
`n · n` coins.

**Proof sketch.** Move `B`'s coins to `(ω, ρ)` along `φ` (`expect_sample_equiv`). For fixed coins,
T1 makes `B`'s output the adversary's output `a` of the handler's run (`handler_result`), and the
handler's run is the run of `drawStep` with exponents from the seed blocks
(`simulate_handler`), so `[B accepts] = runAccept ρ (j ↦ draw (block j of ω))`. Split the uniform
pair (`Bridge.expect_sample_pair`), exchange the samples (`expect_sample_comm`) and read the seed as
its blocks (`seedBlocks`, `expect_sample_equiv`). -/
theorem expect_handlerMachine (B : NUPPT)
    (φ : (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ ≃ B.Coins κ)
    (hφ : ∀ (z : List Bool) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
      (ρ : A'.Coins κ), ∃ (a : Fin ((PolyExpr.const 1).eval κ) → Bool)
        (s : Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool),
        simulate ((handler G ℓ O b q H).impl κ z ω)
            (A'.toCompOn (bitCodec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)
              ((PolyExpr.const 1).eval κ)) κ (q.eval κ) ((handler G ℓ O b q H).advInput κ z ω) ρ)
            ((handler G ℓ O b q H).init κ) = .pure (a, s) ∧
          B.runAt κ z (φ (ω, ρ)) = (handler G ℓ O b q H).result κ z ω s a) :
    ProbComp.expect (ProbComp.sample (B.Coins κ))
        (fun ρ => if B.distinguisherL κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ρ = true then 1 else 0) =
      ProbComp.expect (ProbComp.sample (A'.Coins κ)) fun ρ =>
        ProbComp.expect (ProbComp.sample (Fin (q.eval κ) →
            Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool))
          fun V => runAccept G ℓ b q A' κ r g X Y Z T ρ fun j => draw G κ (G.desc κ r) (V j) := by
  have hpt : ∀ x : (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ,
      (if B.distinguisherL κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
          (φ x) = true then (1 : ℝ) else 0) =
        runAccept G ℓ b q A' κ r g X Y Z T x.2
          fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ x.1 j) := by
    rintro ⟨ω, ρ⟩
    obtain ⟨a, s, hsim, hrun⟩ :=
      hφ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ω ρ
    rw [handler_advInput] at hsim
    obtain ⟨f, hf⟩ := simulate_handler G ℓ O b q H κ r g X Y Z T ω
      (A'.toCompOn (bitCodec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)
        ((PolyExpr.const 1).eval κ)) κ (q.eval κ) [] ρ)
      (NUPPT.toCompOn_costBoundedBy _ _ _ _ _ _)
    rw [hf] at hsim
    have he := congrArg (fun c => ProbComp.expect c
      (fun p => if List.ofFn p.1 = [true] then (1 : ℝ) else 0)) hsim
    simp only [ProbComp.expect_bind, ProbComp.expect_pure] at he
    rw [runAccept_eq, he, NUPPT.distinguisherL_eq, hrun, handler_result]
    simp only [decide_eq_true_eq]
  -- the uniform pair `(ω, ρ)` in sequence
  have hpair : ∀ F : (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ → ℝ,
      ProbComp.expect (ProbComp.sample
          ((Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ)) F =
        ProbComp.expect (ProbComp.sample (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool))
          fun ω => ProbComp.expect (ProbComp.sample (A'.Coins κ)) fun ρ => F (ω, ρ) := by
    intro F
    rw [← Bridge.expect_sample_pair, ProbComp.expect_bind]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  calc ProbComp.expect (ProbComp.sample (B.Coins κ))
        (fun ρ => if B.distinguisherL κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ρ = true then 1 else 0)
      = ProbComp.expect (ProbComp.sample
          ((Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ))
          (fun x => if B.distinguisherL κ
            (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (φ x) = true then 1
            else 0) :=
        (ProbComp.expect_sample_equiv φ (fun ρ => if B.distinguisherL κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ρ = true then
            (1 : ℝ) else 0)).symm
    _ = ProbComp.expect (ProbComp.sample
          ((Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ))
          (fun x => runAccept G ℓ b q A' κ r g X Y Z T x.2
            fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ x.1 j)) :=
        congrArg _ (funext hpt)
    _ = ProbComp.expect (ProbComp.sample (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool))
          (fun ω => ProbComp.expect (ProbComp.sample (A'.Coins κ)) fun ρ =>
            runAccept G ℓ b q A' κ r g X Y Z T ρ
              fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j)) := hpair _
    _ = ProbComp.expect (ProbComp.sample (A'.Coins κ)) (fun ρ =>
          ProbComp.expect (ProbComp.sample (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool))
            fun ω => runAccept G ℓ b q A' κ r g X Y Z T ρ
              fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j)) :=
        ProbComp.expect_sample_comm _
    _ = _ := congrArg _ (funext fun ρ => ProbComp.expect_sample_equiv (seedBlocks G ℓ O b q H κ)
          (fun V => runAccept G ℓ b q A' κ r g X Y Z T ρ fun j => draw G κ (G.desc κ r) (V j)))

/-- The output bit read as a word: `[a 0 = 1] = [⟦a⟧ = [1]]` for a one-bit output `a`. -/
private theorem ite_ofFn_one {σ : Type} :
    (fun p : (Fin 1 → Bool) × σ => if p.1 0 = true then (1 : ℝ) else 0) =
      fun p => (fun lp : List Bool × σ => if lp.1 = [true] then (1 : ℝ) else 0)
        (List.ofFn p.1, p.2) := by
  funext p
  simp only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true]

/-- **The simulator with fresh exponents accepts with the average of `runAccept` over uniform
exponents**: the run of `A'` on the game's oracle lengths against the oracles of `drawStep` with
a fresh uniform exponent per query, read on the game's lengths (`castImpl` of
`ETTGame.freshImpl`), outputs `1` with probability `𝔼_{U ← Z_p^{q(κ)}} runAccept ρ U`.

**Proof sketch.** Transport the run to the handler's lengths, which are the game's
(`expect_simulate_castImpl_toCompOn` with `qLen_eval`, `aLen_eval`), then draw the exponents in
advance (`ETTGame.expect_simulate_tapeImpl`: `A'` makes at most `q(κ)` queries,
`NUPPT.toCompOn_costBoundedBy`). -/
theorem expect_castImpl_freshImpl (ρ : A'.Coins κ) :
    ProbComp.expect (simulate (castImpl (ins := (bb1Scheme G ℓ).inLens κ)
        (outs := (bb1Scheme G ℓ).outLens κ)
        (ETTGame.freshImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
          (drawStep G ℓ b κ (G.desc κ r) g X Y Z T)))
        (A'.toCompOn (bitCodec ((bb1Scheme G ℓ).inLens κ) ((bb1Scheme G ℓ).outLens κ) 1) κ
          (q.eval κ) [] ρ) (none, none))
      (fun p => if p.1 0 = true then 1 else 0) =
      ProbComp.expect (ProbComp.sample (Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order))
        fun U => runAccept G ℓ b q A' κ r g X Y Z T ρ U := by
  rw [ite_ofFn_one]
  refine (expect_simulate_castImpl_toCompOn (qLen_eval G ℓ κ).symm
    (aLen_eval G ℓ κ).symm (PolyExpr.eval_const 1 κ).symm
    (ETTGame.freshImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
      (drawStep G ℓ b κ (G.desc κ r) g X Y Z T)) A' κ (q.eval κ) [] ρ (none, none)
    (fun lp => if lp.1 = [true] then (1 : ℝ) else 0)).trans ?_
  exact (ETTGame.expect_simulate_tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
    (drawStep G ℓ b κ (G.desc κ r) g X Y Z T) (q.eval κ)
    (fun a => if List.ofFn a = [true] then (1 : ℝ) else 0)
    (A'.toCompOn (bitCodec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)
      ((PolyExpr.const 1).eval κ)) κ (q.eval κ) [] ρ) (q.eval κ)
    (NUPPT.toCompOn_costBoundedBy _ _ _ _ _ _) (none, none) 0 (by omega)).symm

/-- **Drawn exponents against uniform ones**: averaged over the adversary's coins,
`|𝔼_ρ 𝔼_V runAccept ρ (draw ∘ V) − 𝔼_ρ 𝔼_U runAccept ρ U| ≤ q(κ) · (1/2)^n`
(`abs_expect_draws_sub_le` for each `ρ`, `runAccept` having values `0` and `1`). -/
theorem abs_expect_runAccept_sub_le :
    |ProbComp.expect (ProbComp.sample (A'.Coins κ)) (fun ρ =>
        ProbComp.expect (ProbComp.sample (Fin (q.eval κ) →
            Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool))
          fun V => runAccept G ℓ b q A' κ r g X Y Z T ρ fun j => draw G κ (G.desc κ r) (V j)) -
      ProbComp.expect (ProbComp.sample (A'.Coins κ)) (fun ρ =>
        ProbComp.expect (ProbComp.sample (Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order))
          fun U => runAccept G ℓ b q A' κ r g X Y Z T ρ U)| ≤
      q.eval κ * (1 / 2 : ℝ) ^ (blockLen G).eval κ :=
  ProbComp.abs_expect_sub_le _ fun ρ => abs_expect_draws_sub_le G κ (G.desc κ r) (q.eval κ)
    (runAccept G ℓ b q A' κ r g X Y Z T ρ) (runAccept_eq_zero_or_one G ℓ b q A' κ r g X Y Z T ρ)

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
