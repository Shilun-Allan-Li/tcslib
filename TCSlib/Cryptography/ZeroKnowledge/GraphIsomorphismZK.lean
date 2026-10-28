/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Closeness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge of the graph isomorphism protocol

[PS10, Theorem 122.3]: one iteration of the graph isomorphism protocol
(`giProtocol`, [PS10, Protocol 120.6]) is a zero-knowledge interactive proof for `L_iso` with
the witness relation `R_iso`. The simulator is [PS10, Algorithm 123.4]: guess the challenge
`b'`, send `H = π(G_{b'})`, run `V*` on `H` with fresh coins, and output the view if `V*`'s
challenge is `b'`; [PS10, Lemma 123.5] says that `H` is distributed as `π(G₀)` independently
of `b'` and that each attempt succeeds with probability exactly `1/2`.

The chapter's mathematics is stated first at the *concrete* layer over typed coins (a
cheating verifier is any function `V* : Graph n → ρ → Bool` of the first message and its
coins): the honest-verifier simulator by reindexing (Thm-122.3.hv, proved), Lemma 123.5
(proved), perfect simulation conditioned on success (Claim-123.b, proved by the coin
bijection `(π', b') ↦ π`), and the truncated simulator with `N` attempts, which fails with
probability `2^{-N}` and is otherwise exact (Thm-122.3.trunc). The string-level simulator
`giSim` (Alg-123.4) runs `n` attempts, each with a rejection-sampled permutation, a guessed
bit and a fresh tape for `V*`; its machine form is Claim-123.d and the statistical
zero-knowledge theorem is `gi_statZK` (Thm-122.3). The machine behind Claim-123.d and the
coin-tape bookkeeping behind Thm-122.3 live in the sibling files
`GraphIsomorphismZK/Simulator.lean` and `GraphIsomorphismZK/Closeness.lean` (namespace
`TCSlib.Cryptography.GIZK`), which shadow the definitions of this file with definitionally
equal copies; the targets here are closed by instantiating their results.

**Deviation (D8, D10):** strict PPT simulator truncated at `n` attempts, so the theorem is
*statistical* zero-knowledge with error `2^{-n} + (n + 1) · permFailBound n` (the text claims
perfect zero-knowledge with an expected polynomial-time simulator); only one iteration is
treated (the text defers the `n`-fold protocol to its §7.2.1); the Goldreich abort form
`PerfectZKAbort` holds for the one-attempt simulator at the concrete layer
(`giSimAttempt_perfectAbort`) but is not claimed for `giProtocol` itself, whose honest
prover's rejection-sampled `π` is not exactly uniform.

## Contents

* `GraphIsomorphismZK/Simulator.lean` — the string simulator as a polynomial-time machine
  (Claim-123.d, shadow form `GIZK.exists_simulator`).
* `GraphIsomorphismZK/Closeness.lean` — coin-tape bijections, `N`-fold products of close
  samplers, the real view from `exec`, and the closeness assembly `GIZK.statClose_real_sim`.

## Main definitions

* `TCSlib.Cryptography.giHonestView`, `TCSlib.Cryptography.giHVSim` — the honest verifier's
  view and its simulator by reindexing (Thm-122.3.hv).
* `TCSlib.Cryptography.giRealView`, `TCSlib.Cryptography.giSimAttempt`,
  `TCSlib.Cryptography.giSimTrunc` — the view of a cheating verifier, one attempt of
  [PS10, Algorithm 123.4], and the simulator truncated at `N` attempts (Alg-123.4, typed).
* `TCSlib.Cryptography.giSim`, `TCSlib.Cryptography.giSimCoins` — the string-level simulator
  of [PS10, Algorithm 123.4] and its coin polynomial.

## Main results

* `TCSlib.Cryptography.statClose_giHonestView` — honest-verifier perfect zero-knowledge of one
  iteration by reindexing (Thm-122.3.hv, proved).
* `TCSlib.Cryptography.gi_sim_H_dist`, `TCSlib.Cryptography.gi_sim_half` —
  [PS10, Lemma 123.5] (Lem-123.5, proved).
* `TCSlib.Cryptography.uprob_giSimAttempt_some` — perfect simulation conditioned on success
  (Claim-123.b, proved); `TCSlib.Cryptography.giSimAttempt_perfectAbort` — the abort form.
* `TCSlib.Cryptography.uprob_giSimTrunc_none` (proved),
  `TCSlib.Cryptography.statClose_giSimTrunc` — the truncated simulator (Thm-122.3.trunc).
* `TCSlib.Cryptography.exists_giSimulator` — the simulator is a uniform PPT (Claim-123.d).
* `TCSlib.Cryptography.gi_statZK`, `TCSlib.Cryptography.gi_zk`, `TCSlib.Cryptography.gi_hvzk`
  — [PS10, Theorem 122.3] (Thm-122.3).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge proofs, pp. 122–124.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
  Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Honest-verifier zero-knowledge by reindexing (Thm-122.3.hv) -/

/-- The honest verifier's view of one iteration of [PS10, Protocol 120.6] on the prover's
coins `π` and the verifier's coin `b`: `(b, π(G₀), γ)` with `γ = if b then π σ⁻¹ else π`. -/
def giHonestView {n : ℕ} (G₀ : Graph n) (σ : Equiv.Perm (Fin n)) (w : Equiv.Perm (Fin n) × Bool) :
    Bool × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph G₀ w.1, if w.2 then w.1 * σ⁻¹ else w.1)

/-- The honest-verifier simulator: draw `γ` and `b` uniformly and output `(b, γ(G_b), γ)`
[PS10, Theorem 122.3, honest-verifier case]. -/
def giHVSim {n : ℕ} (G₀ G₁ : Graph n) (w : Equiv.Perm (Fin n) × Bool) :
    Bool × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph (cond w.2 G₁ G₀) w.1, w.1)

/-- The reindexing `(π, b) ↦ (if b then π σ⁻¹ else π, b)` of the prover's coins, a bijection
with inverse `(γ, b) ↦ (if b then γ σ else γ, b)`. -/
def giReindex {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) × Bool ≃ Equiv.Perm (Fin n) × Bool where
  toFun w := (if w.2 then w.1 * σ⁻¹ else w.1, w.2)
  invFun w := (if w.2 then w.1 * σ else w.1, w.2)
  left_inv w := by
    rcases w with ⟨π, b⟩
    cases b <;> simp
  right_inv w := by
    rcases w with ⟨π, b⟩
    cases b <;> simp

/-- The simulator on the reindexed coins is the honest view (`gi_honest_reply_eq`). -/
theorem giHVSim_giReindex {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁)
    (w : Equiv.Perm (Fin n) × Bool) : giHVSim G₀ G₁ (giReindex σ w) = giHonestView G₀ σ w := by
  rcases w with ⟨π, b⟩
  cases b <;> simp [giHVSim, giHonestView, giReindex, permGraph_mul_inv_of_eq hσ]

/-- Honest-verifier perfect zero-knowledge of one iteration of the graph isomorphism
protocol [PS10, Theorem 122.3, honest verifier] (Thm-122.3.hv): for `σ(G₀) = G₁` the honest
view and the simulator's output have the same law, since the honest view is the simulator
composed with the bijection `giReindex σ` (`uprob_comp_equiv`). -/
theorem uprob_giHonestView_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (T : Bool × Graph n × Equiv.Perm (Fin n) → Prop) :
    uprob (fun w : Equiv.Perm (Fin n) × Bool => T (giHonestView G₀ σ w)) =
      uprob (fun w : Equiv.Perm (Fin n) × Bool => T (giHVSim G₀ G₁ w)) := by
  rw [← uprob_comp_equiv (giReindex σ) (fun w => T (giHVSim G₀ G₁ w))]
  congr 1
  funext w
  rw [giHVSim_giReindex hσ]

/-- The honest view is statistically `0`-close to the honest-verifier simulator
(Thm-122.3.hv in the `StatClose` form consumed by `StatZK`). -/
theorem statClose_giHonestView {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) : StatClose (giHonestView G₀ σ) (giHVSim G₀ G₁) 0 := fun T => by
  rw [uprob_giHonestView_eq hσ T, sub_self, abs_zero]

/-! ### Lemma 123.5 -/

/-- The coin bijection `(b, (π, r)) ↦ ((π, b), r)` between the simulator's coin layouts. -/
private def coinAssoc (α β γ : Type*) : α × (β × γ) ≃ (β × α) × γ where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- [PS10, Lemma 123.5], first half (exact, uniform permutation): in the simulator the graph
`H = π(G_{b'})` has the law of `π(G₀)`, independently of the guessed bit `b'`.

**Proof.** Condition on `b'` (`uprob_bool_prod` after swapping the coordinates); for `b' = 1`
the law of `π(G₁)` is that of `π(G₀)` by `uprob_permGraph_eq_of_isomorphic'` (Lem-119.a). -/
theorem gi_sim_H_dist {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (hσ : permGraph G₀ σ = G₁)
    (p : Graph n → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × Bool => p (permGraph (cond z.2 G₁ G₀) z.1)) =
      uprob (fun π : Equiv.Perm (Fin n) => p (permGraph G₀ π)) := by
  rw [← uprob_comp_equiv (Equiv.prodComm Bool (Equiv.Perm (Fin n))), uprob_bool_prod]
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, cond_false, cond_true]
  rw [uprob_permGraph_eq_of_isomorphic' hσ p]
  ring

/-- [PS10, Lemma 123.5], second half: for every cheating verifier `V*` (any function of the
graph `H` and of its coins `r`), the guessed bit equals `V*`'s challenge with probability
exactly `1/2`.

**Deviation:** `ρ` is assumed nonempty (for `ρ` empty every `uprob` is `0`; the frozen
statement omits the hypothesis).

**Proof.** Condition on `b'` (`uprob_bool_prod`); for `b' = 1` replace `π(G₁)` by `π(G₀)`
(`uprob_permGraph_eq_of_isomorphic`); the two conditional probabilities are those of an
event and of its complement (`uprob_not`), so they sum to `1`. -/
theorem gi_sim_half {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] (G₀ G₁ : Graph n)
    (σ : Equiv.Perm (Fin n)) (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) :
    uprob (fun z : (Equiv.Perm (Fin n) × Bool) × ρ =>
      V (permGraph (cond z.1.2 G₁ G₀) z.1.1) z.2 = z.1.2) = 1 / 2 := by
  rw [← uprob_comp_equiv (coinAssoc Bool (Equiv.Perm (Fin n)) ρ), uprob_bool_prod]
  simp only [coinAssoc, Equiv.coe_fn_mk, cond_false, cond_true]
  rw [uprob_permGraph_eq_of_isomorphic hσ (fun H r => V H r = true)]
  have h : uprob (fun w : Equiv.Perm (Fin n) × ρ => V (permGraph G₀ w.1) w.2 = false) =
      uprob (fun w : Equiv.Perm (Fin n) × ρ => ¬ V (permGraph G₀ w.1) w.2 = true) := by
    congr 1
    funext w
    simp
  rw [h, uprob_not]
  ring

/-! ### One attempt of the simulator and perfect simulation given success -/

/-- The view of a cheating verifier `V*` in one real iteration of [PS10, Protocol 120.6] on
the prover's coins `π` and `V*`'s coins `r`: `(r, H, γ)` with `H = π(G₀)`, `b = V*(H, r)` and
`γ = if b then π σ⁻¹ else π`. -/
def giRealView {n : ℕ} {ρ : Type*} (G₀ : Graph n) (σ : Equiv.Perm (Fin n)) (V : Graph n → ρ → Bool)
    (w : Equiv.Perm (Fin n) × ρ) : ρ × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph G₀ w.1, if V (permGraph G₀ w.1) w.2 then w.1 * σ⁻¹ else w.1)

/-- One attempt of the simulator [PS10, Algorithm 123.4] on the coins `((π', b'), r)`: send
`H = π'(G_{b'})`, run `V*` on `H` with coins `r`, and output the view `(r, H, π')` if `V*`'s
challenge is `b'`, `none` otherwise (Alg-123.4, typed). -/
def giSimAttempt {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (c : (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  if V (permGraph (cond c.1.2 G₁ G₀) c.1.1) c.2 = c.1.2 then
    some (c.2, permGraph (cond c.1.2 G₁ G₀) c.1.1, c.1.1)
  else none

/-- An attempt fails exactly when `V*`'s challenge differs from the guessed bit. -/
theorem giSimAttempt_eq_none_iff {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (c : (Equiv.Perm (Fin n) × Bool) × ρ) :
    giSimAttempt G₀ G₁ V c = none ↔ ¬ V (permGraph (cond c.1.2 G₁ G₀) c.1.1) c.2 = c.1.2 := by
  unfold giSimAttempt
  split_ifs with h <;> simp [h]

/-- One attempt fails with probability exactly `1/2` [PS10, Lemma 123.5] (`gi_sim_half`,
`uprob_not`). -/
theorem uprob_giSimAttempt_none {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) :
    uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V c = none) = 1 / 2 := by
  rw [OneWay.uprob_congr (giSimAttempt_eq_none_iff G₀ G₁ V), uprob_not, gi_sim_half G₀ G₁ σ hσ V]
  norm_num

/-- The coin bijection of Claim-123.b: `((π, b'), r) ↦ ((if b' then π σ⁻¹ else π, b'), r)`,
mapping the prover's coins to the simulator's coins (inverse: multiply by `σ`). -/
private def simReindex {n : ℕ} (ρ : Type*) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm (Fin n) × Bool) × ρ ≃ (Equiv.Perm (Fin n) × Bool) × ρ where
  toFun c := ((if c.1.2 then c.1.1 * σ⁻¹ else c.1.1, c.1.2), c.2)
  invFun c := ((if c.1.2 then c.1.1 * σ else c.1.1, c.1.2), c.2)
  left_inv c := by
    rcases c with ⟨⟨π, b⟩, r⟩
    cases b <;> simp
  right_inv c := by
    rcases c with ⟨⟨π, b⟩, r⟩
    cases b <;> simp

/-- Splitting an event along a second event: `Pr[p ∧ q] + Pr[¬p ∧ q] = Pr[q]`. -/
private theorem uprob_and_add_uprob_not_and {α : Type*} [Fintype α] (p q : α → Prop) :
    uprob (fun a => p a ∧ q a) + uprob (fun a => ¬ p a ∧ q a) = uprob q := by
  classical
  simp only [uprob_eq_card_filter]
  rw [← add_div]
  congr 1
  have h := filter_card_add_filter_neg_card_eq_card (s := univ.filter q) p
  rw [filter_filter, filter_filter] at h
  norm_cast
  rw [← h]
  congr 2 <;> ext a <;> simp [and_comm]

/-- Perfect simulation conditioned on success [PS10, proof of Theorem 122.3, "since `H` is
independent from `b'`, this does not change the output distribution"] (Claim-123.b): for
every test set `T` of views, the probability that an attempt succeeds with a view in `T` is
exactly half the probability that the real view of `V*` lies in `T`.

**Proof sketch.** Reindex the attempt's coins by `simReindex`: on `((π, b'), r)` the attempt sends
`H = π(G₀)` in both cases (`permGraph_mul_inv_of_eq`), succeeds iff `V*(π(G₀), r) = b'`, and
then outputs exactly `giRealView (π, r)`. Condition on `b'` (`uprob_bool_prod`) and add the
two halves (`uprob_and_add_uprob_not_and`). -/
theorem uprob_giSimAttempt_some {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool)
    (T : ρ × Graph n × Equiv.Perm (Fin n) → Prop) :
    uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => ∃ v, giSimAttempt G₀ G₁ V c = some v ∧ T v) =
      1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (giRealView G₀ σ V w)) := by
  rw [← uprob_comp_equiv (simReindex ρ σ)]
  have key : ∀ c : (Equiv.Perm (Fin n) × Bool) × ρ,
      (∃ v, giSimAttempt G₀ G₁ V (simReindex ρ σ c) = some v ∧ T v) ↔
        (V (permGraph G₀ c.1.1) c.2 = c.1.2 ∧ T (giRealView G₀ σ V (c.1.1, c.2))) := by
    rintro ⟨⟨π, b⟩, r⟩
    cases b <;> cases hV : V (permGraph G₀ π) r <;>
      simp [simReindex, giSimAttempt, giRealView, hV, permGraph_mul_inv_of_eq hσ]
  rw [OneWay.uprob_congr key, ← uprob_comp_equiv (coinAssoc Bool (Equiv.Perm (Fin n)) ρ),
    uprob_bool_prod]
  simp only [coinAssoc, Equiv.coe_fn_mk]
  have h := uprob_and_add_uprob_not_and (fun w : Equiv.Perm (Fin n) × ρ => V (permGraph G₀ w.1) w.2 = true)
    (fun w => T (giRealView G₀ σ V w))
  have hf : uprob (fun w : Equiv.Perm (Fin n) × ρ =>
      V (permGraph G₀ w.1) w.2 = false ∧ T (giRealView G₀ σ V (w.1, w.2))) =
      uprob (fun w : Equiv.Perm (Fin n) × ρ => ¬ V (permGraph G₀ w.1) w.2 = true ∧ T (giRealView G₀ σ V w)) := by
    congr 1
    funext w
    simp
  rw [hf]
  linarith

/-- The abort form of perfect zero-knowledge for one attempt of the simulator
[Goldreich, Definition 4.3.1; PS10, Algorithm 123.4] (Claim-123.b, `PerfectZKAbort` shape at
the concrete layer): the attempt aborts with probability at most `1/2`, and for every test
set `T`, `Pr[T(view)] · Pr[attempt ≠ ⊥] = Pr[attempt ≠ ⊥ ∧ T(attempt)]`. -/
theorem giSimAttempt_perfectAbort {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool)
    (T : ρ × Graph n × Equiv.Perm (Fin n) → Prop) :
    uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V c = none) ≤ 1 / 2 ∧
    uprob (fun w : Equiv.Perm (Fin n) × ρ => T (giRealView G₀ σ V w)) *
        uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V c ≠ none) =
      uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ =>
        ∃ v, giSimAttempt G₀ G₁ V c = some v ∧ T v) := by
  refine ⟨(uprob_giSimAttempt_none hσ V).le, ?_⟩
  rw [uprob_not, uprob_giSimAttempt_none hσ V, uprob_giSimAttempt_some hσ V T]
  ring

/-! ### The truncated simulator (Thm-122.3.trunc) -/

/-- The simulator truncated at `N` attempts with independent coins: the output of the first
successful attempt, `none` (`⊥`) if all `N` fail (Alg-123.4, typed; the strict-PPT
truncation of D8). -/
def giSimTrunc {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool) (N : ℕ)
    (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  (List.finRange N).findSome? fun t => giSimAttempt G₀ G₁ V (c t)

/-- The truncated simulator fails exactly when every attempt fails. -/
theorem giSimTrunc_eq_none_iff {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool) (N : ℕ)
    (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) :
    giSimTrunc G₀ G₁ V N c = none ↔ ∀ t, giSimAttempt G₀ G₁ V (c t) = none := by
  unfold giSimTrunc
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The truncated simulator outputs `⊥` with probability exactly `2^{-N}`
[PS10, proof of Theorem 122.3, "`S` has probability `1/2` of succeeding in each trial"]
(Thm-122.3.trunc, failure probability): the attempts use disjoint coins
(`OneWay.uprob_pi_forall`) and each fails with probability `1/2`
(`uprob_giSimAttempt_none`). -/
theorem uprob_giSimTrunc_none {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) (N : ℕ) :
    uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => giSimTrunc G₀ G₁ V N c = none) =
      (2 : ℝ)⁻¹ ^ N := by
  rw [OneWay.uprob_congr (giSimTrunc_eq_none_iff G₀ G₁ V N),
    OneWay.uprob_pi_forall (ι := Fin N) (fun c => giSimAttempt G₀ G₁ V c = none),
    uprob_giSimAttempt_none hσ V, Fintype.card_fin]
  norm_num

/-- With one more attempt whose first attempt succeeds, the truncated simulator outputs that
attempt's view (`List.finRange_succ`, `List.findSome?_cons_of_isSome`). -/
private theorem giSimTrunc_cons_of_some {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (N : ℕ) {a : (Equiv.Perm (Fin n) × Bool) × ρ} (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ)
    {v : ρ × Graph n × Equiv.Perm (Fin n)} (ha : giSimAttempt G₀ G₁ V a = some v) :
    giSimTrunc G₀ G₁ V (N + 1) (Fin.cons a c) = some v := by
  unfold giSimTrunc
  rw [List.finRange_succ, List.findSome?_cons_of_isSome]
  · simp [ha]
  · simp [ha]

/-- With one more attempt whose first attempt fails, the truncated simulator is the truncated
simulator on the remaining attempts (`List.findSome?_cons_of_isNone`, `List.findSome?_map`). -/
private theorem giSimTrunc_cons_of_none {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (N : ℕ) {a : (Equiv.Perm (Fin n) × Bool) × ρ} (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ)
    (ha : giSimAttempt G₀ G₁ V a = none) :
    giSimTrunc G₀ G₁ V (N + 1) (Fin.cons a c) = giSimTrunc G₀ G₁ V N c := by
  unfold giSimTrunc
  rw [List.finRange_succ, List.findSome?_cons_of_isNone, List.findSome?_map]
  · simp only [Function.comp_def, Fin.cons_succ]
  · simp [ha]

/-- Independent coordinates: `Pr[A(z.1) ∧ B(z.2)] = Pr[A] · Pr[B]` on a product
(`uprob_prod`, `OneWay.uexp_indicator`). -/
private theorem uprob_prod_and {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop) :
    uprob (fun z : α × β => A z.1 ∧ B z.2) = uprob A * uprob B := by
  classical
  rw [uprob_prod, mul_comm, ← OneWay.uexp_indicator]
  congr 1
  funext a
  by_cases ha : A a
  · simp [ha]
  · simp [ha, uprob_false]

/-- One step of the recursion for the law of the truncated simulator: with one more attempt,
`Pr[T(S_{N+1})] = 1/2 · Pr[T(S_N)] + 1/2 · Pr[T(some view)]`.

**Proof sketch.** Split the coins of the `N + 1` attempts as (first attempt, remaining
attempts) by `Fin.consEquiv` (`uprob_comp_equiv`) and the event along "the first attempt
fails" (`uprob_and_add_uprob_not_and`): when it fails, `S_{N+1}` is `S_N` on the remaining
coins (`giSimTrunc_cons_of_none`), and the two factors are independent
(`uprob_prod_and`, `uprob_giSimAttempt_none`); when it succeeds the output is its view
(`giSimTrunc_cons_of_some`), an event of the first coordinate alone (`uprob_fst`) of
probability `1/2 · Pr[T(some view)]` (`uprob_giSimAttempt_some`). -/
private theorem uprob_giSimTrunc_succ {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) (N : ℕ)
    (T : Option (ρ × Graph n × Equiv.Perm (Fin n)) → Prop) :
    uprob (fun c : Fin (N + 1) → (Equiv.Perm (Fin n) × Bool) × ρ =>
        T (giSimTrunc G₀ G₁ V (N + 1) c)) =
      1 / 2 * uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) +
        1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) := by
  rw [← uprob_comp_equiv (Fin.consEquiv fun _ => (Equiv.Perm (Fin n) × Bool) × ρ)]
  have hsplit := uprob_and_add_uprob_not_and
    (fun z : ((Equiv.Perm (Fin n) × Bool) × ρ) × (Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) =>
      giSimAttempt G₀ G₁ V z.1 = none)
    (fun z => T (giSimTrunc G₀ G₁ V (N + 1) ((Fin.consEquiv fun _ => _) z)))
  have hA : uprob (fun z : ((Equiv.Perm (Fin n) × Bool) × ρ) × (Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) =>
      giSimAttempt G₀ G₁ V z.1 = none ∧
        T (giSimTrunc G₀ G₁ V (N + 1) ((Fin.consEquiv fun _ => _) z))) =
      1 / 2 * uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) := by
    rw [← uprob_giSimAttempt_none hσ V,
      ← uprob_prod_and (fun a : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V a = none)
        (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c))]
    refine OneWay.uprob_congr fun z => and_congr_right fun hz => ?_
    rw [show (Fin.consEquiv fun _ => (Equiv.Perm (Fin n) × Bool) × ρ) z = Fin.cons z.1 z.2 from rfl,
      giSimTrunc_cons_of_none G₀ G₁ V N z.2 hz]
  have hB : uprob (fun z : ((Equiv.Perm (Fin n) × Bool) × ρ) × (Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) =>
      ¬ giSimAttempt G₀ G₁ V z.1 = none ∧
        T (giSimTrunc G₀ G₁ V (N + 1) ((Fin.consEquiv fun _ => _) z))) =
      1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) := by
    rw [← uprob_giSimAttempt_some hσ V (fun v => T (some v)),
      ← uprob_fst (β := Fin N → (Equiv.Perm (Fin n) × Bool) × ρ)
        (fun a : (Equiv.Perm (Fin n) × Bool) × ρ => ∃ v, giSimAttempt G₀ G₁ V a = some v ∧ T (some v))]
    refine OneWay.uprob_congr fun z => ?_
    rw [show (Fin.consEquiv fun _ => (Equiv.Perm (Fin n) × Bool) × ρ) z = Fin.cons z.1 z.2 from rfl]
    constructor
    · rintro ⟨hne, hT⟩
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      exact ⟨v, hv, by rwa [giSimTrunc_cons_of_some G₀ G₁ V N z.2 hv] at hT⟩
    · rintro ⟨v, hv, hT⟩
      exact ⟨by simp [hv], by rwa [giSimTrunc_cons_of_some G₀ G₁ V N z.2 hv]⟩
  rw [← hsplit, hA, hB]

/-- The distance between the law of the truncated simulator and the law of the real view
halves with every attempt: `|Pr[T(S_N)] - Pr[T(some view)]| ≤ 2^{-N}`.

**Proof sketch.** Induction on `N`. For `N = 0` the simulator outputs `none`
(`List.finRange_zero`) and both probabilities lie in `[0, 1]`. The step is
`uprob_giSimTrunc_succ`: `Pr[T(S_{N+1})] - p = 1/2 (Pr[T(S_N)] - p)`. -/
private theorem abs_uprob_giSimTrunc_sub_le {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool)
    (N : ℕ) (T : Option (ρ × Graph n × Equiv.Perm (Fin n)) → Prop) :
    |uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) -
      uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w)))| ≤ (2 : ℝ)⁻¹ ^ N := by
  induction N with
  | zero =>
    have h0 : ∀ c : Fin 0 → (Equiv.Perm (Fin n) × Bool) × ρ, giSimTrunc G₀ G₁ V 0 c = none :=
      fun c => by simp [giSimTrunc]
    have hp0 := uprob_nonneg fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))
    have hp1 := uprob_le_one fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))
    simp only [h0, pow_zero]
    by_cases hT : T none
    · simp only [hT, uprob_true]
      rw [abs_le]
      constructor <;> linarith
    · simp only [hT, uprob_false]
      rw [abs_le]
      constructor <;> linarith
  | succ N ih =>
    rw [uprob_giSimTrunc_succ hσ V N T]
    have h : 1 / 2 * uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) +
        1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) -
        uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) =
        1 / 2 * (uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) -
          uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w)))) := by ring
    rw [h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), pow_succ]
    calc 1 / 2 * |uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) -
          uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w)))|
        ≤ 1 / 2 * (2 : ℝ)⁻¹ ^ N := by gcongr
      _ = (2 : ℝ)⁻¹ ^ N * 2⁻¹ := by ring

/-- The truncated simulator is statistically `2^{-N}`-close to the real view
[PS10, Theorem 122.3, truncated form] (Thm-122.3.trunc): for every test set `T` of optional
views, `|Pr[T(S_N)] - Pr[T(some view)]| ≤ 2^{-N}`.

**Proof sketch.** Decompose the event `T(S_N)` by the index of the first successful attempt
(`List.findSome?` on `List.finRange N`: `giSimTrunc = some v` iff some `t` has
`giSimAttempt (c t) = some v` and all earlier attempts fail): the attempts have disjoint
coins, so by `uprob_prod` / `OneWay.uprob_update` the `t`-th term is
`(1/2)^t · Pr[∃ v, attempt = some v ∧ T (some v)] = (1/2)^{t+1} · Pr[T (some view)]`
(`uprob_giSimAttempt_some`, `uprob_giSimAttempt_none`); summing the geometric series,
`Pr[T(S_N)] = (1 - 2^{-N}) Pr[T (some view)] + 2^{-N} [T none]`
(`uprob_giSimTrunc_none`), whose distance from `Pr[T (some view)]` is at most `2^{-N}`. -/
theorem statClose_giSimTrunc {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) (N : ℕ) :
    StatClose (giSimTrunc G₀ G₁ V N)
      (fun w : Equiv.Perm (Fin n) × ρ => some (giRealView G₀ σ V w)) ((2 : ℝ)⁻¹ ^ N) :=
  fun T => abs_uprob_giSimTrunc_sub_le hσ V N T

/-! ### The string-level simulator [PS10, Algorithm 123.4] (Alg-123.4, Claim-123.d) -/

/-- The length of the coin block of one attempt of the string simulator against `V'` at
instance length `N`: one guessed bit, `(N + 1)²` permutation-sampling bits, and `V'`'s tape. -/
def giSimBlockLen (V' : Strategy) (N : ℕ) : ℕ := 1 + (N + 1) ^ 2 + V'.coinLen N

/-- The coin polynomial of the string simulator: `|x|` blocks (at most `|x|` attempts are
made, the actual number being the vertex count `n ≤ |x|`). -/
def giSimCoins (V' : Strategy) : PolyExpr :=
  .mul .var (.add (.add (.const 1) (.normal 1 2)) V'.coins)

/-- The coin polynomial evaluates to `|x|` blocks of `giSimBlockLen V' |x|` bits. -/
theorem giSimCoins_eval (V' : Strategy) (N : ℕ) : (giSimCoins V').eval N = N * giSimBlockLen V' N := by
  simp [giSimCoins, giSimBlockLen, PolyExpr.eval, PolyExpr.normal, Strategy.coinLen]

/-- One attempt of the string simulator [PS10, Algorithm 123.4] on `(x, z)` with the coin
block `c = b' :: (permutation coins ++ V'`'s tape)`: `H := π(G_{b'})` for `π := samplePerm n`,
`b :=` the bit of `V'.next x z rV [H]`, and the encoded view `⟨⟨x, z⟩, ⟨rV, [H, encPerm π]⟩⟩`
if `b = b'`, `none` otherwise. -/
noncomputable def giSimAttemptStr (V' : Strategy) (x z c : List Bool) : Option (List Bool) :=
  let n := instanceVertexCount x
  let b' := c.headD false
  let π := samplePerm n ((c.drop 1).take ((x.length + 1) ^ 2))
  let rV := c.drop (1 + (x.length + 1) ^ 2)
  let H := encGraph (permGraph (if b' then instanceG₁ x else instanceG₀ x) π)
  if (V'.next x z rV [H]).headD false = b' then some (View.encode ⟨x, z, rV, [H, encPerm π]⟩)
  else none

/-- The string simulator [PS10, Algorithm 123.4] (Alg-123.4): up to `n = instanceVertexCount x`
attempts on the consecutive coin blocks of the tape `r`; the first successful attempt's view,
or `⊥ = []` after `n` failures.

**Deviation (D8):** truncated at `n` attempts (strict PPT) instead of restarting until
success. -/
noncomputable def giSim (V' : Strategy) (x z r : List Bool) : List Bool :=
  ((List.range (instanceVertexCount x)).findSome? fun t =>
    giSimAttemptStr V' x z (coinSlice (giSimBlockLen V' x.length) t r)).getD []

/-- The string simulator is a uniform PPT [PS10, proof of Theorem 122.3, "`S` runs in
(expected) polynomial time"] (Claim-123.d): for every efficient `V'` there is a uniform
`NUPPT` with coin polynomial `giSimCoins V'` whose activation on `⟨x, z⟩` at parameter `|x|`
is `giSim V' x z r`.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with `V'.next x z rV [H] =
A.runAtL |x| ⟨⟨x, z⟩, encodeMsgs [H]⟩ rV` (`Strategy.ofNUPPT_next`), polynomial-time by
`A.polyTimeComputable_output` and the pairing calculus. One attempt on the raw layout is
polynomial-time: the block is cut by `polyTimeComputable_pairTakePoly`/`pairDropPoly` with
the unary block length (`polyTimeComputable_unaryPoly`), `encPerm π` by
`polyTimeComputable_encSamplePerm`-style sampling, `H` by `polyTimeComputable_encPermGraph`,
the comparison by `polyTimeComputable_pairEq`, the view by `PolyTimeComputable.pairEncode`.
The loop over `t < n` is `Complexity.polyTimeComputable_iterateFind` with the attempt index in
the state and the accepting test "the attempt succeeded" (`R := var`, `P :=` the layout
length); the result is packaged by `NUPPT.ofPolyTimeUniform` with coins `giSimCoins V'`
(`NUPPT.runAtL_ofPolyTimeUniform`, `NUPPT.ofPolyTimeUniform_uniform`). -/
theorem exists_giSimulator (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = giSimCoins V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = giSim V' x z (List.ofFn r) :=
  GIZK.exists_simulator V' hV'

/-! ### Theorem 122.3 -/

/-- [PS10, Theorem 122.3], one iteration, statistical form (D8): the graph isomorphism
protocol is statistical zero-knowledge for `R_iso` with a negligible error.

**Deviation (D8, D10):** statistical instead of perfect zero-knowledge (strict PPT simulator
truncated at `n` attempts; rejection-sampled permutations); one iteration (the text's
`n`-fold protocol relies on its §7.2.1).

**Proof sketch.** Take `δ N := 2⁻¹ ^ instanceVertices N + (instanceVertices N + 1) ·
permFailBound (instanceVertices N)`, negligible by `negligible_two_pow_neg_sqrt_div` (with
`instanceVertices N ≥ √(N / 4)` for `N ≥ 8`), `negligible_mul_permFailBound` and
`Negligible.add`. For an efficient `V'` take the simulator of `exists_giSimulator`. For
`Riso x y`, i.e. `x = encInstance G₀ G₁`, `y = encPerm σ`, `σ(G₀) = G₁`, let
`V* H r := (V'.next x z r [encGraph H]).headD false` on `ρ := V'.Coins |x|` (nonempty) and
`enc (r, H, γ) := View.encode ⟨x, z, List.ofFn r, [encGraph H, encPerm γ]⟩`. The real view
`((giProtocol.withV V').viewV x y z (r₁, r₂)).encode` is `enc (giRealView G₀ σ V* (π, r₂))`
with `π = samplePerm n (List.ofFn r₁)` (`exec_succ` three times, `decPerm_encPerm`,
`decGraph_encGraph`), and `giSim V' x z (List.ofFn r)` is `(Option.map enc (giSimTrunc G₀ G₁
V* n c)).getD []` with the `t`-th attempt's coins `c t = ((samplePerm n …, b'_t), rV_t)` read
from the `t`-th block (`giSimCoins_eval`, `coinSlice`). Chain of `StatClose` steps:
(1) real view with sampled `π` ≈ real view with uniform `π` within `permFailBound n`
(`statClose_samplePerm`, `StatClose.prod` with `StatClose.refl` for `r₂`, `StatClose.map`);
(2) `statClose_giSimTrunc` within `2^{-n}`, mapped by `v ↦ (Option.map enc v).getD []`
(`StatClose.map`); (3) the simulator with uniform `π'_t` ≈ with sampled `π'_t` within
`n · permFailBound n` (`StatClose.prod` iterated over the `n` blocks, `StatClose.map`);
`StatClose.trans`, `StatClose.symm`, `StatClose.mono` with
`instanceVertices_length_encInstance`. -/
theorem gi_statZK : ∃ δ : ℕ → ℝ, Negligible δ ∧ StatZK giProtocol Riso δ := by
  refine ⟨fun N => (2 : ℝ)⁻¹ ^ instanceVertices N +
    ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N), GIZK.negligible_delta, ?_⟩
  intro V' hV'
  obtain ⟨S, hS, hc, hsim⟩ := exists_giSimulator V' hV'
  refine ⟨S, hS, ?_⟩
  rintro x y z ⟨n, G₀, G₁, σ, hx, hy, hσ⟩
  rw [show x = encInstance G₀ G₁ from hx, hy]
  have hm : S.coinLen (encInstance G₀ G₁).length =
      (encInstance G₀ G₁).length * GIZK.blockLen V' (encInstance G₀ G₁).length := by
    rw [NUPPT.coinLen, hc, giSimCoins_eval]
    rfl
  have key := GIZK.statClose_real_sim V' G₀ G₁ σ z
    (statClose_giSimTrunc hσ (GIZK.vstar V' (encInstance G₀ G₁) z) n) _ hm
  have hsim' : S.simulate (encInstance G₀ G₁) z =
      fun r => giSim V' (encInstance G₀ G₁) z (List.ofFn r) :=
    funext (hsim _ z)
  dsimp only
  rw [hsim', instanceVertices_length_encInstance]
  exact key

/-- [PS10, Theorem 122.3]: the graph isomorphism protocol is zero-knowledge for `R_iso`
(`StatZK.zk`). -/
theorem gi_zk : ZK giProtocol Riso := by
  obtain ⟨δ, hδ, h⟩ := gi_statZK
  exact h.zk hδ

/-- [PS10, Theorem 122.3, honest verifier]: the graph isomorphism protocol is honest-verifier
zero-knowledge for `R_iso` (`StatZK.hvzk` with `giVerifier_efficient`). -/
theorem gi_hvzk : HVZK giProtocol Riso := by
  obtain ⟨δ, hδ, h⟩ := gi_statZK
  exact h.hvzk hδ giVerifier_efficient

end TCSlib.Cryptography
