import TCSlib.BooleanAnalysis.LMN.CircuitCompression
import TCSlib.BooleanAnalysis.LMN.RestrictionCompose
import Mathlib

/-!
# Iterative Circuit Reduction (Steps 8–9 of LMN)

## Step 8: Subsequent Restrictions

After the first Bernoulli(1/(40w)) restriction reduces the circuit from
depth d to depth d−1 with width l (Steps 5–7), we apply a second
Bernoulli(1/(40l)) restriction. By Håstad's switching lemma — now applied
to width-l formulas rather than width-w — this reduces all width-l CNFs
at the new layer 2 to depth-l decision trees (hence width-l DNFs), except
with probability at most s₃ · ((1/2)^l + exp(−n·p/3)).

The circuit then compresses again (Step 6), reducing to depth d−2.

This is the key observation: the one-step reduction mechanism (Steps 5–7)
applies at every iteration, not just the first. The only change is that
the width parameter shifts from w to l after the first step.

## Step 9: Union Bound Over All Iterations

Proceeding for all d−2 intermediate restrictions (from depth d down to
depth 2), a union bound gives:

  Pr[any step fails] ≤ Σᵢ sᵢ · ((1/2)^l + tail)
                     ≤ s · ((1/2)^l + tail)
                     ≤ ε/2   (when l = logb 2 (2s/ε))

where the sᵢ are the gate counts at each layer and s is the total circuit
size. The inequality Σ sᵢ ≤ s holds because every gate belongs to exactly
one layer.

The final reduction from depth 2 to a decision tree of depth logb 2 (2/ε)
contributes another ε/2 (from the switching lemma applied one last time),
giving total error ε.

**Note on constants**: Our switching lemma constant is 1/(40w) rather than
the textbook 1/(10w), due to the Bernoulli-to-counting conversion cost.
The mathematical structure of the iteration is identical.

## Restriction composition for multi-stage arguments

The composed restriction δ = p₁ · p₂ · ⋯ · pₘ decomposes into stages
via `restriction_compose_eq` (proved in `RestrictionCompose.lean`):

  Pr_{p·q}[event] = Σ_{ρ₁} w_p(ρ₁) · Pr_q[event(compose(ρ₁, ·))]

At each depth-reduction step, the "event" decomposes as
"first-stage failure ∨ second-stage failure":
- A(ρ₁) = "some gate at the current layer fails under ρ₁"
- B(ρ₂) = "some gate at a deeper layer fails under ρ₂"

The `two_stage_composed_union_bound` gives:
  E_{ρ₁}[Pr_{ρ₂}[A(ρ₁) ∨ B(ρ₂)]] ≤ Pr_p[A] + Pr_q[B]

Applied inductively over d−2 stages:
  Pr_{δ}[any fail] ≤ s₂·α + s₃·α + ⋯ + s_{d−1}·α ≤ s · α = ε/2
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

/-! ## Step 8: Subsequent Restriction Steps

The key observation is that `one_step_reduction_failure_bound` (Step 7)
is parameterized by the gate width `w`. After the first step produces
width-l CNFs, we simply instantiate w = l for the next step.

Each subsequent step applies the switching lemma to width-l formulas
under a Bernoulli(1/(40l)) restriction. -/

/-- **Step 8: Reduction at subsequent layers.**

After compression, the new layer-2 gates are width-l DNFs. A
Bernoulli(1/(40l)) restriction reduces them to width-l CNFs, except
with probability ≤ s_i · ((1/2)^l + exp(−n·p/3)).

This is `one_step_reduction_failure_bound` with w = l:
the same mechanism works at every iteration, since the switching lemma
applies to width-l formulas exactly as it does to width-w formulas. -/
theorem subsequent_step_reduction
    (gates : Fin s_i → DNF n) (l : ℕ) (hl : 0 < l)
    (hw : ∀ i, (gates i).width ≤ l)
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑l)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ¬ ∀ i : Fin s_i,
        ∃ ψ : CNF n, CNF.width ψ ≤ l ∧
          ∀ x, CNF.eval ψ x = restrictFn (gates i).eval ρ x) ≤
    ↑s_i * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) :=
  one_step_reduction_failure_bound gates l l hw hl hnd hnodup hn p hp_pos hp_le hp1

/-- **Step 8: dtDepth form.**

All s_i width-l gates have dtDepth ≤ l after a Bernoulli(1/(40l))
restriction, with probability ≥ 1 − s_i · ((1/2)^l + exp(−n·p/3)).

This is `one_step_dtDepth_bound` with w = l. -/
theorem subsequent_step_dtDepth
    (gates : Fin s_i → DNF n) (l : ℕ) (hl : 0 < l)
    (hw : ∀ i, (gates i).width ≤ l)
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑l)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ∀ i : Fin s_i, dtDepth (restrictFn (gates i).eval ρ) ≤ l) ≥
    1 - ↑s_i * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) :=
  one_step_dtDepth_bound gates l l hw hl hnd hnodup hn p hp_pos hp_le hp1

/-! ## Step 9: Multi-Stage Union Bound -/

/-- **Multi-stage failure bound.**

If at each of `m` stages the failure probability is bounded by
`layer_size i · α`, and the sum of layer sizes is at most `s`,
then the total failure probability (by union bound) is at most `s · α`.

This captures the core of Step 9: the per-stage bounds sum up
to at most s · α because every gate belongs to exactly one layer. -/
theorem multi_stage_failure_bound
    (m : ℕ) (layer_size : Fin m → ℕ) (s : ℕ)
    (h_sum : ∑ i, layer_size i ≤ s)
    (α : ℝ) (hα : 0 ≤ α)
    (failure_bound : Fin m → ℝ)
    (h_bound : ∀ i, failure_bound i ≤ (layer_size i : ℝ) * α) :
    ∑ i, failure_bound i ≤ (s : ℝ) * α := by
  exact le_trans (Finset.sum_le_sum fun i _ => h_bound i)
    (by simpa [Finset.sum_mul _ _ _] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_sum) hα)

/-- **Union bound for probabilities.**

For finitely many events A₁, …, Aₘ, the probability that any Aᵢ occurs
is at most the sum of individual probabilities. Stated for
`bernoulliRestrProb`. -/
theorem bernoulliRestrProb_union_bound_fin
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (A : Fin m → Restriction n → Prop)
    [∀ i, DecidablePred (A i)] :
    bernoulliRestrProb p (fun ρ => ∃ i, A i ρ) ≤
    ∑ i, bernoulliRestrProb p (A i) := by
  simp +decide only [bernoulliRestrProb]
  rw [Finset.sum_comm]
  gcongr
  split_ifs <;> norm_num
  · obtain ⟨i, hi⟩ := ‹_›
    exact le_trans (by aesop) (Finset.single_le_sum
      (fun i _ => by split_ifs <;> linarith [bernoulliRestrWeight_nonneg' p hp hp1 ‹_›])
      (Finset.mem_univ i))
  · exact Finset.sum_nonneg fun _ _ => by
      split_ifs <;> first | positivity | exact bernoulliRestrWeight_nonneg' p hp hp1 _

/-- **Step 9: Iterative reduction — dominant term bound.**

After d−2 iterations (from depth d to depth 2), each with gate counts
s₂, s₃, …, s_{d−1} where Σ sᵢ ≤ s, and failure probability
≤ sᵢ · (1/2)^l at each stage, the total failure probability is:

  Σ sᵢ · (1/2)^l ≤ s · (1/2)^l

When l = logb 2 (2s/ε), this equals ε/2. Combined with the final
depth-2 → decision tree step (which contributes another ε/2),
the total error is ε. -/
theorem iterative_dominant_term_bound
    (m : ℕ) (layer_size : Fin m → ℕ) (s : ℕ)
    (h_sum : ∑ i, layer_size i ≤ s) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    let l := Real.logb 2 (2 * ↑s / ε)
    ∑ i, ((layer_size i : ℝ) * (1 / 2 : ℝ) ^ l) ≤ ε / 2 := by
  simp +zetaDelta at *
  rw [← Finset.sum_mul _ _ _]
  rw [Real.inv_rpow (by positivity), Real.rpow_logb] <;> try positivity
  · field_simp; exact_mod_cast h_sum
  · norm_num

/-! ## Two-stage restriction composition bound -/

/-- **Two-stage composed union bound.**

Under a two-stage restriction (first Bernoulli(p), then Bernoulli(q)),
if A depends on the first-stage restriction ρ₁ and B depends on the
second-stage restriction ρ₂, then:

  E_{ρ₁ ~ p} [Pr_{ρ₂ ~ q}[A(ρ₁) ∨ B(ρ₂)]] ≤ Pr_p[A] + Pr_q[B]

This uses the fact that Pr_q[A(ρ₁) ∨ B(ρ₂)] ≤ 1_{A(ρ₁)} + Pr_q[B]
and then E_p[1_{A(ρ₁)}] = Pr_p[A].

**Application to the LMN iteration**: At each depth-reduction step,
the composed restriction δ = p₁ · p₂ · ⋯ decomposes via
`restriction_compose_eq` into:

  Pr_{δ}[event] = Σ_{ρ₁} w_{p₁}(ρ₁) · Pr_{rest}[event(compose(ρ₁, ·))]

When the event decomposes as A₁(ρ₁) ∨ B_{rest}(ρ₂), this theorem bounds:

  Pr_{δ}[fail] ≤ Pr_{p₁}[A₁] + Pr_{rest}[B_{rest}]

Iterating d−2 times gives the telescoping bound:

  Pr_{δ}[any fail] ≤ s₂·α + s₃·α + ⋯ + s_{d−1}·α ≤ s · α -/
theorem two_stage_composed_union_bound
    (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (A : Restriction n → Prop) [DecidablePred A]
    (B : Restriction n → Prop) [DecidablePred B] :
    ∑ ρ₁ : Restriction n, bernoulliRestrWeight p ρ₁ *
      bernoulliRestrProb q (fun ρ₂ => A ρ₁ ∨ B ρ₂) ≤
    bernoulliRestrProb p A + bernoulliRestrProb q B := by
  sorry -- TODO: goal ordering from rotate_left changed in v4.25.0-rc2; needs interactive rewrite

/-! ## Step 9: Full iterative argument (abstract version)

The following theorem captures the complete iterative reduction,
stated abstractly in terms of per-layer failure probabilities. -/

/-- **Abstract iterative reduction (Steps 8–9 combined).**

Consider a circuit with d−2 intermediate layers, where layer i has
sᵢ gates and Σ sᵢ ≤ s. At each iteration:
1. Apply a Bernoulli(pᵢ) restriction (Step 8)
2. With probability ≤ sᵢ · α, some gate at that layer fails (Step 7)
3. Compress the circuit (Step 6)

By the union bound (Step 9), the probability that ANY iteration fails
is at most (Σ sᵢ) · α ≤ s · α.

When α = (1/2)^l with l = logb 2 (2s/ε), we get s · α = ε/2.

This is purely an arithmetic/probability consequence of the per-stage
bounds; it does not depend on specific circuit structure. -/
theorem abstract_iterative_reduction
    (m : ℕ) (layer_size : Fin m → ℕ) (s : ℕ)
    (h_sum : ∑ i, layer_size i ≤ s) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε)
    (per_stage_bound : Fin m → ℝ)
    (h_stage : ∀ i, per_stage_bound i ≤
      (layer_size i : ℝ) * (1 / 2 : ℝ) ^ Real.logb 2 (2 * ↑s / ε)) :
    ∑ i, per_stage_bound i ≤ ε / 2 := by
  refine le_trans (Finset.sum_le_sum fun i _ => h_stage i) ?_
  convert iterative_dominant_term_bound m layer_size s h_sum hs ε hε using 1

end LMN
end
