<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: varWeight_compose_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Per-coordinate composition identity for `varWeight`

**Claim.** For all `p q : ℝ` and every outcome `c : Option Bool`,

`∑ a : Option Bool, ∑ b : Option Bool, varWeight p a * varWeight q b * [a.orElse (fun _ => b) = c] = varWeight (p * q) c`,

where `[·]` is the `if … then 1 else 0` indicator. So one coordinate of a
Bernoulli(`p`) restriction followed by a Bernoulli(`q`) restriction has exactly
the Bernoulli(`p*q`) marginal. No hypothesis on `p`, `q`.

**Proof.** Finite case check: `rcases c with (_ | b) <;> simp +decide [varWeight]`,
then `cases b <;> norm_num <;> ring`.

- `c = none`: the only surviving pair is `a = b = none`, contributing
  `p * q = varWeight (p*q) none`.
- `c = some b`: two pairs survive — `a = some b` (weight `(1-p)/2`) and
  `a = none, b' = some b` (weight `p * (1-q)/2`) — and
  `(1-p)/2 + p(1-q)/2 = (1 - p q)/2 = varWeight (p*q) (some b)`, which is the
  `ring` step.

**Remark.** This one coordinate computation is the entire probabilistic content
of the composition theorem; everything above it (`compose_fiber_weight_eq`,
`restriction_compose_eq`) is sum/product bookkeeping over the `n` coordinates.

**Used in.** `compose_fiber_weight_eq`.
