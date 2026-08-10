<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: localFactor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Per-coordinate factor for the event `U ∩ freeVars = S`

**Definition.** `localFactor (U S : Finset (Fin n)) (i : Fin n) (v : Option Bool) : ℝ`
is a three-way case split on the coordinate `i` and the value `v` a restriction
takes there:

- `i ∈ S`: `1` if `v = none`, else `0` — coordinate `i` is required to be free;
- `i ∉ S` but `i ∈ U`: `0` if `v = none`, and `boolToSign b` if `v = some b` —
  coordinate `i` is required to be fixed, and contributes its sign;
- `i ∉ S` and `i ∉ U`: `1` — coordinate `i` is unconstrained.

**Remark.** This is exactly the factor whose product over all coordinates equals
the summand `(if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)`
(`indicator_signProd_eq_prod`). Putting the indicator and the sign into one
coordinatewise product is what allows the Bernoulli average to be computed in a
single pass via `sum_bernoulli_prod`, instead of the textbook's two-stage
average over the free set and then the fixed bits.

**Used in.** `indicator_signProd_eq_prod`, `sum_varWeight_localFactor`,
`sum_varWeight_localFactor_mul`.
