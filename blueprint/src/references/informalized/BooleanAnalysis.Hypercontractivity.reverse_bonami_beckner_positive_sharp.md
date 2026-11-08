<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.reverse_bonami_beckner_positive_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp reverse hypercontractivity

**Claim.** Under the stated sharp parameter conditions, every nonnegative function on the Boolean cube satisfies $M_q(T_\rho f)\ge M_p(f)$.

**Proof.** Use tensorization of the reverse inequality (`tensorize_reverse_bonami_beckner`). Its one-bit hypothesis is supplied by the one-bit reverse Bonami–Beckner theorem (`reverse_bonami_beckner_one_bit`), since the given $q,p,\rho$ satisfy its hypotheses, including the equality $\rho^2=(1-p)/(1-q)$. Tensorization then yields the claimed inequality for the full Boolean cube.

**Key facts.** `BooleanAnalysis.Hypercontractivity.tensorize_reverse_bonami_beckner`, `BooleanAnalysis.Hypercontractivity.reverse_bonami_beckner_one_bit`.
