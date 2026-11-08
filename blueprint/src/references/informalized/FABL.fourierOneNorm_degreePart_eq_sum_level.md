<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.fourierOneNorm_degreePart_eq_sum_level -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a degree part

**Claim.** The Fourier one norm of the degree-$k$ part of $f$ is the sum of $|\widehat f(S)|$ over all frequencies $S$ of cardinality $k$.

**Proof.** For each frequency $T$, the Fourier coefficient of the degree-$k$ part is $\widehat f(T)$ when $|T|=k$, and is zero otherwise (`fourierCoeff_degreePart`). Thus its absolute value is $|\widehat f(T)|$ on the level $|T|=k$ and zero off that level. Summing over all frequencies leaves exactly the sum over that level.

**Key facts.** `FABL.fourierCoeff_degreePart`.
