<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.noiseOperator_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity at Unit Noise

**Claim.** For every function on the sign cube, the noise operator with parameter $1$ is the identity.

**Proof.** Fix an input $x$. The Fourier expansion of the noise operator expresses its value there as $\sum_S 1^{|S|}\widehat f(S)\chi_S(x)$ (`noiseOperator_fourier_expansion`). Every factor $1^{|S|}$ equals one, so this is the Fourier expansion of $f(x)$ (`fourier_expansion`). Thus the two functions agree at every input.

**Key facts.** `FABL.noiseOperator_fourier_expansion`, `FABL.fourier_expansion`.
