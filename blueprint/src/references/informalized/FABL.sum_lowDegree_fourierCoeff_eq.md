<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/IntegralThresholdRepresentations.lean :: FABL.sum_lowDegree_fourierCoeff_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier expansion of a low-degree function

**Claim.** If $p$ has Fourier degree at most $d$, then at each point $x$ its value is the sum of its Fourier coefficient times the corresponding monomial over all subsets of size at most $d$.

**Proof.** The sum over the low-degree family is the same as the sum over subsets $S\subseteq[n]$ with $|S|\le d$. Extend this sum to all subsets of $[n]$. Each newly included subset has $|S|>d$, so its Fourier coefficient vanishes by the characterization of degree at most $d$ (\(\texttt{FABL.fourierDegree_le_iff}\)); thus the extension does not change the sum. The full sum is $p(x)$ by the Fourier expansion identity (\(\texttt{FABL.fourier_expansion}\)).

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourier_expansion`.
