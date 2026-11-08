<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.eventually_exercise9_30_asymptotic_kkl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic KKL bound

**Claim.** For all sufficiently large $n$, every Boolean function on the $n$-dimensional cube satisfies the stated asymptotic lower bound on its maximum influence in terms of its variance and $\log n$.

**Proof.** The numerical conditions theorem ensures that for all sufficiently large $n$, the logarithmic, power, and exponential inequalities required by the large-$n$ estimate hold ($\texttt{eventually\_exercise9\_30\_numeric\_conditions}$). For each such $n$, apply the asymptotic bound of the large-$n$ theorem to an arbitrary Boolean function. This gives the asserted inequality, uniformly over all such functions.

**Key facts.** `FABL.eventually_exercise9_30_numeric_conditions`, `FABL.exercise9_30_asymptotic_bound_of_large`.
