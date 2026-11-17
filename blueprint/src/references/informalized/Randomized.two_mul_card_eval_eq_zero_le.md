<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SchwartzZippel.lean :: Randomized.two_mul_card_eval_eq_zero_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial zero count over a finite set

**Claim.** For a nonzero polynomial $p$ in $m$ variables over an integral domain, if $S$ is finite and nonempty and $2\deg(p)\le |S|$, at most half of the functions from the variables to $S$ make $p$ vanish.

**Proof.** The Schwartz–Zippel bound says that the fraction of functions $f$ with values in $S$ for which $p(f)=0$ is at most $\deg(p)/|S|$. Nonemptiness of $S$ makes the denominator positive. The hypothesis $2\deg(p)\le |S|$ implies $\deg(p)/|S|\le 1/2$. The set of all functions has cardinality $|S|^m$, so clearing the positive denominators in this fraction bound gives twice the number of zeros at most $|S|^m$.
