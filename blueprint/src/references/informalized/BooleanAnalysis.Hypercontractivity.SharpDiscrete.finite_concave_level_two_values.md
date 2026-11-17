<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_concave_level_two_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Values on a Concave Level Set

**Claim.** If a nonnegative function on a finite set takes values in one level set of a strictly concave function, then it takes at most two distinct values.

**Proof.** If the index set is empty, choose both values to be $0$; the coordinate condition is then vacuous. Otherwise, choose indices $x$ and $y$ where $f$ has its minimum and maximum, respectively. Set $a=f(x)$ and $b=f(y)$, which are nonnegative. Any coordinate equal to either endpoint already has one of the desired values. If some coordinate $i$ were strictly between them, then strict concavity on the nonnegative half-line would give $\varphi(f(i))>\min\{\varphi(a),\varphi(b)\}$. But all three function values equal $c$, making this the contradiction $c>c$. Thus every coordinate equals one of the two endpoint values.
