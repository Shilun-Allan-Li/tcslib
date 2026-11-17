<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean :: Complexity.comp_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Length Under Composition

**Claim.** If $f$ and $g$ satisfy the stated polynomial length bounds, then $g\circ f$ has the asserted polynomial length bound.

**Proof.** Fix $x$. Since $|x|+1\ge1$, we have $1\le(|x|+1)^c$. Combining this with $|f(x)|\le C(|x|+1)^c$ gives $|f(x)|+1\le(C+1)(|x|+1)^c$. Apply the bound for $g$ at $f(x)$, then raise this inequality to the $d$th power and multiply by $D$. Finally, $(ab)^d=a^db^d$ and $((|x|+1)^c)^d=(|x|+1)^{cd}$ yield the desired estimate.
