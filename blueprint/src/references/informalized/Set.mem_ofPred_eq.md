<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Compat.lean :: Set.mem_ofPred_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a predicate-defined set

**Claim.** For any type $\alpha$, element $x\in\alpha$, and predicate $p:\alpha\to\mathrm{Prop}$, membership of $x$ in $\{y\mid p(y)\}$ is equivalent to $p(x)$.

**Proof.** By definition, the set $\{y\mid p(y)\}$ consists precisely of those elements satisfying $p$. Thus membership of $x$ in this set is definitionally the proposition $p(x)$; the two sides are equal by reflexivity.
