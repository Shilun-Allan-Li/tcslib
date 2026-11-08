<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.NSPACE.mono_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity Under Constant Rescaling

**Claim.** If $s_1(n)\le a s_2(n)$ for every $n$, then $\mathrm{NSPACE}(s_1)\subseteq\mathrm{NSPACE}(s_2)$.

**Proof.** Let $L\in\mathrm{NSPACE}(s_1)$, witnessed by a constant $c$ and a nondeterministic machine. Keep that machine and its per-input halting time. Every choice sequence uses at most $c\,s_1(|x|)\le c(a s_2(|x|))=(ca)s_2(|x|)$ space, where the inequality follows by multiplying the assumed bound by $c$ and the equality by associativity. Therefore the same machine, with space constant $ca$, witnesses membership in $\mathrm{NSPACE}(s_2)$.
