<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.nchoice_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice Target Characterization

**Claim.** If the choice-target function at a compiled state $q$ returns $(l_1,l_0)$, then $q$ is the program state at the initial phase for some label $l$, and the instruction $A(l)$ chooses between $l_1$ and $l_0$.

**Proof.** Since the choice-target function returns a pair, its defining cases force $q$ to be a program state $(l,\mathrm{ph})$; all other compiled-state forms return no targets. In the program-state case, targets are reported only when $\mathrm{ph}$ is the initial phase, so $q=(l,\mathrm{start})$. The instruction at $l$ cannot be deterministic, since deterministic instructions have no choice targets. Thus $A(l)$ is a choice instruction, and equality of its reported pair with $(l_1,l_0)$ identifies its two targets as $l_1$ and $l_0$.
