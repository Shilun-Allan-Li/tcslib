<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ncompileTM_stepWith_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Choice Step

**Claim.** When $A(l)$ chooses between $l_1$ and $l_0'$, one compiled step with choice bit $b$ sends the configuration at $l$ to the configuration at $l_1$ if $b$ is true and at $l_0'$ otherwise, leaving the register valuation and output unchanged.

**Proof.** The given configuration has compiled state $(l,\mathrm{start})$. At this state, the choice-target function returns $(l_1,l_0')$, by the hypothesis about $A(l)$ and the definition of choice targets. Hence the compiled transition takes its choice branch: it moves to the program state $(l_1,\mathrm{start})$ when $b$ is true and to $(l_0',\mathrm{start})$ otherwise, with no tape writes, head movement, or output. Applying this transition therefore changes only the program label; the input-head position, register tapes and head positions, auxiliary tapes, and output remain as in the original configuration. These are precisely the components of the corresponding configuration formed by adjoining blank auxiliary tapes at the selected label.
