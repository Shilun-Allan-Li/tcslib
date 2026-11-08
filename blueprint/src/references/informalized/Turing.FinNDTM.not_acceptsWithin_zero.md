<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.FinNDTM.not_acceptsWithin_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No acceptance in zero steps

**Claim.** There is no choice word of length zero for which the run from the initial configuration halts with output exactly the one-bit string $1$.

**Proof.** Suppose such a choice word exists. Its length is zero, so it is the empty word. Running on the empty word leaves the machine in its initial configuration, whose state is the initial state and is therefore present, not `none`. This contradicts the assumed halting condition.
