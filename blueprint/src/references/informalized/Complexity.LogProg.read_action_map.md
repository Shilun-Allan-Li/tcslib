<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_action_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State relabeling of reading actions

**Claim.** For each reading phase, optional Boolean value, and tuple of work-tape symbols, relabeling the states of the reading transition defined through the canonical sum injections gives the reading transition defined directly using $st$ and $ex$.

**Proof.** Check the possible reading phases. In each case, the transition is built from actions whose movements, tape operations, and output are independent of the state labels; the only state-dependent data are the successor states. Applying the relabeling sends a phase successor from the left summand to its image under $st$, and an outcome successor from the right summand to its image under $ex$. These are exactly the successors used in the directly defined transition. The equality follows in every phase, including the branches determined by the read symbols.
