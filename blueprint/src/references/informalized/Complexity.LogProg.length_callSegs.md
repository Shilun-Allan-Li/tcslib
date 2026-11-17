<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Program.lean :: Complexity.LogProg.length_callSegs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Call Segmentation

**Claim.** For a call specification with an argument list of length $q$, the resulting list of call segments has length $q+1$.

**Proof.** The call segmentation consists of the mode-dependent first segment followed by the argument segmentation of the words selected by the argument list. The first segment contributes one element. Argument segmentation preserves the length of its input list (`Complexity.LogProg.length_argSegs`), and mapping the register-to-word assignment over the argument list preserves that list's length. Thus the total is $1+q=q+1$.

**Key facts.** `Complexity.LogProg.length_argSegs`.
