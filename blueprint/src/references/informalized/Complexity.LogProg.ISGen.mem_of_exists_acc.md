<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.mem_of_exists_acc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from a Reachable Accepting Code

**Claim.** If a code is reachable from the initial configuration code by zero or more valid steps within a fixed window and encodes an accepting configuration in that window, then $x\in L$.

**Proof.** Unpack the hypothesis to obtain a code $t$, its reachability path from the initial code, and its accepting-code witness. The initial code satisfies the initial-language condition by `mem_initLang`. Apply the decision principle for code paths (`Complexity.Codec.mem_of_codePath`) to this initial-code witness, the reachability path, and the accepting-code witness; it concludes that $x$ belongs to $L$.

**Key facts.** `Complexity.Codec.mem_initLang`, `Complexity.Codec.mem_of_codePath`.
