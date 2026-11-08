<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftOver_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Under Lifting

**Claim.** For configurations $D$ on $x$ and $c$ on an equal-length Boolean input, the output of the configuration obtained by lifting $c$ over $D$ is the concatenation of $D$'s output with the symbolwise image under $e$ of $c$'s output.

**Proof.** The definition of lifting assigns the output to be the output of $D$ followed by the symbolwise image under $e$ of the output of $c$. The claimed equality is therefore exactly this defining equation.
