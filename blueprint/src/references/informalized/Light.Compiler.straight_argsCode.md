<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.straight_argsCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straight instructions in argument code

**Claim.** For every finite list of expressions and every natural number $k$, each instruction in the code compiling that list starting at $k$ is straight.

**Proof.** Proceed by induction on the expression list. For the empty list, the argument code is empty, so there are no instructions to check. For a nonempty list $e::es$, its code is the concatenation of the code for $e$ at slot $k$ and the code for the remaining list $es$ at slot $k+1$. Every instruction in the first part is straight by `Light.Compiler.straight_compileExpr`; every instruction in the second part is straight by the induction hypothesis. Therefore every instruction in the concatenation is straight.

**Key facts.** `Light.Compiler.straight_compileExpr`.
