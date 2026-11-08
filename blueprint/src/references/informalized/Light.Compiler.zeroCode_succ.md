<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.zeroCode_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Zero-Code Blocks

**Claim.** For every natural number $F$, the code that initializes $F+1$ stack cells is the code that initializes the first $F$ cells followed by the instruction that subtracts the value in the constant-one cell from itself and stores the result in the stack cell indexed by the main-frame offset plus $F$.

**Proof.** The range of indices below $F+1$ consists of the indices below $F$, followed by the single index $F$. Mapping the zeroing instruction over this split list gives the first $F$ instructions followed by the subtraction instruction targeting `cStack (mainFrame + F)`, as claimed.
