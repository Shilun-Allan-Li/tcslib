<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Suffix into the Choice Buffer

**Claim.** When $y=\mathrm{pre}\,r$, the pair-loader in state $3$, positioned just after $\mathrm{pre}$ and with buffers $x,u$, copies the suffix $r$ into the choice buffer in exactly $|r|$ steps, reaching the stated configuration with input position $|y|+1$ and empty output.

**Proof.** Induct on the suffix $r$. If it is empty, the run takes zero steps, so the initial and target configurations agree. For the inductive step, write $r=b::r'$. Since $y=\mathrm{pre}\,b::r'$, the next input symbol at the current position is $b$. The loader’s state-$3$ transition copies this symbol to the choice buffer, advances the input and choice heads by one, and leaves the input buffer, the other tape contents, and the output unchanged (`cont_load_right`). This gives the claimed configuration for the shorter suffix $r'$, with prefix extended to $\mathrm{pre}\,b$ and choice buffer extended to $u\,b$. Apply the induction hypothesis to those updated data. The suffix length and concatenation identities identify its endpoint with the required configuration for $ur$.

**Key facts.** `Complexity.cont_load_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
