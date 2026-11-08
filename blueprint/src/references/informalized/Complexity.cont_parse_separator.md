<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_parse_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recognizing the Pair Separator

**Claim.** When the input after prefix $pre$ begins with $0,1$, the pair loader consumes those two bits and reaches parser state $3$, preserving the input buffer and the other prescribed loader data.

**Proof.** The proof tracks the two transitions separately. At input position $|pre|+1$, the next symbol is $0$. The one-step loading result (`Complexity.cont_load_right`) applies to this transition: it moves from parser state $0$ to state $1$, advances the input head, and leaves both buffers unchanged. At the next position the symbol is $1$, so the same result applies again, now from state $1$ to state $3$. It advances the head once more and again leaves the buffers unchanged. The two-step run is exactly these successive transitions.

**Key facts.** `Complexity.cont_load_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
