<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_parse_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding one doubled bit

**Claim.** When the input contains the doubled bit $bb$ immediately after the prefix, two steps of the loader parser append $b$ to the input buffer and return it to state $0$ at position $|pre|+3$, leaving the choice buffer empty.

**Proof.** Use the right-moving loader-transition lemma twice (`Complexity.cont_load_right`). At position $|pre|+1$, the next input symbol is $b$, as follows from $y=pre\,bb\,rest$. The parser's transition selects state $1$ or $2$ according to this bit, makes no buffer write, and moves right; the first application of the lemma therefore advances to position $|pre|+2$. At that position the next symbol is again $b$. The parser transition writes this bit to the input buffer, leaves the choice buffer unchanged, and returns to state $0$; the second application advances to position $|pre|+3$ and changes the buffer from $x$ to $x++[b]$. The two one-step transitions compose to the two-step run by the successor and zero-time run identities (`Turing.MultiTapeTM.runFrom_succ_eq_step` and `Turing.MultiTapeTM.runFrom_zero`).

**Key facts.** `Complexity.cont_load_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
