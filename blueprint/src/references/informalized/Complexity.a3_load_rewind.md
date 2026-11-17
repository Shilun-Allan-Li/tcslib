<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_load_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding After Loading a Word

**Claim.** For every $j\leq \operatorname{length}(x)$, starting in phase $1$ with the input head at $j$ and tape zero’s head at $j-1$, the wrapper reaches phase $2$ after $j+1$ steps, with its input head at $1$, tape zero containing $x$ with its head at zero, all other work tapes blank with their heads at zero, and empty output.

**Proof.** Proceed by induction on $j$. For $j=0$, split the run into its first step and the remaining zero steps. The input head starts at the left end, so the phase-$1$ transition sees no input symbol and moves tape zero’s head left; at position $-1$ that tape is blank. The next phase-$1$ transition therefore moves the tape-zero head right into phase $2$. The input head is now at position $1$, the tape-zero head is back at zero, and its contents and all other tapes are as required. The output remains empty.

For the successor case, suppose the claim holds for $j$, and start instead with the input head at $j+1$ and tape-zero head at $j$. Since $j<\operatorname{length}(x)$, the symbol under the input head is $x_j$. The phase-$1$ transition writes that same symbol at the tape-zero head and moves both heads one position left, leaving the machine in phase $1$. Thus this single step changes the configuration exactly to the prescribed starting configuration for index $j$: the tape content is still $x$, the input head is at $j$, and tape-zero head is at $j-1$. The induction hypothesis supplies the remaining $j+1$ steps to phase $2$. Together with the first step, this gives $(j+1)+1$ steps, as claimed.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_neg_val`.
