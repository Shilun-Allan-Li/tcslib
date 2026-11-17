<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_take_parse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing the encoded first component

**Claim.** When $x=p\langle a,b\rangle$, the extractor starting at the end of $p$ in state $0$ reaches state $3$ after $2|a|+2$ steps, with the work tape extended by $|a|$ unary marks, its work head at $m+|a|-1$, and empty output.

**Proof.** Induct on the bit string $a$. If $a$ is empty, the encoding begins at the current position with the separator $01$. Its first two bits are therefore $0$ and $1$, and the separator behavior lemma (`Complexity.tmsat_take_separator`) shows that after two steps the machine is in state $3$, with the head advanced over the separator and the work head moved to $m-1$. This is the asserted configuration when $|a|=0$.

For the inductive step, write $a=v::a'$. The encoding begins with the doubled block $vv$, followed by the encoding of $a'$. The two bits at the current input positions are both $v$. The doubled-block behavior lemma (`Complexity.tmsat_take_double`) shows that after two steps the machine remains in state $0$, advances past this block, and increases the unary work-tape length and work-head position from $m$ to $m+1$. Apply the induction hypothesis to the remaining encoding, now starting after $vv$ with work parameter $m+1$. It takes $2|a'|+2$ further steps and reaches state $3$ with the claimed tape, head, and output. Adding the initial two steps gives $2|a|+2$; the stated final positions follow by substituting $|a|=|a'|+1$. The time decomposition is justified by the run composition rule (`Turing.MultiTapeTM.runFrom_add`).

**Key facts.** `Complexity.tmsat_take_separator`, `Complexity.tmsat_take_double`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universal_pair_length`.
