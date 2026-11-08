<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transducer startup configuration

**Claim.** For every CNF formula, the transducer started on its serialization reaches state $9$ with input head at position $1$, counter length equal to the formula's number of variables and head at zero, the specified empty-word buffer and head at zero, and empty output, within the stated time bound.

**Proof.** Let $x$ be the serialization of the formula. First use the maximum-scan theorem for formulas (\texttt{Complexity.satRed\_maxFormula}) with empty prefix and suffix, initial counter length zero, and the specified buffer. In some $s\le 2|x|$ steps this reaches state $7$ at input position $|x|-1$, with counter length equal to the formula's number of variables and all other listed tape and output data unchanged. The initialization theorem (\texttt{Complexity.satRed\_init}) says the machine reaches the corresponding state-$2$ starting frame in two steps. From the state-$7$ frame, the timed rewind theorem (\texttt{Turing.FinTM.timed\_rewind}) applies: the transition rules in states $7$ and $8$ move the input head left through the input, then right once at the left boundary and enter state $9$. It supplies a rewind duration $r\le c.inputPos+2$ and restores the same frame's tape contents, heads, and output, with state $9$ and input head at position $1$. Combining initialization, formula scan, and rewind by run addition gives total time $2+s+r$. Since the scan ends at position $|x|-1$, the rewind bound and $s\le 2|x|$ imply $2+s+r\le 3|x|+5$.

**Key facts.** `Complexity.satRed_init`, `Complexity.satRed_maxFormula`, `Turing.FinTM.timed_rewind`, `Turing.MultiTapeTM.runFrom_add`.
