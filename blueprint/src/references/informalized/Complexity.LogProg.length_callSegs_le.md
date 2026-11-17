<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.length_callSegs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Encoded Call Words

**Claim.** Under the stated length bound on register words and the no-repetition condition on the selected register list, the virtual call word has length at most $2|x|+2+m(2W+2)$.

**Proof.** First bound the virtual word's length by the sum of the segment lengths, measured by $rlen$, plus two symbols per segment (`Complexity.LogProg.length_vword_le`). The first segment contributes at most $2|x|$: in whole-input mode its rendered length is twice the input length, and in unary-first mode the initial run of ones has length at most $|x|$. The argument segments contribute at most $q(2W)$ in total, where $q$ is the number of listed registers (`Complexity.LogProg.sum_rlen_argSegs_le`), since each assigned word has length at most $W$. The no-repetition condition gives $q\le m$. Also, the number of argument segments equals the number of listed registers (`Complexity.LogProg.length_argSegs`), so the total number of segments is $q+1$. Consequently the bound is at most $2|x|+q(2W)+2(q+1)$. Using $q\le m$ and rearranging yields $2|x|+2+m(2W+2)$.

**Key facts.** `Complexity.LogProg.length_vword_le`, `Complexity.LogProg.sum_rlen_argSegs_le`, `Complexity.LogProg.length_argSegs`.
