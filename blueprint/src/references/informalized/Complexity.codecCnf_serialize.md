<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnf_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for CNF serialization

**Claim.** If every variable in every clause of a CNF is mapped to an index less than $N$, then the binary serialization of the relabeled formula has length at most $\operatorname{cost}(\varphi)(N+3)+1$.

**Proof.** First, a literal relabeled to index $j<N$ serializes to a list of length $j+3$, hence at most $N+2$. For a clause $C$, summing this bound over its $|C|$ literals shows that the concatenated literal encodings have length at most $|C|(N+2)$. The clause serialization adds one terminating bit, and the formula format adds one leading bit per clause. Together these are bounded by $(|C|+1)(N+3)$, the clause's contribution to the claimed cost bound. Induct on the formula list: the empty formula serializes to the final single bit, while adjoining a clause adds its serialization length to that of the tail. Applying the clause bound and the induction hypothesis, and summing the contributions $(|C|+1)$, yields $\operatorname{cost}(\varphi)(N+3)+1$.
