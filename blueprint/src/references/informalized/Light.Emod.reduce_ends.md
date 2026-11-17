<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.Emod.reduce_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Execution of Remainder Reduction

**Claim.** Under the stated machine bounds and table assumptions, the remainder-reduction program reaches locals $[x,M,fr,a\bmod M,0,t]$ without changing memory, at cost at most $24r+4$, where $r$ is the binary size of $\lfloor a/M\rfloor$.

**Proof.** Use a loop invariant indexed by the number $i$ of completed rounds: the rest value is some $q$ with $q<M2^{r-i}$, its residue modulo $M$ is $a\bmod M$, and the counter is $r-i$; memory remains $\mu'$. Initially take $q=a$. The bound $a<M2^r$ follows from the defining size of the quotient, and the residue condition is immediate. The round bound $r\le \lfloor\log_2(V+1)\rfloor+1$ follows from $a\le V$ (the estimate `emodRounds_le`). The characterization $M2^i\le a$ exactly when $i<r$ (`mul_two_pow_le_iff`) supplies the power-of-two comparisons needed at each round and ensures that the table entry for the current counter exists.

Apply the fixed-iteration loop principle (`Ends.whileConst`) to execute exactly $r$ rounds. In a round with counter $c+1$, the table contains $m=M2^c$. If $m\le q$, the conditional subtracts $m$ from the rest; the result is still below $m$, hence below the next threshold $2m$, and its residue modulo $M$ is unchanged because $m$ is a multiple of $M$. If $m>q$, the conditional skips the subtraction, and $q<m<2m$ gives the next bound while preserving the residue. The counter decreases in either case, and memory is untouched. At termination the counter is zero and the invariant gives $q<M$. Since $q\equiv a\pmod M$, it follows that $q=a\bmod M$, proving the stated final locals. The loop cost estimate together with the round bound yields the advertised budget.

**Key facts.** `Light.emodRounds_le`, `Light.mul_two_pow_le_iff`, `Light.Ends.whileConst`, `Light.Ends.iteLast`, `Light.Ends.setTo`, `Light.Ends.skip`.
