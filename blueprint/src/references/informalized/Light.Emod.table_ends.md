<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.Emod.table_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Construction of a Doubling Table

**Claim.** Under the stated bounds, the table-building program reaches locals $[x,M,fr,a,r,M2^r]$ at cost at most $19r+6$, and the resulting memory stores $M2^j$ at each address $fr+j$ for $j<r$ while agreeing with the original memory below $fr$.

**Proof.** Maintain the invariant after $i$ iterations that the counter is $i$, the multiplier is $M2^i$, and the table entries at addresses $fr+j$ for $j<i$ contain $M2^j$; memory below $fr$ still agrees with its initial value. Initially $i=0$, the multiplier is $M$, and there are no table entries to check. The fixed-loop principle (`Ends.whileConst`) reduces the execution to verifying one round and the stopping condition. The bound $r\le \lfloor\log_2(V+1)\rfloor+1$ follows from $a\le V$ (`emodRounds_le`). Moreover, $M2^i\le a$ exactly when $i<r$ (`mul_two_pow_le_iff`), so at each iteration before $r$ the loop condition holds. The round stores the current multiplier at $fr+i$, increments the counter, and doubles the multiplier; thus the invariant extends by one entry, while addresses below $fr$ remain unchanged. At $i=r$, the same characterization shows that $M2^r\nleq a$, so the loop stops. The invariant then gives the required table and final locals, and the loop cost estimate gives the bound $19r+6$.

**Key facts.** `Light.emodRounds_le`, `Light.mul_two_pow_le_iff`, `Light.Ends.whileConst`.
