<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix extraction time and output

**Claim.** On the pair encoding of Boolean words $u$ and $v$, the suffix-extraction machine halts after exactly $3(|\langle u,v\rangle|+1)$ steps and outputs the word obtained from $v$ by deleting its first $|u|$ bits.

**Proof.** Set $x=\langle u,v\rangle$ and $p=2|u|+2$. Split the encoded input as $x=\mathrm{pre}++v.drop(|u|)$, where $\mathrm{pre}=\mathrm{satBits}(u)++[\mathrm{false},\mathrm{true}]++v.take(|u|)$. Since the encoding doubles each bit of $u$ and then inserts a two-bit separator, $|x|=p+|v|$ and $|\mathrm{pre}|=p+\min(|u|,|v|)$. Consequently the clamped stream positions at offset $p+|u|$ and at $|\mathrm{pre}|$ agree, whether $|u|\le |v|$ or $|v|\le |u|$.

The parser processes the doubled prefix and reaches the separator state; the separator transition, rewind, skip, and dispatch steps then place the machine in state $5$ at the start of $\mathrm{pre}$, with its counter and head at $|u|$ and empty output. These are precisely the transitions supplied by Complexity.satDrop_parse, Complexity.satDrop_separator, Complexity.satDrop_rewind, Complexity.satDrop_skip, and Complexity.satDrop_dispatch, composed using the run-concatenation law Turing.MultiTapeTM.runFrom_add. The initial configuration agrees with the stated starting configuration by direct comparison of their components.

Now Complexity.satDrop_copy applies to the decomposition $x=\mathrm{pre}++v.drop(|u|)$. After $|v.drop(|u|)|+1$ more steps it halts, leaves the counter unchanged, and appends the remaining suffix to the output. The exact total time is therefore $2|u|+2+(|u|+1)+|u|+1+(|v.drop(|u|)|+1)$. The run is characterized by its halting state and output through Turing.FinTM.computesInTime_iff. Finally, the machine's computation can be extended to the requested time by Turing.FinTM.ComputesInTime.mono, since the displayed total is at most $3(|x|+1)$ using $|x|=2|u|+2+|v|$ and $|v.drop(|u|)|\le |v|$.

**Key facts.** `Complexity.satBits_length`, `Complexity.satDrop_parse`, `Complexity.satDrop_separator`, `Complexity.satDrop_rewind`, `Complexity.satDrop_skip`, `Complexity.satDrop_dispatch`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.satDrop_copy`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
