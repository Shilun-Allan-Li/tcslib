<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_take_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix extraction from a pair encoding

**Claim.** For any bit strings $a$ and $b$, the prefix extractor started on the encoding that doubles each bit of $a$, appends the separator $01$, and then appends $b$, halts within $|\langle a,b\rangle|+1$ steps and outputs the first $|a|$ bits of $b$, or all of $b$ if $|b|<|a|$.

**Proof.** Write the input as $x=p b$, where $p$ consists of the doubled bits of $a$ followed by the separator $01$. The doubled block and separator have length $2|a|+2$, by the pair-encoding length formula (`Turing.universal_pair_length`). The extractor's initial configuration is exactly its designated starting configuration at the beginning of $x$.

After $2|a|+2$ steps, the parsing behavior lemma (`Complexity.tmsat_take_parse`) places the machine in state $3$, at the start of $b$, with the work tape representing $1^{|a|}$ and its head at $|a|-1$. From there, the payload behavior lemma (`Complexity.tmsat_take_payload`) applies for $j=\min(|a|,|b|)$: this many steps copy the first $j$ bits of $b$ to the output while keeping the machine in state $3$. Since $j$ is the smaller of the two lengths, those bits are exactly $b$ truncated to length $|a|$.

At that point the machine reads either the work-tape blank, if $b$ has ended, or the input blank, if it has copied $|a|$ bits. These alternatives are established by comparing the two lengths and locating the input position in $x=p b$. In either case the next transition halts and leaves the desired output unchanged. Thus it computes the output in $2|a|+2+\min(|a|,|b|)+1$ steps. The computation-time monotonicity theorem (`Turing.FinTM.ComputesInTime.mono`) extends this to the claimed bound: the encoding has length $2|a|+2+|b|$, and $\min(|a|,|b|)\le |b|$.

**Key facts.** `Turing.universal_pair_length`, `Complexity.tmsat_take_parse`, `Complexity.tmsat_take_payload`, `Complexity.tmsat_take_read`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.ComputesInTime.mono`.
