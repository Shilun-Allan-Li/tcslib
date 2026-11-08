<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairValid_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity Tester Halting Bound

**Claim.** If $x=p\,r$, then from the block state at position $|p|$ with empty output, the validity tester halts within $|r|+1$ steps and outputs the bit indicating whether the aligned pair parser decodes $r$.

**Proof.** We induct on the length of the remaining word, using the two step induction that separates the empty word, a singleton, and a word beginning with two bits. If the remainder is empty, one transition reads the end marker and halts; the output is the parser’s success bit for the empty word. If it is a singleton, the first transition advances past that bit and the next reads the end marker and halts. In each case the machine’s transition table gives the claimed output, and the number of steps is at most the remainder length plus one.

Now suppose the remainder begins $b,c$. If $b=c$, the two-step block behavior (the fact that two matching bits are consumed and the machine returns to the block state, `pairValid_block`) reduces the run to the induction hypothesis on the suffix, with prefix extended by $[b,b]$. Thus the suffix run halts with the correct result, since the parser prepends the common bit to its decoded first component, and the total time is $2+t\le |r|+1$. If $b\ne c$, the same block behavior halts after two steps and emits the bit $\neg b\land c$. Among unequal Boolean pairs, this is true exactly for $(b,c)=(\mathrm{false},\mathrm{true})$, the parser’s delimiter case; otherwise the parser fails. Hence the output is precisely the parser’s success indicator, and two steps satisfy the bound for this case.

**Key facts.** `Turing.FinTM.pairValid_block`, `Turing.FinTM.scanCfg_read`.
