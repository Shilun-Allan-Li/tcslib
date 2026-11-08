<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairValid_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair validity run bound

**Claim.** Given bit strings $x,r$ and a prefix $p$ with $x=p++r$, the constructed machine started just after $p$ halts within $|r|+1$ steps and outputs the one-bit indicator of whether the pair parser succeeds on $r$.

**Proof.** Use induction on the suffix $r$, grouped into the empty word, a singleton, and a two-bit prefix followed by a shorter suffix. For the empty suffix, one transition reads the end marker and halts with the parser's failure indicator. For a singleton, the machine takes two steps: the first moves across the bit, and the next transition halts with the correct result; the one-bit parser equations verify both possible bit values. Now write a longer suffix as $b::c::r'$. The two-step block calculation (`f2_pairValid_block`) describes what happens after reading $b,c$. If $b\ne c$, that block halts and emits the parser's indicator, as is checked against the parser's cases. If $b=c$, it advances to the start of the remaining suffix, without output, in the scanning state. Apply the induction hypothesis to $r'$ from that new configuration, and prepend the two steps. The parser equations identify the result on $b::c::r'$ with the result on $r'$ in this equal-bit case, and the total time is at most $2+(|r'|+1)=|b::c::r'|+1$.

**Key facts.** `Turing.FinTM.f2_scanStep_right`, `Turing.FinTM.f2_scanCfg_read`, `Turing.FinTM.f2_pairValid_block`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
