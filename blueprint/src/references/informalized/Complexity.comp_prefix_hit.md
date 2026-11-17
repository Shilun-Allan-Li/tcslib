<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_prefix_hit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix-Match Halt Result

**Claim.** On input $\langle\langle x,b\rangle,\mathrm{bits}(p)\rangle$, the machine started in the prefix-match state halts with answer true if mode is true; otherwise it returns the bit of $f(x)$ at index $\lfloor v(0)/2\rfloor$, with an out-of-range bit interpreted as false. Every configuration before halting satisfies the precondition and register bound.

**Proof.** When mode is true, the prefix-match instruction returns true immediately. The initial configuration is admissible by \texttt{comp\_preS} and bounded by the hypothesis, so the immediate-return principle (\texttt{AHalt.ret}) proves this case.

When mode is false, the instruction halves register 0 and proceeds to the prefix-bit state. Let $v'$ be the resulting vector, so $v'(0)=\lfloor v(0)/2\rfloor$. Since halving cannot increase a natural number, all entries of $v'$ remain at most $B$; this follows formally from \texttt{register\_update\_le}. The call-return result (\texttt{comp\_call\_return}) reduces the subsequent computation to the oracle's answer on the encoded input and the binary representation of $v'(0)$. The lifted-oracle identity (\texttt{comp\_lifted}) identifies that answer with the bit of $f(x)$ at index $v'(0)$. Prefixing the initial halving instruction via \texttt{AHalt.step} proves the result, and \texttt{comp\_preS} supplies admissibility at the initial configuration.

**Key facts.** `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.register_update_le`, `Complexity.comp_call_return`, `Complexity.comp_lifted`, `Complexity.comp_preS`, `Complexity.LogProg.AHalt.step`.
