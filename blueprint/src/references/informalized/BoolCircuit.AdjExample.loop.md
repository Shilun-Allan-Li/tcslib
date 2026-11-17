<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean :: BoolCircuit.AdjExample.loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Space Comparison Loop

**Claim.** For all $a,b,n,i$ and all $c,d$ with $c+d=n$ and $c\le i$, the comparison program started in its test state with register value $c$ halts with the specified Boolean answer, maintains its invariant, and keeps its register within the stated bound.

**Proof.** Fix the input $y=\langle 1^n,\operatorname{bits}(i)\rangle$. Its payload is valid and canonical (`canon_bits`), and its plain payload is exactly $\operatorname{bits}(i)$ (`plainWord_pairEncode`). Throughout the loop, when the program is in any of its states with register value $c\le n$, its invariant holds: the only nontrivial input check is valid by the preceding fact, and the register is at most $|y|+1$. The latter follows because $n\le |y|$ (`pairEncode_eq_dbl`, `dbl_replicate`). At a test state, the oracle answers whether $c<n$ (`astep_call₁`, `orc_eq`). If $c<n$, the program compares the register’s bit word to the input payload; injectivity of natural-number bit words makes this comparison equivalent to $c=i$. If they agree, then $i<n$ and the program returns $a$. If they do not, it increments $c$ and repeats. This maintains $c\le i$ and the condition that the remaining distance to $n$ decreases by one. Formally, induct on $d$ with $c+d=n$. When $d=0$, $c=n$: the strict-comparison test fails, and the payload comparison returns $b$ exactly when $i=n$, otherwise false. When $d>0$, the strict-comparison test succeeds; equality returns $a$ exactly when $i=c$, and otherwise the program increments the register and invokes the induction hypothesis with $c+1$ and $d-1$. Each transition preserves the invariant and register bound (`AHalt.step`), and the terminal return is justified by `AHalt.ret`.

**Key facts.** `Complexity.LogProg.canon_bits`, `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.plainWord_pairEncode`, `Complexity.LogProg.astep_call₁`, `BoolCircuit.AdjExample.orc_eq`, `Complexity.LogProg.bits_injective`, `BoolCircuit.AdjExample.upd_const`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AHalt.ret`.
