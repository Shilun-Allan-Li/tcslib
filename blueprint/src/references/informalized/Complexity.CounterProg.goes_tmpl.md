<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_tmpl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Template Sequence

**Claim.** A program whose labels implement the prescribed template instructions reaches the designated next label after executing the template, with registers and input position unchanged and the template output appended, in at most $n+1$ steps.

**Proof.** Prove a stronger statement by induction on the number $d$ of remaining template positions: whenever $i+d$ equals the template length, execution from label $\mathrm{lab}(i)$ reaches the designated next label, appends the output of the suffix beginning at $i$, and uses at most $d+1$ steps. For $d=0$, the template has ended at index $i$, so its prescribed instruction is a jump to the next label. The jump reachability fact (\texttt{goes\_goto}) gives the result in one step, and the remaining suffix is empty. For the successor case, $i$ is strictly before the end. Thus the prescribed instruction at $i$ is either a bit-print instruction or a unary-register-print instruction. In the first case, the one-step output fact (\texttt{goes\_out}) appends that bit; in the second, the unary-print fact (\texttt{goes\_pr}) appends the register's unary string. In each case the program then reaches label $\mathrm{lab}(i+1)$, with registers and input position unchanged. Apply the induction hypothesis to the remaining suffix from that label. Concatenating the two executions appends the head operation's output followed by the suffix output, and takes at most the sum of their bounds (\texttt{Goes.trans}); this sum is at most $d+2$, the required bound for the successor case (\texttt{Goes.mono}). Finally, take $i=0$ and $d=n$.

**Key facts.** `Complexity.CounterProg.goes_goto`, `Complexity.CounterProg.goes_out`, `Complexity.CounterProg.goes_pr`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.mono`.
