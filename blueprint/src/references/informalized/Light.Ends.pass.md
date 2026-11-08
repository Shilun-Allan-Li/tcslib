<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Pass.lean :: Light.Ends.pass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Memory Pass

**Claim.** Under the stated safety, evaluation, memory-space, local-variable, and cost hypotheses, the pass that writes the first $n$ values of $f$ starting at $\mathrm{dst}$ executes within cost $T$ and ends in a state satisfying $Q$.

**Proof.** Apply the bounded loop theorem `Light.Ends.forMem` to the loop counter $c$, with invariant that after $j$ iterations the memory is exactly the memory obtained by writing the first $j$ values of $f$. The initial invariant holds because writing zero values leaves the initial memory unchanged (`Light.wrote_zero`). For the $j$th iteration, the invariant identifies the current memory as the required prefix. The hypotheses `round` give safety of the expression and its value $f(j)$. Since $x$ and $y$ differ from $c$, updating the counter leaves their values unchanged: the length expression still evaluates to $n$, and the destination expression to $\mathrm{dst}$. The store address is therefore $\mathrm{dst}+j$; it is valid because $j<n$ and $\mathrm{dst}+n\le\mathrm{lim.space$. The space bound and `Light.Limits.Addr.abs_le` ensure the address is within the word limit, so the store expression is safe. Executing the store updates the memory to the prefix of length $j+1$ by `Light.toNat_natCast_add_natCast` and `Light.wrote_succ`; the loop body also leaves the counter at $j$, as required by the loop theorem’s round postcondition. The supplied bound on $\mathrm{loc}(x)$ and the unchanged-local facts meet that theorem’s loop-condition hypotheses, and the total cost bound follows from $n(\mathrm{cost}(e)+12)+6\le T$. At termination, the invariant gives the length-$n$ written memory, and `done` gives $Q$ for the resulting state.

**Key facts.** `Light.Ends.forMem`, `Light.wrote_zero`, `Light.Limits.Addr.abs_le`, `Light.toNat_natCast_add_natCast`, `Light.wrote_succ`.
