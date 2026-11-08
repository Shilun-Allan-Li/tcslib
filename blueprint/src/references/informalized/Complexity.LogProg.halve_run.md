<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.halve_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated halving after a countdown

**Claim.** Starting with $c=k$ and all registers bounded by $B$, the program reaches the configuration at $l_x$ with $c$ cleared and $r$ replaced by $v(r)/2^{v(c)}$, while the guard holds at every earlier configuration.

**Proof.** Proceed by induction on $k$. If $k=0$, the zero branch goes directly from $l$ to $l_x$. Since $v(c)=0$ and $c\ne r$, the two updates in the claimed target leave the register assignment unchanged; the run therefore ends at the desired configuration after this one step. The starting configuration satisfies the guard because its registers are bounded and the instruction at $l$ has no additional precondition. For the successor case, write $v(c)=k+1$. The zero test takes its positive branch to $l_1$, the decrement changes $c$ to $k$, and the half instruction changes $r$ to $v(r)/2$. The updated assignment remains bounded: $k\le B$, and halving cannot increase a natural number. It also satisfies the program precondition at $l_2$. Apply the induction hypothesis to this assignment. Its resulting value of $r$ is $(v(r)/2)/2^k=v(r)/2^{k+1}$, using the natural-number identity that successive division by powers of two combines into division by their product. The value of $c$ is zero, and because $c$ and $r$ are distinct, the target's two updates agree with this result. The three configurations preceding the recursive run satisfy the guard by the initial register bound, the decrement bound, and the fact that the half instruction has no additional precondition. The reachability step lemma composes these transitions with the inductive run, and equality of the final configurations identifies its endpoint with the claimed target.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.reach_of_eq`.
