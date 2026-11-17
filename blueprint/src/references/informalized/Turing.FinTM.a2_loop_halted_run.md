<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_loop_halted_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-time loop evaluation

**Claim.** Under the stated round-by-round hypotheses and the terminal condition at index $N$, the run from $C_0$ halts within $NB$ steps and outputs the one-bit word indicating whether $P(j)$ holds for some $j<N$.

**Proof.** Proceed by induction on $N$, allowing the configuration sequence and predicate to vary. When $N=0$, the initial configuration is already $C_N$; take zero steps. The output is $[false]$, as required because the empty range has no accepting index.

For the successor case, first use the round hypothesis at index $0$ to obtain a time $t\le B$. If $P(0)$ holds, this round halts with output $[true]$. Its time is at most $NB\le (N+1)B$, and the disjunction over the first $N+1$ indices is true.

If $P(0)$ does not hold, the round reaches $C_1$ after $t$ steps. Apply the induction hypothesis to the shifted sequence $j\mapsto C_{j+1}$ and predicate $j\mapsto P(j+1)$, using the original terminal condition and round hypotheses at the shifted indices. It gives a further run of $s\le NB$ steps that halts with the output indicating whether some later index accepts. Concatenating the two runs gives $t+s\le B+NB=(N+1)B$. The identity expressing a run of $t+s$ steps as a run of $t$ steps followed by $s$ steps (`runFrom_add`) transfers the induction conclusion to the original run; since $P(0)$ is false, its output is exactly the required disjunction over all $N+1$ indices.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
