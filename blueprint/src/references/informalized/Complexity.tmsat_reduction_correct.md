<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_reduction_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the TMSAT reduction

**Claim.** Under the stated witness characterization of $L$ and machine correctness hypothesis, a string $x$ belongs to $L$ exactly when its specified nested encoding belongs to $\mathrm{TMSAT}_c$.

**Proof.** Fix $x$. For the forward implication, the witness characterization supplies $u$ with the required length and with $x u\in V$. Use $\alpha,x,u$ and the specified unary encodings of the witness length and time as the existential data for membership in $\mathrm{TMSAT}_c$. The encoding equality and witness-length condition hold by construction. The machine hypothesis gives the required computation: since $x u\in V$, its indicator is $1$, so the output is $[1]$.

For the reverse implication, take witnesses $\beta,y,u,n,t$ for membership in $\mathrm{TMSAT}_c$. Equality of the nested encodings and injectivity of that encoding (`Complexity.tmsat_quad_injective`) identify $\beta=\alpha$, $y=x$, $n=C(|x|+1)^e$, and $t=T(|x|)$. Substituting the identified length into the witness condition gives $|u|=C(|x|+1)^e$. The witnessed computation and the computation supplied by the machine hypothesis have the same input and time, so their outputs agree by uniqueness of output for a machine (`Turing.FinTM.ComputesInTime.output_unique`). The latter output is the one-bit indicator of $x u\in V$. Since the witnessed output is $[1]$, this indicator is true, and thus $x u\in V$. The witness characterization of $L$ now implies $x\in L$.

**Key facts.** `Complexity.tmsat_quad_injective`, `Turing.FinTM.ComputesInTime.output_unique`.
