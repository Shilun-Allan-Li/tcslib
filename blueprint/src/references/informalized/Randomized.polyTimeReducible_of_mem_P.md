<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.polyTimeReducible_of_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction from a Polynomial-Time Language

**Claim.** If $L'$ belongs to polynomial time and $L$ contains some string $a$ while omitting some string $b$, then $L'$ is polynomial-time many-one reducible to $L$.

**Proof.** Because $L'$ is in $	extsf P$, its membership indicator is polynomial-time computable (`Complexity.mem_P_iff_polyTimeComputable`). Define the reduction to output $a$ when the indicator says the input is in $L'$, and $b$ otherwise. This piecewise choice is polynomial-time computable from the indicator and the two constant-output functions (`Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`). If $x\in L'$, the output is $a\in L$; if $x\notin L'$, the output is $b\notin L$. In either case, the output lies in $L$ exactly when $x$ lies in $L'$, proving the reduction.

**Key facts.** `Complexity.mem_P_iff_polyTimeComputable`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`.
