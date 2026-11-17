<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.EXP_subset_POracle_EXPCOM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time with an Exponential-Time Oracle

**Claim.** Every language in $\mathrm{EXP}$ belongs to $\mathsf{P}^{\mathrm{EXPCOM}}$.

**Proof.** Let a language in $\mathrm{EXP}$ be decided by a machine $M$ within $a2^{n^c}$ steps. Convert it to an equivalent one-work-tape binary machine $M'$ with a bound $b(a2^{n^c}+1)^2$, using `one_work_tape_binary`, and then choose a code $N$ for $M'$ using `exists_codeTM`. Set $C=b+2(a+1)+2$. By `expcom_padding_bound` and time monotonicity (`ComputesInTime.mono`), $N$ decides the language within $2^{C(n+1)^c}$ steps. Now map input $x$ to the encoding of the fixed code for $N$ together with $x$ and a unary padding string of length $C(|x|+1)^c$. This map is polynomial-time computable: the constant code, identity map, and polynomial unary-padding map are polynomial-time computable, and pair encoding preserves polynomial-time computability (`PolyTimeComputable.pairEncode`). The reduction is correct because the encoded query asks whether $N$ accepts within $2^{C(|x|+1)^c}$ steps. If $x$ is in the language, the time bound makes the answer positive. Conversely, if the query is positive, `output_unique` ensures that $N$'s bounded computation produces the same output as its decider computation, so its acceptance output implies $x$ is in the language. Thus this is a polynomial-time reduction to $\mathrm{EXPCOM}$, and `mem_POracle_of_polyTimeReducible` places the original language in $\mathsf{P}^{\mathrm{EXPCOM}}$.

**Key facts.** `Turing.FinTM.one_work_tape_binary`, `Turing.exists_codeTM`, `Complexity.expcom_padding_bound`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_polyUnary`, `Turing.MachineCode.decode_encode`, `Turing.pairEncode_injective`, `Turing.FinTM.ComputesInTime.output_unique`, `Complexity.mem_POracle_of_polyTimeReducible`.
