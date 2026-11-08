<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_pt_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time truncation

**Claim.** If $f$ and $g$ are polynomial-time computable, then $x\mapsto (g(x)).take\,|f(x)|$ is polynomial-time computable.

**Proof.** 1. First compute both $f(x)$ and $g(x)$ together by the polynomial-time pair-encoding closure theorem (`Complexity.PolyTimeComputable.pairEncode`). On the resulting encoding, a fixed machine extracts the prefix of the second component whose length is the length of the first. The truncation machine’s running time is bounded by the encoded input length plus one (`Complexity.tmsat_take_computes`). The encoded input supplied by the first machine has length at most its running time, since a machine’s output length is at most its number of steps (`Turing.MultiTapeTM.output_length_le`). Thus the truncation machine can be run for its required time within a bound given by the first computation’s time plus one (`Turing.FinTM.ComputesInTime.mono`).

2. Compose the machine producing the encoded pair with the truncation machine. The composition theorem gives a machine for the desired function with time bounded by twice the first time bound, plus the truncation time bound and a constant (`Turing.FinTM.exists_comp_on_image`). The first bound has the form $C(|x|+1)^e$; the second is at most that quantity plus one. Since $(|x|+1)^e\ge 1$, the resulting bound is at most $3(C+1)(|x|+1)^e$. This is a polynomial bound, proving polynomial-time computability.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.tmsat_take_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.exists_comp_on_image`.
