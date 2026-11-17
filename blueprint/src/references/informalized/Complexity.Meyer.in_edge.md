<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.in_edge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-cell consistency at a machine step

**Claim.** If all local checks hold and the answer table correctly represents the configuration at time $t$, then the encoded input symbols at times $t$ and $t+1$ satisfy the consistency equalities dictated by the current state, head movement, and boundary condition.

**Proof.** Let $c$ be the configuration at time $t$. The proof first applies the local-check hypothesis to the input-step check at the encoded address for $e$. The correctness assumption for the tableau's state and scanned-symbol claims (`claims_of_correct`) makes the check's premise true, so the check forces its `inOK` condition. The signed-address identities `edge_c1` and `edge_c2`, together with the encoding-to-tableau-symbol correspondence `sv_sgn`, identify the four symbols appearing in this condition with the actual encoded symbols at positions $e$ and $e+1$, at times $t$ and $t+1$.

The proof then separates halted and nonhalted configurations, and in the latter case separates zero, right, and left head movement. A halted machine or a zero move imposes equality at both positions. For a right move, the clamping condition gives those same equalities; if it does not hold, the forced comparison says that the new symbol at $e$ equals the old symbol at $e+1$. For a left move, clamping again gives equality at both positions, while the unclamped comparison says that the new symbol at $e+1$ equals the old symbol at $e$. The address bookkeeping that converts the Boolean sign-and-magnitude encoding into $e$ and $e+1$ uses `avOf_ite`; expanding the encoded symbol selector via `symvA_NumVal` then yields exactly the stated cases.

**Key facts.** `Complexity.Meyer.claims_of_correct`, `Complexity.Meyer.edge_c1`, `Complexity.Meyer.edge_c2`, `Complexity.Meyer.sv_sgn`, `Complexity.Meyer.avOf_ite`, `Complexity.Meyer.symvA_NumVal`.
