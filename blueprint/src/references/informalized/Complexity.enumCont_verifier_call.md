<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_verifier_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepared Verifier Call Bound

**Claim.** Starting from the canonical seam configuration with $s$ on the work tape and input $x$, the buffered composition of the assembly machine with $M_V$ halts with output the indicator of $x\mathbin{++}s\in V$ within the stated time bound.

**Proof.** Apply the buffered-composition time bound (`enumCont_prepared_comp`) to the concatenation machine and $M_V$. The concatenation machine, started with input $x$ and work tape $s$, halts after $|x|+|s|+2$ steps and outputs $x\mathbin{++}s$ (`enumCont_concat_run`). The hypothesis that $M_V$ decides $V$ supplies its halting computation on this concatenated word, with the required indicator as output. The seam identity (`enumCont_round_seam`) identifies the buffered first-phase starting configuration with the canonical configuration specified in the claim. The composition bound is therefore $|x|+|s|+2+|x\mathbin{++}s|+2+T_V(|x\mathbin{++}s|)$; using $|x\mathbin{++}s|=|x|+|s|$ gives the asserted bound.

**Key facts.** `Complexity.enumCont_prepared_comp`, `Complexity.enumCont_concat_run`, `Complexity.enumCont_round_seam`.
