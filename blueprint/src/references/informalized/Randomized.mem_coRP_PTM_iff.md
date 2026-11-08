<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_coRP_PTM_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# coRP Verifier Characterization

**Claim.** A language belongs to polynomial-time coRP exactly when its complement has a polynomial-time RP verifier with acceptance probability at least $2/3$ on complement members and certain rejection outside the complement.

**Proof.** Apply the RP verifier characterization to the complement language $L^c$. By definition, membership of $L$ in coRP is membership of $L^c$ in RP, and `mem_RP_PTM_iff` characterizes the latter as `InRP polyTimeModel L^c`. By definition, this is exactly `InCoRP polyTimeModel L`.

**Key facts.** `Randomized.mem_RP_PTM_iff`.
