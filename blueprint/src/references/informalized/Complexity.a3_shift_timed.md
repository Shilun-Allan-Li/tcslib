<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_shift_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time bound for the Boolean shift function

**Claim.** For every fixed Boolean word $w$, the shift machine computes $x\mapsto 0^{|x|}\mathbin{++}w$ on every Boolean word $x$ within $(|w|+2)(|x|+1)$ steps.

**Proof.** For each input $x$, the exact-time result gives computation of the required output in $|x|+|w|+2$ steps (Complexity.a3_shift_computes). This is at most $(|w|+2)(|x|+1)$, as follows by expanding the product and using the nonnegativity of the lengths. Computation within a given time remains valid at any larger time (Turing.FinTM.ComputesInTime.mono), so the exact-time computation implies the stated bound.

**Key facts.** `Complexity.a3_shift_computes`, `Turing.FinTM.ComputesInTime.mono`.
