<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.sum_fullCoefficient_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the coefficient sum

**Claim.** For every natural number $k$, the sum of the first $k$ shifted full coefficients is at most $13420/15309$.

**Proof.** Check the first four values of $k$ directly; for the first three coefficients the sum is $4/9+8/27+224/2187$. For larger $k$, split off those first three terms. Each later coefficient, with index at least four, is bounded by $(32/3)(2/9)^i$ (the coefficient-tail bound, `FABL.SwitchingCode.fullCoefficient_tail`). The resulting tail is a constant multiple of a finite geometric sum: factor out $(32/3)(2/9)^4$ and sum the powers $(2/9)^x$. This geometric sum is at most $9/7$ (`FABL.SwitchingCode.geometric_two_ninths_bound`). Combining this bound with the first three terms gives $13420/15309$.

**Key facts.** `FABL.SwitchingCode.fullCoefficient_tail`, `FABL.SwitchingCode.geometric_two_ninths_bound`.
