<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.ups_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Scan Invariant

**Claim.** Under the stated register, pointer, counter, and size bounds, if every next-row configuration has acceptance probability $q$, then the row-check configuration has acceptance probability $q$.

**Proof.** Proceed by induction on $dd$, the truncated difference between the row register and the outer counter. When $dd=0$, the outer counter equals the row register. The equality test at the row-check state therefore takes its positive branch, and the resulting configuration is exactly the assumed next-row configuration with inner counter equal to its current value. The bound on the inner counter lets us apply that assumption; equality of the register states is bookkeeping (`UPS.of_eq`).

For the successor case, the outer counter is strictly below the row register. The equality test takes its negative branch, after which the program clears the inner counter and uses the addition subroutine to advance the input pointer by twice the vertex count. The addition rule (`ups_ad`) applies because the inner counter has been cleared and the pointer and register bounds follow from the hypotheses, including the stated size bound. The program then increments the outer counter. The row-update identity (`ix_v_upd`) shows that this increment does not change the row or column values relevant to the scan. The new truncated difference is one smaller, so the induction hypothesis applies with the updated state: the outer counter remains at most the row register, the row remains below the vertex count, and the pointer equation advances by exactly the required amount. The assumed next-row semantics supplies the induction hypothesis's continuation for each allowed inner-counter value. Reassembling these deterministic steps with the equality-branch rules (`PSem.jeq_neg`, `PSem.clr`, and `PSem.inc`) proves the claim.

**Key facts.** `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.UPS.of_eq`, `Complexity.LogProg.PSem.jeq_neg`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.ups_ad`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.ix_v_upd`, `Complexity.LogProg.UReg.reg`.
