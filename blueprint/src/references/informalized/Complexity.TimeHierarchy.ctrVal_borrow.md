<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrVal_borrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Borrow Identity

**Claim.** A string of $j$ true digits followed by a false digit and then $r$, with one added to its value, has the same value as $j$ false digits followed by a true digit and then $r$.

**Proof.** Apply the repeated-prefix value formulas: $j$ true digits followed by a list have value plus one equal to $2^j$ times the value of that list plus one, while $j$ false digits multiply the following value by $2^j$. The false digit in the first list contributes twice the value of $r$; the true digit in the second contributes one plus twice the value of $r$. Thus both sides reduce to $2^j(2\,\mathrm{ctrVal}(r)+1)$, proving the identity.

**Key facts.** `Complexity.TimeHierarchy.ctrVal_replicate_true`, `Complexity.TimeHierarchy.ctrVal_replicate_false`.
