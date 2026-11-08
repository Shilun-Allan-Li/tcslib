<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.two_mul_sum_addressingErrorIndicator_ge_event_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing error and unselected coordinates

**Claim.** For an addressing function and a function depending only on coordinates in \(J\), the total error-indicator sum is at least half the number of inputs whose selected coordinate is outside \(J\).

**Proof.** The proof pairs each input \(x\) with its address-preserving flip. Summing the error indicator over all inputs is unchanged by this flip (\(\texttt{FABL.sum_addressingErrorIndicator_flip}\)); hence twice the total error sum equals the sum, over all inputs, of the two error indicators in each pair. Whenever the selected coordinate of \(x\) lies outside \(J\), at least one of those two inputs must disagree with \(g\): the flip changes the addressed data bit while leaving the coordinates in \(J\) unchanged, so a function depending only on \(J\) cannot match both outputs (\(\texttt{FABL.one_le_addressingErrorIndicator_add_flip}\)). Summing this lower bound over the event inputs gives at least the event's cardinality. Extending that sum to all inputs can only increase it, since each error indicator is nonnegative. Thus twice the total error sum is at least the number of such inputs.

**Key facts.** `FABL.sum_addressingErrorIndicator_flip`, `FABL.one_le_addressingErrorIndicator_add_flip`.
