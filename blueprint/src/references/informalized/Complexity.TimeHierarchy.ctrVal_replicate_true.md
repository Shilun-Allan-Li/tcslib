<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrVal_replicate_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After True Digits

**Claim.** Placing $j$ true digits before a Boolean list $r$ gives a value which, after adding one, equals $2^j$ times the value of $r$ plus one.

**Proof.** Induct on $j$. With no added digits, the identity is immediate. In the inductive step, prepend a true digit. The defining recurrence says this adds one and doubles the value of the remaining list. Adding one to the resulting value therefore gives twice the remaining value plus two, or twice the remaining value plus one. By the induction hypothesis, that latter quantity is twice $2^j(\mathrm{ctrVal}(r)+1)$, which is $2^{j+1}(\mathrm{ctrVal}(r)+1)$, as required.
