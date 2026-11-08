<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.le_bribeInput_one_of_isMonotoneInCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity under coordinate bribery

**Claim.** If the function is nondecreasing in every coordinate, then changing any finite set of coordinates to $1$ cannot decrease its value.

**Proof.** Induct on the finite set $J$. For $J=\varnothing$, bribing changes no coordinate, so the values agree. For the inductive step, write $J$ as the insertion of a coordinate $i$ into a set not containing $i$. First change coordinate $i$ to $1$. This does not decrease the function: if the current value of coordinate $i$ is already $1$, the input is unchanged; if it is $-1$, coordinatewise monotonicity compares the input with the one having coordinate $i$ set to $1$. Then apply the induction hypothesis to the remaining coordinates, starting from this modified input. The bribery identity (FABL.bribeInput_insert) identifies this two-stage modification with bribing all of $J$, and transitivity gives the result.

**Key facts.** `FABL.bribeInput_insert`, `FABL.setCoordinate_eq_self`.
