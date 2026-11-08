<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.guideFill_left_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finishing the guide from the left

**Claim.** For positive radius $R$, filling $R$ cells leftward from the right guide, then setting coordinates $-R$ and $-R-1$ to the inside and left edge marks respectively, produces the guide tape of radius $R$.

**Proof.** Compare the two tapes at an arbitrary integer coordinate. The two updates first prescribe the leftmost interior cell and then the left edge marker. At every other coordinate, the leftward fill supplies the inside mark exactly on the newly filled interval; outside that interval the right guide retains its prescribed values. Expanding the definitions of the right guide, copied guide, guide marks, and guide tape, these cases agree pointwise. The assumption $R>0$ ensures the relevant intervals and their boundary coordinates have the required order.
