<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitCount_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step compatibility of the split counter

**Claim.** Applying the lifted action to the counter configuration associated with $c$ gives exactly the counter configuration associated with the result of applying the original action to $c$.

**Proof.** Separate the cases according to whether the original action emits an output symbol. If it emits none, the output length does not change, so the counter position and overflow flag stay fixed; the lifted action leaves the added tape unchanged and applies the original work-tape actions. The input head also stays at the same position. If the action emits a symbol, the output length increases by one, so the counter advances one input position and updates its overflow flag to record whether the new count has passed $|w|$. The flag update follows from the overflow characterization (`f2_splitCount_over`), and the input-position update follows from the successor-position rule (`f2_splitPos_succ`). In either case, the state, tapes, head positions, input position, and output field match those of the counter configuration built from the updated original configuration.

**Key facts.** `Turing.FinTM.f2_splitCount_over`, `Turing.FinTM.f2_splitPos_succ`.
