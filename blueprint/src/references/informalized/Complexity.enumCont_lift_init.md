<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_lift_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting an initial computation

**Claim.** If the larger machine simulates the smaller machine's transitions at embedded states by padding its work tapes, then a computation of the smaller machine from its blank initial configuration is reproduced by the larger machine from the corresponding blank configuration at the same time, with the same output.

**Proof.** The computation hypothesis is equivalent to saying that the smaller machine's run from its initial configuration is halted at time $T$ and has output $y$ (`Turing.FinTM.computesInTime_iff`). The padded-initial-configuration identity (`Complexity.enumCont_pad_init`) identifies the larger machine's stated start configuration with the padded smaller initial configuration. The simulation theorem (`Complexity.enumCont_pad_run`) carries this identity through all $T$ steps. At the resulting configuration, the smaller state is none, whose image under the state embedding remains none, and its output is still $y$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.enumCont_pad_init`, `Complexity.enumCont_pad_run`.
