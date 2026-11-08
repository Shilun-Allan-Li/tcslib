<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.contH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting from Equal States

**Claim.** If two register states are equal and the machine halts from one of them with answer $r$, while satisfying the guard at every earlier configuration, then it halts from the other with the same answer and guard conditions.

**Proof.** The hypothesis identifying the two states lets us substitute one for the other in the entire halting assertion. The starting configurations are therefore identical, and the same finite execution witnesses the same halting label, answer, and guard conditions.
