<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean :: Complexity.LogProg.runWith_append_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Makes a Choice Suffix Irrelevant

**Claim.** If running from $C$ under the choice word $u$ reaches a halted configuration, then running under the concatenated choice word $uv$ yields the same configuration as running under $u$.

**Proof.** The run on a concatenation first processes $u$ and then processes $v$ from the resulting configuration (`runWith_append`). By hypothesis that intermediate configuration is halted. A halted configuration is unchanged by any further choice word (`runWith_of_halt`), so the continuation on $v$ leaves it exactly as it was after $u$.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
