<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs from an Already Halted Configuration

**Claim.** From a configuration whose state is already none, every choice word leads to a halted configuration, and every earlier configuration satisfies $G$ whenever it is nonhalted.

**Proof.** The run step leaves a halted configuration unchanged. Thus, by iterating this fact, every run from $(\mathrm{none},v,r)$ still has state none. At any intermediate time the run likewise has state none, so the premise that this intermediate configuration is nonhalted is impossible; the conditional requirement involving $G$ is therefore satisfied.
