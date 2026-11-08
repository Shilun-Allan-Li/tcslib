<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.Cfg.embedOracle_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Embedding

**Claim.** Embedding the initial configuration yields the initial configuration in the enlarged model with its state included through the left inclusion.

**Proof.** Compare the five fields of the configurations. The state is the initial state included on the left, and the input-head position is unchanged. Every original work tape is blank and every original head is at zero; the added tape is also blank with head at zero. The output is empty on both sides. Thus all fields agree.
