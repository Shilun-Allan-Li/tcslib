<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapValidate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent Validation of Encoded Pairs

**Claim.** For each decomposition $x=u r$, the silent validator reaches a next-phase configuration within $|r|+1$ steps if the parser succeeds, and otherwise reaches a halted configuration with empty output within that bound.

**Proof.** Induct on the suffix $r$ by separating its length into the empty case, a singleton, and a word with at least two bits. For the empty suffix, one step reads the end marker and halts; the pair decoder fails and the output stays empty. For a singleton, the first bit is processed by `mapParse_first`; the next step sees the end marker and halts. A one-bit suffix cannot decode as a pair, so this gives the failure conclusion in two steps. For a suffix beginning with two equal bits, the two-step behavior `mapParse_block` consumes that doubled bit and returns to the same silent parsing state. The induction hypothesis applies to the remaining suffix, with the prefix and input-head position shifted past the two bits; concatenating the runs via `runFrom_add` gives a total bounded by $|r|+1$. The decoder succeeds on this branch exactly when it succeeds on the remaining suffix. If the first two bits differ, there are two possibilities: $[\mathrm{false},\mathrm{true}]$ is the delimiter, in which case the parser enters the next phase after two steps and the decoder returns some pair; or $[\mathrm{true},\mathrm{false}]$, which is rejected, so the parser halts after two steps with empty output. The cases where the equal bits are false or true, and the two differing-bit cases, exhaust all possibilities, proving both the behavior and the stated time bound.

**Key facts.** `Turing.FinTM.mapCfg_read`, `Turing.FinTM.mapParse_block`, `Turing.FinTM.mapParse_first`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
