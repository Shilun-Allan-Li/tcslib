<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_restore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration phase of the round

**Claim.** Starting in the restoration phase at scan position $0$, the split-search round body reaches its restoration return state within $2|s|+|w|+5$ steps, with candidate $s$ extended by $1$ when $|s|\le |w|$ and otherwise unchanged; the run avoids the anchor state through that time.

**Proof.** The standalone restoration machine reaches state $(4,\mathrm{false})$ from the cleanup-scan configuration in at most $2|s|+|w|+5$ steps, with its work tapes encoding $\mathrm{splitStep}(w,s)$ and its heads at $0$ (the restoration-run bound, `splitRestore_run`). Embed this machine's states as restoration states of the round body. The embedding never gives the anchor state. Away from the designated stopping state, the round body's transitions agree with the restoration machine's transitions; at the stopping state, the restoration machine is fixed, and the host transition is the zero-movement control action, which leaves the configuration unchanged. Thus the embedded run follows the restoration run until it reaches the stopping state, and the embedding argument (`splitEmbed_cut`) supplies a time no larger than the standalone bound at which the desired embedded configuration is reached, while certifying that every configuration up to then avoids the anchor. The zero-movement action preserves the input-head position (`moveInputPos_zero`), as required for the fixed-state check.

**Key facts.** `Turing.FinTM.splitRestore_run`, `Turing.FinTM.splitEmbed_cut`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
