<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison during the read

**Claim.** Starting in the initial comparison phase with tape $s$ holding the binary representation of $k$ and tape $r$ holding that of $i$, the read program reaches phase $yes$ exactly when $k=i$, and phase $no$ otherwise, while preserving the specified read-frame bounds throughout the run.

**Proof.** Use the comparison-run property (`eq_run`) with the two tapes as its compared registers. It supplies a finite run from the comparison setup to the corresponding $yes$ or $no$ state, and bounds the moving head by the length of the binary representation of the value on tape $r$. The setup used in that property is expressed by `eqCfg`; because $r\ne s$ and the original head on $r$ is at $0$, this configuration agrees with the stated `readAt` setup (`view` in the proof). Rewriting the endpoint therefore gives the desired comparison result. At every earlier time, `eq_run` gives a configuration with the two comparison heads within its stated range. The tape-$s$ portion has the fixed binary representation of $k$, and $k\le |x|$, so monotonicity of binary-word length bounds that head by the read-frame limit (`length_bits_mono`). The other head already has the required bound from `eq_run`; the unchanged tapes and output then give the read-frame condition.

**Key facts.** `Complexity.LogProg.eq_run`, `Complexity.LogProg.length_bits_mono`.
