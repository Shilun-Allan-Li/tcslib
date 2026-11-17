<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterToken_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Token Encoding

**Claim.** Starting just after a prefix $p$ in the token-scanning state, if the next input bit is $b$, then after two steps the encoder is just after $pb$, has appended $bb$ to its output, and is in the token-scanning state when $b$ is true and the separator-phase state when $b$ is false.

**Proof.** The decomposition $x=pbr$ ensures that the symbol read just after $p$ is $b$. The first transition reads that bit and appends one copy to the output; it enters the intermediate state for the corresponding bit value. On the second transition, the machine appends the second copy, advances the input head past $b$, and enters state $0$ if $b$ is true or state $3$ if $b$ is false. The two-step run is obtained by unfolding the definition of iteration into two successive machine steps. Since there are no work tapes, equality of state, input position, and output gives equality of configurations (zero-tape configuration extensionality, `Turing.Cfg.ext_zero_tapes`). The head advancement uses the fact that a positive move from a position short of the right boundary increases its position by one (`Turing.moveInputPos_pos_of_ne_right`).

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`.
