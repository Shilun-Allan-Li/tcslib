<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean :: Turing.ndAcceptsWithin_decider_of_universal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic exponential-time decision

**Claim.** Under the stated assumption that a nondeterministic universal machine halts within a code-dependent linear bound and correctly recognizes acceptance within the given time bound, there is a finite deterministic machine that outputs $[1]$ when the decoded machine accepts within $t$ steps and $[0]$ otherwise, within a code-dependent exponential bound.

**Proof.** Choose a nondeterministic universal machine $U_N$ and its linear-bound constant $C$ from the hypothesis. Apply the exhaustive-decision result (Turing.FinNDTM.exists_exhaustiveDecider) to obtain a finite deterministic machine $E$ and constant $C_E$. Whenever $U_N$ halts on the encoded input within $T=C(t+1)$ steps, this machine outputs $[1]$ if $U_N$ accepts within $T$ steps and outputs $[0]$ if it does not. The hypothesis identifies this acceptance condition with acceptance by the decoded machine within $t$ steps, so the two outputs have the required meanings.

The exhaustive-decision time bound is $C_E2^{C_E(T+1)}$. Set $D=C_E(C+1)$. Since $C(t+1)+1\le (C+1)(t+1)$, we have $C_E(C(t+1)+1)\le D(t+1)$. Also $C_E\le D$, so monotonicity of powers of $2$ and multiplication gives $C_E2^{C_E(C(t+1)+1)}\le D2^{D(t+1)}$. The deterministic machine therefore meets the claimed bound, using the monotonicity of computation time (Turing.FinTM.ComputesInTime.mono) to enlarge the time allowance.

**Key facts.** `Turing.FinNDTM.exists_exhaustiveDecider`, `Turing.FinTM.ComputesInTime.mono`.
