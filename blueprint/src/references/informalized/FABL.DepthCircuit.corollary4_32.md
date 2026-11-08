<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.corollary4_32 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Agreement Forces Large Circuit Size

**Claim.** If a depth-$d$ circuit agrees with full parity on a uniform random input with probability at least $1/2+\varepsilon_0$, then for every $s>1$ whose stated LMN degree cutoff is below $n$, the circuit’s size exceeds $s.

**Proof.** Apply the half-switching corollary to the circuit. Its required switching hypothesis is supplied by the bound for circuits (`hastadHalfSwitchingBoundForCircuits`), and the corollary gives exactly the claimed size conclusion under the agreement and cutoff hypotheses.

**Key facts.** `FABL.DepthCircuit.corollary4_32_of_halfSwitching`, `FABL.hastadHalfSwitchingBoundForCircuits`.
