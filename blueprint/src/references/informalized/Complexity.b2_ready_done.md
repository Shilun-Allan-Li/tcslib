<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_ready_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Startup from Assembly Blank

**Claim.** From the assembly-rewind configuration with head at $-1$, one host step enters the verifier phase initialized on $y$, with true boundary tag, input head at $c$'s position, and scheduler tapes and heads inherited from $c$.

**Proof.** At assembly head position $-1$, the assembly tape is blank, so the host's loader-state transition takes the branch that starts verification. This transition leaves the input head fixed, as a zero movement does (`moveInputPos_zero`). It changes the control state to the verifier's initial state, sets the boundary tag to true, and initializes the verifier work tapes and heads. The scheduler tape block is untouched and therefore agrees with the inherited data from $c$; the assembly block becomes the stored input $y$ at the verifier's input position, with its output buffer empty. These are exactly the components of the verifier configuration built from the initial configuration of $V$ on $y$.

**Key facts.** `Turing.moveInputPos_zero`.
