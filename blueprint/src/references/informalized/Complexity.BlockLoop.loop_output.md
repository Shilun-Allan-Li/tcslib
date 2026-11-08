<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.loop_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of a finite block loop

**Claim.** Under the stated initialization, nonemptiness, and update assumptions, if $K<N$, the concatenated emissions from the first $N$ iterates equal the output evaluated at the terminal state with head $P(K)$, empty countdown, and next state $Q(K)$.

**Proof.** The orbit formula says that for each $i\le K$, the state after $i$ steps has head $P(i)$, countdown $1^{K-i}$, and next state $Q(i)$ (`orbit`). At $i=K$, this countdown is empty, so the state is exactly the terminal state at which the output is evaluated. Once the countdown is empty, the step function sends the state to the completed state and keeps every later iterate there (`iterate_done`), using the fact that $P(K)$ is nonempty to ensure the terminal branch is selected. The emission-summing result (`flatMap_emit_orbit`) now applies: before the terminal state, emissions are empty; at the terminal state, the output is emitted; afterward, the completed state emits nothing. Since $K<N$, the first $N$ iterates include that terminal state, and their concatenated emissions are precisely the claimed output.

**Key facts.** `Complexity.BlockLoop.orbit`, `Complexity.BlockLoop.iterate_done`, `Complexity.BlockLoop.flatMap_emit_orbit`.
