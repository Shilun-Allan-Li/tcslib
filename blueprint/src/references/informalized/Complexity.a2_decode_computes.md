<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_decode_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Decoding by a Binary Countdown

**Claim.** For every finite Boolean word $x$, the countdown emitter computes the word of $a2Value(x)$ ones within $2|x|+2+(a2Value(x)+1)(2|x|+3)$ steps.

**Proof.** Apply the countdown result (a2_countdown) to counter word $x$, with $n=a2Value(x)$ and empty initial output. It supplies a halting run with the required output in some time $t\le(a2Value(x)+1)(2|x|+3)$. The startup configuration lemma (a2_start) says that after $2|x|+2$ steps the machine is in exactly the borrow-phase configuration required by that countdown result. Concatenating the startup and countdown runs using runFrom_add proves that the machine halts with the desired output after $2|x|+2+t$ steps. The characterization of computation in time by the halting state and output (computesInTime_iff) packages these facts as computation, and monotonicity of computation time (ComputesInTime.mono) extends the bound to the claimed time.

**Key facts.** `Complexity.a2_countdown`, `Complexity.a2_start`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
