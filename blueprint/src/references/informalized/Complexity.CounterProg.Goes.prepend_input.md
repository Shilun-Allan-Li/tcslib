<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgInput.lean :: Complexity.CounterProg.Goes.prepend_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending to the Input

**Claim.** If the program has the stated run on input $v$ from position $p$ to position $p'$, then on input $u$ followed by $v$ it has the same run from position $|u|+p$ to position $|u|+p'$, with the same step bound and output extension.

**Proof.** Fix an initial output word $o$, and choose a run of length $t\le b$ supplied by the hypothesis on input $v$. Shifting a configuration's input position forward by $|u|$ makes each step on input $u$ followed by $v$ correspond to the same step on input $v$; consequently, the run shift identity (`run_shiftInput`) says that the shifted initial configuration evolves to the shifted final configuration after the same $t$ steps. The shifted initial and final configurations have positions $|u|+p$ and $|u|+p'$, respectively, while their labels, registers, and output are unchanged. This gives the required run for each $o$.

**Key facts.** `Complexity.CounterProg.run_shiftInput`.
