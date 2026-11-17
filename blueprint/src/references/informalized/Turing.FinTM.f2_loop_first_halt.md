<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halting Time

**Claim.** If $c$ is not halted but the run from $c$ is halted at time $t$, there is a first halting time $u$ with $0<u\le t$; the run is nonhalting at every earlier time, is halted at $u$, and has the same configuration at $u$ as at $t$.

**Proof.** Consider the nonempty set of times at which the run is halted; it contains $t$. Let $u$ be its least element. Then the run is halted at $u$, and minimality says it is not halted at any $v<u$. Since $t$ is one of the halting times, minimality also gives $u\le t$. Moreover, $u$ cannot be zero: the run at time zero is the starting configuration, which is not halted by hypothesis (`Turing.MultiTapeTM.runFrom_zero`). Thus $u>0$. Finally, decompose the run at time $t$ into its first $u$ steps and the remaining $t-u$ steps using the run composition law (`Turing.MultiTapeTM.runFrom_add`). A halted configuration remains unchanged under every further number of steps (`Turing.MultiTapeTM.runFrom_of_halt`), so the configuration at time $t$ equals the one at time $u$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
