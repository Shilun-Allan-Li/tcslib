<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSafe_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining Safe Computation Segments

**Claim.** Let $M$ be a deterministic multi-tape Turing machine with Boolean work-tape symbols, let $a$ be a state, and let $c,d,f$ be configurations on the same input. If $M$ reaches $d$ from $c$ after $u$ steps while avoiding $a$ at every step from $0$ through $u$, and reaches $f$ from $d$ after $v$ steps while avoiding $a$ at every step from $0$ through $v$, then $M$ reaches $f$ from $c$ after $u+v$ steps and avoids $a$ at every step from $0$ through $u+v$.

**Proof.** The run-composition law says that running for $u+v$ steps from $c$ is the same as first running for $u$ steps and then running for $v$ more steps ( `Turing.MultiTapeTM.runFrom_add`). Since the first segment ends at $d$ and the second ends at $f$, this gives the claimed endpoint. For safety, apply the concatenation principle for safe runs (`Turing.FinTM.f2_splitSafe_add`): the run from $c$ avoids $a$ for its first $u$ steps, and its continuation from the configuration reached at time $u$ avoids $a$ for the next $v$ steps. The configuration at time $u$ is $d$ by hypothesis, so the second segment's safety assumption supplies precisely this continuation condition. Together these show that no step from $0$ through $u+v$ has state $a$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_splitSafe_add`.
