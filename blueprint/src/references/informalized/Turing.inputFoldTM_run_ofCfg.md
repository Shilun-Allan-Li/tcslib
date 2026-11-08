<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.inputFoldTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the Input-Fold Machine

**Claim.** Starting in state $(\mathrm{fwd},a_0)$ with input head at position $1$, the input-fold machine finishes after $2|x|+2$ steps in state $(\mathrm{done},\operatorname{foldl}(\delta,a_0,x))$, is never in a done state earlier, and leaves every work-tape head fixed throughout.

**Proof.** The run at each time is given by the scan-fold trace (`Turing.scan_fold_trace`). During the forward scan, the machine updates its accumulator by applying $\delta$ to each successive input symbol, so after reading all of $x$ the accumulated value is $\operatorname{foldl}(\delta,a_0,x)$. It then scans back and enters the corresponding done state at time $2|x|+2$. The trace remains in forward or backward states at every earlier time, so it has not yet entered any done state. Its transitions move only the input head; the work-tape heads therefore retain their initial positions at every time, including the endpoint.

**Key facts.** `Turing.scan_fold_trace`.
