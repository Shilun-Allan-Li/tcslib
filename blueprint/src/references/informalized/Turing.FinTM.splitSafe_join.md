<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSafe_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining Anchor-Free Runs

**Claim.** If the run from $c$ reaches $d$ after $u$ steps and avoids state $a$ through that time, and the run from $d$ reaches $f$ after $v$ steps and avoids $a$ through that time, then the run from $c$ reaches $f$ after $u+v$ steps and avoids $a$ throughout.

**Proof.** By the run-composition identity (`runFrom_add`), the run from $c$ for $u+v$ steps is the run from its time-$u$ configuration for another $v$ steps. Since that intermediate configuration is $d$, the second reachability hypothesis shows that the result is $f$. For avoidance, apply the concatenation principle `splitSafe_add`: the first segment avoids $a$ through time $u$, and the second avoids $a$ through time $v$ when started at the time-$u$ configuration. Rewriting that configuration as $d$ using the first reachability hypothesis lets the given second avoidance hypothesis apply.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.splitSafe_add`.
