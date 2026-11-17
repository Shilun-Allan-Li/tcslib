<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_strict_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining Strict Safety Intervals

**Claim.** Suppose the run from $c$ reaches $d$ after $a$ steps, avoids state $r$ from time $0$ through time $a$, and the run from $d$ avoids $r$ for all times less than $b$. Then the run from $c$ avoids $r$ at every time less than $a+b$.

**Proof.** Fix $j<a+b$ and split into two cases. If $j\le a$, safety of the first run applies directly, since it covers every time through $a$ inclusively. If $j>a$, write $j=a+(j-a)$. The run-composition law (`runFrom_add`) and the equality of the configuration at time $a$ with $d$ identify the configuration at time $j$ from $c$ with the configuration at time $j-a$ from $d$. Since $j<a+b$, we have $j-a<b$, so the second safety assumption excludes state $r$ there as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
