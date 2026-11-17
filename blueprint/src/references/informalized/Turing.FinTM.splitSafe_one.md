<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSafe_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Single Anchor-Free Step

**Claim.** If one step carries $c$ to $d$ and neither endpoint has state $a$, then the one-step run from $c$ reaches $d$ and avoids $a$ at times $0$ and $1$.

**Proof.** The one-step run is exactly the result of applying one machine step to $c$, so it equals $d$ by hypothesis. The only times from $0$ through $1$ are the endpoints: at time $0$ the run is at $c$, whose state is not $a$, and at time $1$ it is at $d$, whose state is not $a$.
