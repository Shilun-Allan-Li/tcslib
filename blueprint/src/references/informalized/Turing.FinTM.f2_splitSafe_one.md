<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSafe_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Safe Segment

**Claim.** If one step from $c$ produces $d$, and neither configuration has state $a$, then the run from $c$ is at $d$ after one step and avoids state $a$ at steps $0$ and $1$.

**Proof.** By definition, the run from $c$ at time $1$ is the result of one application of the step function, so the given equality identifies it with $d$. To check safety through time $1$, the only possible times are $0$ and $1$. At time $0$ the run is at $c$, whose state is not $a$; at time $1$ it is at $d$, whose state is not $a$.
