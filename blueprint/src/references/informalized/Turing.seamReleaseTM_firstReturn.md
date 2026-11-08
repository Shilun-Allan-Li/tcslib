<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamReleaseTM_firstReturn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Return in Seam Release

**Claim.** For a positive-time computation from state $a$ back to state $a$ with no intermediate return, the seam-release run reaches the right-state embedding of the final configuration at time $T$, and before then never has state $\mathrm{inr}(a)$.

**Proof.** For the endpoint, use the positive-time seam-release run identity (`seamReleaseTM_runFrom_pos`) at time $T$, then substitute the given equality for the original machine's run. Now fix $t<T$ to prove avoidance. If $t>0$, the same run identity identifies the seam-release configuration with the right embedding of the original run at $t$. A state equal to $\mathrm{inr}(a)$ would, by injectivity of the right-summand embedding, imply that the original run has state $a$, contradicting the no-intermediate-return hypothesis. If $t$ is not positive, then $t=0$; the initial state is the left embedding of $a$, so it cannot be the right embedding of $a$.

**Key facts.** `Turing.seamReleaseTM_runFrom_pos`.
