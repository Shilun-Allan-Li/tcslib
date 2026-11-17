<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceCore_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep Choice-Prefix Simulation

**Claim.** For every prefix length $t\le |u|$, the core run for $t$ steps encodes the nondeterministic run under the first $t$ bits of $u$, with a valid boundary tag and choice-head position $t$.

**Proof.** Proceed by induction on $t$. At $t=0$, choose the given tag: the two runs are at their starting configurations, so the encodings agree. For the successor case, apply the induction hypothesis at length $t$ (the bound needed for the next bit follows from $t+1\le |u|$). The one-step simulation fact (`choiceCore_step`) supplies a valid updated tag and identifies the core's next configuration with the encoding of the nondeterministic configuration after choice bit $u[t]$, with the choice head advanced to $t+1$. The list of the first $t+1$ bits is the first $t$ bits followed by $u[t]$; by the definition of `runWith` and its append law (`Turing.NDTM.runWith_append`), this is exactly the corresponding nondeterministic run. The iterate identity for one additional core step (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) then gives the required equality of runs.

**Key facts.** `Complexity.choiceCore_step`, `Turing.NDTM.runWith_append`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
