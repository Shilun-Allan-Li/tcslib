<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitEmbed_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe embedded run to a stopped configuration

**Claim.** If a stopped configuration $d$ is reached from $c$ within $T$ steps, then some time $t\le T$ reaches its state-renaming in the host machine, with the host state avoiding the anchor at every time up to $t$.

**Proof.** Consider the nonempty set of times when the source run is in a stopped state, and let $t$ be its least element. Then $t\le T$, and before $t$ the source is never stopped. A stopped configuration is fixed by one step, so once the run reaches the stopped configuration at time $t$, it remains there. Decomposing the run at times $t$ and $T$ with the run composition law (`runFrom_add`) therefore shows that the source configuration at time $t$ is exactly $d$. Next, prove by induction on $j\le t$ that the host run at time $j$ equals the state-renaming of the source run at time $j$. At a halted source configuration, both machines remain fixed. At a live source configuration before time $t$, its state is not stopped by minimality of $t$, so the transition-agreement hypothesis makes one host step equal to the renamed source step. The successor-time run equation (`runFrom_succ_eq_step'`) supplies the induction step. At time $t$, this equality and the identification with $d$ give the required endpoint. Finally, for every $j\le t$, the source state is either absent or is some state $q$; in the latter case its embedded state differs from the anchor by hypothesis. The induction equality thus shows the host state avoids the anchor at every such time.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
