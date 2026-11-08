<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitCount_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a live counter run

**Claim.** As long as the source machine has not halted before time $t$, the host machine's configuration after $t$ steps is exactly the counter configuration associated with the source machine's configuration after $t$ steps.

**Proof.** First establish the one-step correspondence for any source configuration $d$ that is not halted. Its state is some $q$. The corresponding counter configuration has host state $emb(q,over)$, where $over$ records whether the accumulated output length has passed the relevant bound. Its input symbol is blank, because the source machine is running on empty input. The last $k$ work heads read the same symbols as the source heads, while the added tape holds the buffer data; this is the work-symbol correspondence used in the construction. The assumed transition agreement then makes the host transition precisely the lifted source action, and the counter-configuration update lemma (`f2_splitCount_apply`) identifies the resulting host configuration with the counter configuration of the source's next configuration. Induct on the number of steps. At time zero the configurations agree by definition. For the successor step, the hypothesis that the source run is live at every earlier time ensures its configuration at the preceding time is not halted, so the one-step correspondence applies; combining it with the induction hypothesis proves the desired equality. The successor-time run equation (`runFrom_succ_eq_step'`) relates each run to its next single step and completes the induction.

**Key facts.** `Turing.FinTM.f2_splitCount_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
