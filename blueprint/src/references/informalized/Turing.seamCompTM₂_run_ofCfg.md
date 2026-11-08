<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM₂_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Stage Seam Composition Run

**Claim.** If the first machine avoids both exit states before reaching its final configuration, then the twice-composed machine follows the appropriate second-stage run after the handoff, according to which exit state that configuration has.

**Proof.** Prove the two implications separately. Suppose first that the final configuration has state $e_1$. The first seam composition, between $M_0$ and $M_1$, then follows the run of $M_1$ after its handoff (`seamCompTM_run_ofCfg`). To apply the left-run agreement theorem to the outer composition, show that this first seam composition never reaches the outer exit state, the left-embedded $e_2$, before time $T_0+1+t$. Up through time $T_0$, its run agrees with $M_0$ (`seamCompTM_runFrom_left`); before $T_0$, the avoidance hypothesis excludes $e_2$, and at $T_0$ the state is $e_1$, distinct from $e_2$. After the first handoff, the run follows $M_1$ in the middle component, whose states cannot equal the left-embedded $e_2$. The outer left-run agreement theorem now identifies the twice-composed run with that first seam composition at the required time; the inner run identity gives the claimed middle-component configuration.

Now suppose the final configuration has state $e_2$. The first seam composition agrees with the embedded $M_0$ run through time $T_0$, again by `seamCompTM_runFrom_left`, so it reaches the embedded final configuration at that time. It avoids the outer exit state before then by the original avoidance of $e_2`. Applying the two-machine run theorem (`seamCompTM_run_ofCfg`) to this first seam composition and $M_2$ gives the right-component run after the handoff. The nested state maps simplify to the stated embedding, yielding the second implication.

**Key facts.** `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM_run_ofCfg`.
