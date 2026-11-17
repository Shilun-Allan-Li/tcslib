<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostEmitTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation for Any Number of Steps

**Claim.** For every $t$, there is a tag satisfying the boundary condition for the input-head position reached after $t$ original steps such that the virtual simulation after $t$ steps is exactly the configuration built from that reached configuration, tag, fixed virtual position $p$, and fixed prefix $\mathrm{pre}$.

**Proof.** Induct on $t$. At zero steps, use the original tag: the initial virtual configuration is precisely the required construction. For the successor step, take the tag and configuration identity supplied by the induction hypothesis. Apply the one-step simulation theorem (`vhostEmitTM_step`) to that reached original configuration and tag; it supplies a new tag satisfying the boundary condition after one more original step, and identifies the corresponding virtual step with the construction from that successor configuration. The run identity expressing $t+1$ steps as one step after $t$ steps (`runFrom_succ_eq_step'`) aligns both simulations, yielding the required identity.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.vhostEmitTM_step`.
