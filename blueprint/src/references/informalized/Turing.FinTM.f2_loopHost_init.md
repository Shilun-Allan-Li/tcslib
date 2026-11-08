<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Loop Host Configuration

**Claim.** On input $x$, the loop host’s initial configuration is the capture of the fuel source’s initial configuration, embedded into the host state space with empty prefix and output and control return state $0$.

**Proof.** Rewrite both initial configurations using the characterization of a machine’s initial configuration as the word configuration with its initial state (`initCfg_ofWords`). Unfolding the definitions, both sides have the fuel machine’s initial state embedded in the host state space, the same input position, blank work tapes with heads at zero, and empty output. The capture therefore has exactly the asserted form.

**Key facts.** `Turing.initCfg_ofWords`.
