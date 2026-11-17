<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitBody_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial split-body configuration

**Claim.** The initial configuration of the split-body machine on $w$ has anchor state, input-head position $1$, blank work tapes with all heads at position $0$, and empty output.

**Proof.** The initial configuration of any multi-tape machine is the configuration with its initial state, input head at position $1$, blank work tapes, heads at position $0$, and empty output. The initial state of the split-body machine is the anchor. The word configuration with empty words on every tape has exactly these blank tapes and head positions, so the two configurations agree (`initCfg_ofWords`).

**Key facts.** `Turing.initCfg_ofWords`.
