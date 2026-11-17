<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_unselected -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Unselected Tapes

**Claim.** At any index $j$ outside the image of $\sigma$, the embedded configuration retains the supplied tape contents and head position at $j$.

**Proof.** The proof packages the given configuration as the initial configuration of a machine with a trivial transition rule, then applies the unselected-tape frame theorem `Turing.embedEmitTM_frame` at time zero. The zero-step run is the initial configuration itself, by `Turing.MultiTapeTM.runFrom_zero`; hence the frame theorem's tape and head equalities reduce to the two claimed equalities for the embedded configuration.

**Key facts.** `Turing.embedEmitTM_frame`, `Turing.MultiTapeTM.runFrom_zero`.
