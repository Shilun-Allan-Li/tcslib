<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satHost_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forwarded Padded Seam Configuration

**Claim.** Forwarding a module configuration after padding its tapes and prefixing its output gives the corresponding host configuration, with the optional state mapped into the host state space or replaced by the module's return state when absent.

**Proof.** First use the padded seam identity: for a module with positive tape count, padding a configuration with its word on tape zero and all other tapes blank produces the same tape contents and head positions as the corresponding configuration with $K$ tapes (`Complexity.satPad_seam`). Emit this padded configuration into the host state space. The input position is unchanged, the tape contents and head positions agree by that identity, and the output becomes $\mathrm{pre}\,\mathrm{out}$. For the state, an existing module state is mapped into the host's module-tagged state; when the state is absent, the emitting configuration uses the return state. These coordinate equalities establish the claimed configuration equality.

**Key facts.** `Complexity.satPad_seam`.
