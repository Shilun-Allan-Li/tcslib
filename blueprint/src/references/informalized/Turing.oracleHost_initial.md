<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleHost_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle host initial configuration

**Claim.** From the host initial configuration loaded with the specified machine words, the host reaches after two steps the stable encoding of the oracle machine's initial configuration, with side tag true.

**Proof.** View the initial host tapes as an embedding of a local dispatch configuration in the boot state. The selected dispatch slots are initially blank: the first two selected source slots correspond to the ordinary and query tapes, and the query word is empty by hypothesis; the remaining selected slots lie beyond the prefix of loaded words. The other slots retain the supplied host contents. By the tape-embedding configuration equality (`Turing.oracleBankCfg_eq`), this embedded local boot configuration is exactly the given initial host configuration. The boot transition writes the origin marker on dispatch tape 1 and enters ready; the resulting embedded view is described using the embedding update identity (`Turing.oracleEmbed_updateTape`). Apply the dispatch simulation theorem (`Turing.oracleHost_dispatch`) to this one-step run: ready redirects to the source phase at the oracle machine's initial state with tag true. The resulting host configuration is the stable encoding, by the source-initialization identity (`Turing.oracleSourceCfg_initial`).

**Key facts.** `Turing.oracleBankCfg_eq`, `Turing.oracleEmbed_updateTape`, `Turing.oracleHost_dispatch`, `Turing.oracleSlots_injective`, `Turing.oracleSourceCfg_initial`.
