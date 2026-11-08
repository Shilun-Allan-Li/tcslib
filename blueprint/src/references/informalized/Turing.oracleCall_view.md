<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleCall_view -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration after an oracle call

**Claim.** Under the stated blank-tape and zero-head hypotheses, embedding the virtual-host configuration initialized with $z$ gives the configuration obtained from $d$ by setting the state to $(q,\mathrm{true})$ and replacing the tape at the first virtual bank index by the buffer containing $z$.

**Proof.** First consider the virtual-host configuration whose first work tape is empty and whose other work tapes are empty. Its state, input-head position, and output agree with the target configuration. The blank-tape and zero-head hypotheses show that on each embedded tape its contents and head position also agree with those of $d$. Thus the bank-configuration agreement lemma identifies its embedding with $d$ having state $(q,\mathrm{true})$ (`oracleBankCfg_eq`). Next, initializing the first virtual work tape with $z$ changes the empty virtual-host configuration only at its first bank index: its tape becomes the buffer containing $z$, while all other data stays fixed. This follows by separating that index from the remaining indices; on the first virtual tape the word is $z$, and on the other virtual tapes the initialized words are empty. Finally, embedding an update to a virtual tape transports that update to the corresponding embedded tape (`oracleEmbed_updateTape`). Applying this to the first bank index and using the empty-configuration identification gives exactly the stated update of $d$.

**Key facts.** `Turing.oracleBankCfg_eq`, `Turing.oracleEmbed_updateTape`.
