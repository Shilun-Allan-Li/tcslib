<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.Cfg.ofWords_transfer_endpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transferring a Word Between Tapes

**Claim.** Replacing the source tape contents by the empty word and the destination contents by the original source word gives exactly the configuration obtained by the stated transfer, with state changed to $q'$.

**Proof.** Configurations are equal once their components agree. Expanding the word configuration shows that its work-tape heads all start at position $0$, and that tape $i$ stores the buffer tape of $w_i$. Thus the claimed state, input-head position, work-tape-head positions, and output agree immediately. It remains to compare work-tape contents, so fix a tape index and a cell position, and split into the source, destination, and all other tapes. On the source tape, the transfer erases the cells in the interval from $0$ through the source word's length; outside that interval the original buffer tape is retained. This is precisely the buffer tape of the empty word, since the source interval covers every position at which the finite word could have a symbol. On the destination tape, the hypothesis that its word is empty means its original contents are blank. The transfer writes the source buffer tape at positions starting from $0$; the resulting contents are therefore the buffer tape of the source word. On every other tape neither the transfer nor the nested updates to the word family change the contents. The source and destination cases are disjoint by their assumed distinctness. These pointwise equalities establish equality of the work-tape functions and hence of the configurations.

**Key facts.** `Turing.FinTM.bufferTape_nil`.
