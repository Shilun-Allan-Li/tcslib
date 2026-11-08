<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitEmit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final split-emitting computation

**Claim.** After $|s|+|w|+3$ steps, the split-emitting machine is halted with its input head at $|w|$, its auxiliary head at $|s|$, and output equal to the doubled prefix of length $|s|$, followed by $01$ and then the remaining suffix of $w$.

**Proof.** Rewrite the total time as $2|s|+2+(|w|-|s|+1)$, using $|s|\le |w|$ and the length formula for a list suffix. The paired-step result (`f2_splitEmit_double`) gives the configuration after the first $2|s|$ steps: it is in state $0$, both heads are at $|s|$, and its output repeats each bit of the length-$|s|$ prefix twice. The separator result (`f2_splitEmit_separator`) applies the next two steps, leaving the heads in place, entering state $3$, and appending $01$. The run composition law (`runFrom_add`) allows these successive run segments to be combined. For the final segment, decompose $w$ as its length-$|s|$ prefix followed by the suffix after that prefix, using the prefix-suffix decomposition of a list. The suffix result (`f2_splitEmit_suffix`) says that state $3$ reads and emits this suffix, advances the input head to $|w|$, leaves the auxiliary head at $|s|$, and halts after the suffix length plus one steps. Its output is the previous output followed by the suffix. Together these segments give exactly the claimed encoding and final configuration.

**Key facts.** `Turing.FinTM.f2_splitEmit_double`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_splitEmit_separator`, `Turing.FinTM.f2_splitEmit_suffix`.
