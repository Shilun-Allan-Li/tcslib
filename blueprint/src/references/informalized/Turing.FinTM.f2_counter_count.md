<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Configuration After Counting

**Claim.** For every finite Boolean list $x$ and every $i\le |x|$, there is a time $t$ with $t+2\,\mathrm{count}_{\mathrm{true}}(i.bits)\le 4i$ at which the machine is in state $0$, its input head is at $i+1$, its work-tape head is at $0$, its tape contains $i.bits$, and its output is empty.

**Proof.** Proceed by induction on $i$. For $i=0$, take $t=0$: the initial configuration has state $0$, input position $1$, empty work tape, head position $0$, and empty output, as required. For the successor step, suppose the asserted configuration is reached for $i$ at time $t$. Starting from that configuration, the machine increments the stored binary counter and advances the input head to $i+2$, returning the work-tape head to $0$ and leaving the output empty; this is the counter-increment behavior (`f2_counter_increment`). The increment takes $2\,\mathrm{carry}(i.bits)+2$ steps, so choose the total time $t+2\,\mathrm{carry}(i.bits)+2$. The identity that incrementing the binary expansion of $i$ gives that of $i+1$ (`f2_counterInc_bits`), together with the potential identity $\mathrm{count}_{\mathrm{true}}(f2\_counterInc(bs))+\mathrm{carry}(bs)=\mathrm{count}_{\mathrm{true}}(bs)+1$ (`f2_counterInc_potential`), gives the required time bound by arithmetic. The run-composition law (`runFrom_add`) identifies this two-part run with the run from the initial configuration.

**Key facts.** `Turing.FinTM.f2_counterInc_bits`, `Turing.FinTM.f2_counterInc_potential`, `Turing.FinTM.f2_counter_increment`, `Turing.MultiTapeTM.runFrom_add`.
