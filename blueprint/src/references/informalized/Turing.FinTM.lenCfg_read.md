<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol of a Checker Configuration

**Claim.** For any optional checker state, position $i\le |x|$, and counter $r$, the input symbol scanned by the corresponding length-checker configuration is $x[i]?$.

**Proof.** The configuration `lenCfg` places its input head at position $i+1$ in the shifted indexing used for configurations. The general fact that a configuration whose head has value $i+1$ reads the $i$th list entry, with `none` at the end of the input (`inputSymbol_at`), therefore gives the claimed equality.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
