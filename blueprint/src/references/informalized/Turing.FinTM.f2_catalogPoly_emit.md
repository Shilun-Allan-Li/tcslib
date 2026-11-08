<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary output block

**Claim.** Starting in state $\mathrm{emit}(j)$ with the specified head positions and output $o$, after $j+1$ steps the machine is in state $\mathrm{advance}(0)$, with the same head positions and output $o$ followed by $j$ copies of true.

**Proof.** Induct on $j$. For $j=0$, one transition from $\mathrm{emit}(0)$ produces no symbol and changes state to $\mathrm{advance}(0)$; all positions and tape contents stay fixed, so the claim follows from the one-step run and zero-step run identities (`runFrom_succ_eq_step`, `runFrom_zero`). For the successor case, the transition from $\mathrm{emit}(j+1)$ outputs one true and enters $\mathrm{emit}(j)$. Apply the induction hypothesis to the remaining $j+1$ steps. The emitted symbol precedes the block of $j$ true symbols, yielding the required list of $j+1$ copies; the run decomposition is justified by `runFrom_succ_eq_step`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
