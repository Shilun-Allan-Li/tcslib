<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCall_reframe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reframing a Loop Call

**Claim.** Reframing the indicated loop-call configuration using the second call's state, the specified input position, tapes, head positions, and empty output gives exactly that second loop-call configuration.

**Proof.** The two configurations have the same state by the choice of the reframed state, the same input-head position $c.\mathrm{inputPos}$, and empty output. For the work tapes, split indices according to their roles. The flag tape at index $\mathrm{body.k}$ is the tape containing $\mathrm{flag}'$ only at cell zero. The counter tape at index $\mathrm{body.k}+1$ and the payload tape at index $\mathrm{body.k}+1+(1+F.\mathrm{k})$ are set by the frame to the buffers for $\mathrm{word}'$ and $c.\mathrm{output}$, with the prescribed head positions. At indices belonging to the original body tapes, both constructions use the tapes of $c$ with the requested state replacement; at indices belonging to the fuel tapes, both retain the fuel configuration. These index cases also give identical head positions, so all configuration components agree.
