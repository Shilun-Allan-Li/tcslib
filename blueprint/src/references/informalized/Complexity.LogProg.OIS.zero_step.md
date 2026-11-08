<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.zero_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Zero-Test Step

**Claim.** From the image of a configuration in phase $\mathrm{zt}$, one compiled step keeps the counter unchanged and enters phase $\mathrm{work}(\mathrm{none},\mathrm{true})$ when $i=0$, or phase $\mathrm{dD}$ otherwise.

**Proof.** The one-step run is a single compiled transition (`Complexity.LogProg.rrun_one`). In phase $\mathrm{zt}$, that transition reads the added tape at position zero. The buffer-tape definition identifies this symbol with the head bit of the binary representation of $i$. The head-bit formula (`Complexity.LogProg.bits_head_odd`) says the tape is blank at zero exactly when $i=0$, and otherwise supplies a Boolean bit. The zero-test transition selects the work phase in the blank case and the decrement phase in the nonblank case; it does not move the counter head or alter the counter tape. Hence the resulting configuration is the claimed image.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.bits_head_odd`.
