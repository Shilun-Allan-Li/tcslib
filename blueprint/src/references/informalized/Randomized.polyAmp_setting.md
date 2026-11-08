<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.polyAmp_setting -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial amplification setting

**Claim.** Under the stated space and code-size bounds, the machine halts by $K=2^{F\ell(|x|)}$ steps, its output distribution at $K$ agrees with that at $T_0$, and the amplification program halts with the stated register bound and probabilities.

**Proof.** Put $n=|x|$. First, the logarithmic space allowance is at most $c\ell(n)$, since $\mathrm{logSpace}(n)\le\ell(n)$ (`Randomized.PolyAmp.logSpace_le_ell`). The code-size hypothesis then bounds the exponent needed by the machine's configuration-count halting bound: using $\ell(n)\ge1$ and elementary arithmetic, $\mathrm{codeK}(N)(c\ell(n)+\mathrm{logSpace}(n)+1)\le F\ell(n)$. Thus the configuration bound is at most $2^{F\ell(n)}=K$. The space-based halting theorem (`Randomized.PolyAmp.haltsWithin_codeBound`) supplies halting at the configuration bound, and halting monotonicity (`Turing.NDTM.HaltsWithin.mono`) extends it to $K$.

Because every computation halts by the configuration bound and by the assumed time $T_0$, the output distribution at either later time is the same as at that bound. The halting-based output-probability invariance fact (`Turing.FinNDTM.outputProb_eq_of_haltsWithin`) therefore identifies the distributions at $K$ and $T_0$. The probability that a random string is accepting is the probability of outputting the one-bit word $[1]$ (`Randomized.PolyAmp.accP_init`); identifying these events on each random string and using probability-event congruence (`Randomized.randProb_congr`) gives the stated equality.

Finally, apply the amplification program's start specification (`Randomized.PolyAmp.ps_start`) with space allowance $c\ell(n)$, time bound $K$, and its stated input-length bound. Its probability semantics (`Complexity.LogProg.PSem.decides`) yields a random-bit length at which the program halts and has the two asserted output probabilities. The uniform register estimate follows from `Randomized.PolyAmp.regBound_le`. The program's states satisfy the required precondition property by `Randomized.PolyAmp.ampA_npreS`; combining that with the register estimate gives the requested halting invariant (`Complexity.LogProg.NHalts.mono`).

**Key facts.** `Randomized.PolyAmp.logSpace_le_ell`, `Randomized.PolyAmp.haltsWithin_codeBound`, `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`, `Randomized.PolyAmp.accP_init`, `Randomized.randProb_congr`, `Randomized.PolyAmp.ps_start`, `Complexity.LogProg.PSem.decides`, `Randomized.PolyAmp.regBound_le`, `Randomized.PolyAmp.ampA_npreS`, `Complexity.LogProg.NHalts.mono`.
