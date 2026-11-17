<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.BPP_PTM_ssubset_DTIME_pow_log_of_eq_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Is Properly Contained in Quasipolynomial Time

**Claim.** Assuming $\mathrm{BPP}=\mathrm{P}$, the bounded-error randomized polynomial-time class is a proper subset of deterministic time $n^{\log_2 n}$.

**Proof.** Substitute the assumed equality $\mathrm{BPP}=\mathrm{P}$ into the established strict containment of $\mathrm{P}$ in deterministic time $n^{\log_2 n}$ (`P_ssubset_DTIME_pow_log`). This transports both the inclusion and its strictness to BPP.

**Key facts.** `Randomized.P_ssubset_DTIME_pow_log`.
