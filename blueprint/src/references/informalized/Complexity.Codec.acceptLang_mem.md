<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.acceptLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Language in Logarithmic Space

**Claim.** For every finite nondeterministic Turing machine $N$ over the Boolean alphabet, the language of paired encodings of inputs, certificates, and space-bounded accepting configurations for $N$ is decidable in logarithmic space.

**Proof.** The proof uses the acceptance-checking alternating machine and the polynomial-space-bound criterion for logarithmic-space membership (`arm_decides_poly`). Its oracle languages are the two component encodings, which are already in logarithmic space by `codecAs_mem`; the proposed bound is linear in the input length, with coefficient $8W(N)+8$. It suffices to show that the alternating machine halts within this bound and returns the language indicator.

Fix an input word and apply the run analysis (`one_run`), which splits into two cases. In the first, the word has the required encoding shape and its certificate passes the preliminary check. The analysis supplies a scanned configuration and a register assignment whose values are bounded by the input-dependent bound. The acceptance-check characterization (`acceptLang_iff`) together with the preliminary-check characterization (`validChk_iff_pre`) identifies membership in the language with the conjunction that the scanned configuration is accepting and that its stored state/output summary is the accepting one. Thus the language indicator is the decision of this conjunction. The machine reaches the supplied scanned configuration, then returns that decision; the return is permitted by the register bound (`Regs.Bd.val_le`).

In the second case, every correctly shaped encoding fails the preliminary check, and the run analysis supplies a halting rejection. To see that the language indicator is false, suppose the word had a witness configuration for membership. The encoding-to-shape lemma (`shape_of_code`) gives the required shape, while the acceptance-check characterization and preliminary-check characterization would force the preliminary check to pass. This contradicts the case hypothesis. Hence the machine's rejection agrees with the language indicator. Finally, the guard is enlarged to the polynomial register bound using `gd_mono`, so the correctness and space-bound conditions required by the criterion hold in both cases.

**Key facts.** `Complexity.Codec.codecAs_mem`, `Complexity.Codec.one_run`, `Complexity.Codec.acceptLang_iff`, `Complexity.Codec.validChk_iff_pre`, `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.shape_of_code`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AReach.halt`, `Complexity.Codec.gd_mono`, `Complexity.LogProg.arm_decides_poly`.
