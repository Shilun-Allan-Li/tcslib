<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.validLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace recognition of valid codes

**Claim.** For each finite nondeterministic Turing machine $N$, the language of encodings of configuration codes for configurations of $N$ lying within the stated work-tape window is decidable in logarithmic space.

**Proof.** The proof constructs a logarithmic-space ARM decider using the valid-code codec program and the two auxiliary logspace languages in `codecAs`. Its correctness is established by analyzing the execution of the program on an input $y`.

1. The execution lemma (`one_run`) divides inputs into two cases. In the first, the input has the required encoding shape and passes the preliminary checks; the program reaches a completed scan state whose scan component is the scan of the candidate configuration word. In the second, every correctly shaped parse fails a preliminary check, and the program halts with answer false.

2. In the first case, the characterization of language membership (`validLang_iff`), together with the preliminary-check characterization (`validChk_iff_pre`), shows that the language indicator on $y$ equals the decision of whether the completed scan state is accepting. Thus the program's final answer agrees with the language indicator: it reaches its return instruction after the scan, and that instruction returns exactly this acceptance decision. The register bound supplied by `one_run` fits the chosen polynomial bound, and `gd_mono` transfers the execution's guard and register bounds to the conditions required by the general logspace construction theorem.

3. In the second case, suppose for contradiction that $y$ belongs to the language. Its membership witness determines the required input shape (`shape_of_code`), and the membership characterization yields a valid preliminary check. This contradicts the failure condition from `one_run`. Hence the language indicator is false, matching the program's false halt.

The general theorem that a polynomially bounded ARM with logspace oracle languages decides a language in logspace (`arm_decides_poly`) now applies. The auxiliary oracle languages are logspace by `codecAs_mem`; therefore the target language is in logspace.

**Key facts.** `Complexity.Codec.codecAs_mem`, `Complexity.Codec.one_run`, `Complexity.Codec.validLang_iff`, `Complexity.Codec.validChk_iff_pre`, `Complexity.Codec.indicator_eq_of_iff`, `Complexity.Codec.shape_of_code`, `Complexity.Codec.gd_mono`, `Complexity.LogProg.AReach.halt`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AHalt.mono`, `Complexity.LogProg.arm_decides_poly`.
