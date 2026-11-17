<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productResamplingNoiseSensitivity_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero resampling noise sensitivity

**Claim.** At resampling rate zero, the product resampling noise sensitivity of any function on length-$n$ inputs over a finite state space is zero.

**Proof.** At rate zero the retention probability is one. Relate the retention experiment to the selector experiment at correlation $1$ using `literalProductSelectorPairPMF_eq_productRetention`; the selector-retention probability at $1$ is also one. Now fix the two product inputs. The resulting Boolean function of the selectors has noise sensitivity zero at rate zero: by the Fourier-level formula (`noiseSensitivity_eq_sum_level`), every summand contains the factor $1-(1-2\cdot0)^k=0$. Thus each conditional disagreement expectation is zero. Averaging first over one product input and then over the other leaves zero, since the expectation of a constant equals that constant (`pmfExpectation_const`).

**Key facts.** `FABL.literalProductSelectorPairPMF_eq_productRetention`, `FABL.pmfExpectation_literalProductSelectorPairPMF`, `FABL.noiseSensitivity_eq_sum_level`, `FABL.pmfExpectation_const`.
