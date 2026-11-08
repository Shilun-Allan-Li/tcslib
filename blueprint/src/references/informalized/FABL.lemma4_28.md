<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lemma4_28 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit switching bound

**Claim.** Under the stated circuit, size, width, and parameter hypotheses, the random-restriction switching-failure probability is at most $\varepsilon$.

**Proof.** The proof applies the established half-switching bound for circuits (`hastadHalfSwitchingBoundForCircuits`) as the switching hypothesis in the general circuit switching theorem (`lemma4_28_of_halfSwitching`). That theorem, with the given circuit representation and parameter hypotheses, yields the stated upper bound on the switching-failure probability.

**Key facts.** `FABL.hastadHalfSwitchingBoundForCircuits`, `FABL.lemma4_28_of_halfSwitching`.
