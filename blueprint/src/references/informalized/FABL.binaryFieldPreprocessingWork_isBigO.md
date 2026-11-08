<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFieldPreprocessingWork_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Preprocessing Work

**Claim.** As $\ell$ tends to infinity through the natural numbers, the binary field preprocessing work is $O(2^{8\ell})$.

**Proof.** The pointwise preprocessing estimate gives $\mathrm{binaryFieldPreprocessingWork}(\ell)\le 2^{8(\ell+1)}$ (`binaryFieldPreprocessingWork_le`). Since $2^{8(\ell+1)}=2^8\,2^{8\ell}$, the preprocessing work is bounded at every $\ell$ by the fixed constant $2^8$ times $2^{8\ell}$. This uniform bound is precisely the definition of the asserted big-$O$ estimate.

**Key facts.** `FABL.binaryFieldPreprocessingWork_le`.
