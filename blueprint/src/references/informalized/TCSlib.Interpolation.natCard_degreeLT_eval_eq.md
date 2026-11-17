<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Interpolation.lean :: TCSlib.Interpolation.natCard_degreeLT_eval_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of Partially Interpolated Polynomials

**Claim.** For finite sets $t\subseteq s$, with $v$ injective on $s$, the number of polynomials of degree less than $|s|$ that agree with prescribed values on the nodes indexed by $t$ is $|F|^{|s|-|t|}$.

**Proof.** The fixed evaluation equivalence identifies each polynomial of degree less than $|s|$ satisfying the prescribed values on $t$ with an arbitrary function on the remaining indices $s\setminus t$. Thus the desired count is the number of functions from that difference set to $F$, namely $|F|^{|s\setminus t|}$. Since $t\subseteq s$, the difference set has cardinality $|s|-|t|$, giving the stated power.
