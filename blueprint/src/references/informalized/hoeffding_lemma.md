<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: hoeffding_lemma -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hoeffding's Lemma for a Bernoulli Variable

**Claim.** For $p\in[0,1]$ and real $h$, $\log((1-p)+pe^h)\le ph+h^2/8$.

**Proof.** Apply the Bernoulli moment-generating-function bound `bernoulli_mgf_bound` with parameter $L=p$ and exponent parameter $-h$. Its left side is $\log(1-p+pe^h)$, while its right side is $ph+h^2/8$ after simplifying the signs. The hypotheses on $p$ are exactly those required by that bound.

**Key facts.** `bernoulli_mgf_bound`.
