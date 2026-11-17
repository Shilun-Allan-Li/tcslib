<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.basisExpandedSmallBias_dyadicParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dyadic parameter identity

**Claim.** If $t\le\ell$ and $n=2^{\ell-t}$, then $n/2^\ell=(1/2)^t$ as real numbers.

**Proof.** Substitute $n=2^{\ell-t}$. The resulting equality is the dyadic field-ratio identity: for $t\le\ell$, the ratio $2^{\ell-t}/2^\ell$ equals $(1/2)^t$ (\(\texttt{dyadicFieldRatio\_eq\_invPow}\)).

**Key facts.** `FABL.dyadicFieldRatio_eq_invPow`.
