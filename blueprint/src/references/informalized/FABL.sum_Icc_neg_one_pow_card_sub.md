<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.sum_Icc_neg_one_pow_card_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alternating Sum over an Interval of Subsets

**Claim.** For finite sets $T\subseteq U$, the sum of $(-1)^{|S|-|T|}$ over all $S$ with $T\subseteq S\subseteq U$ is $1$ if $T=U$ and $0$ otherwise.

**Proof.** Write each set in the interval uniquely as $T\cup R$, where $R\subseteq U\setminus T$. The union is disjoint, so $|T\cup R|-|T|=|R|$. Thus the sum becomes the alternating sum over all subsets of $U\setminus T$. The powerset alternating-sum identity gives $1$ when $U\setminus T$ is empty and $0$ otherwise. Since $T\subseteq U$, the difference is empty exactly when $T=U$, yielding the stated result.
