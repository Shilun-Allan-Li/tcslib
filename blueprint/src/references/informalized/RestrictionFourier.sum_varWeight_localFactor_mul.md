<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: RestrictionFourier.sum_varWeight_localFactor_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Averaging a Product of Two Local Factors over a Coordinate

**Claim.** Fix a real parameter $p$, three subsets $U,V,S\subseteq[n]$, and a coordinate $i\in[n]$. The per-coordinate value $v$ ranges over the three possibilities — the "free" value (none) and the two fixed signs (some false, some true) — weighted by $w_p(\text{free})=p$ and $w_p(\text{sign})=\tfrac{1-p}{2}$. The weighted sum of the product $\ell_{U,S}(i,v)\,\ell_{V,S}(i,v)$ of the two local factors equals $p$ when $i\in S$; equals $1-p$ when $i\notin S$ and $i$ lies in both $U$ and $V$; equals $0$ when $i\notin S$ and $i$ lies in exactly one of $U,V$; and equals $1$ when $i\notin S$ and $i$ lies in neither $U$ nor $V$.

**Proof.** Recall the two ingredients. The weight is $w_p(\text{none})=p$ and $w_p(\text{some }b)=\tfrac{1-p}{2}$ for either sign. The local factor is
\[
  \ell_{W,S}(i,v)=
  \begin{cases}
    [\,v=\text{none}\,] & i\in S,\\
    \chi(v) & i\notin S,\ i\in W,\\
    1 & i\notin S,\ i\notin W,
  \end{cases}
\]
where $[\,v=\text{none}\,]$ is $1$ on the free value and $0$ on a sign, and $\chi(\text{none})=0$, $\chi(\text{some false})=+1$, $\chi(\text{some true})=-1$ (the sign attached to a Boolean). The sum has exactly three terms, one for each $v\in\{\text{none},\text{some false},\text{some true}\}$.

The proof simply splits on the three membership questions $i\in S$, $i\in U$, $i\in V$ and evaluates the three terms in each case; the only arithmetic of substance is a cancellation of two equal-and-opposite signs. We organize the eight cases by the four outcomes of the statement.

1. **$i\in S$ (value $p$).** Here both local factors equal $[\,v=\text{none}\,]$, so their product is $1$ at $v=\text{none}$ and $0$ at either sign. Only the free term survives, contributing $w_p(\text{none})\cdot 1=p$.

2. **$i\notin S$, $i\in U$, $i\in V$ (value $1-p$).** Both factors equal $\chi(v)$. At $v=\text{none}$ the product is $0$. At a sign $b$ the product is $\chi(\text{some }b)^2=1$, since $(\pm1)^2=1$. Hence only the two sign terms survive, each with weight $\tfrac{1-p}{2}$, giving $\tfrac{1-p}{2}+\tfrac{1-p}{2}=1-p$.

3. **$i\notin S$, exactly one of $i\in U$, $i\in V$ (value $0$).** Say $i\in U$ but $i\notin V$ (the other sub-case is symmetric). Then $\ell_{U,S}(i,v)=\chi(v)$ while $\ell_{V,S}(i,v)=1$ identically, so the product is just $\chi(v)$. The free term vanishes, and the two sign terms are
   \[
     \tfrac{1-p}{2}\,\chi(\text{some false})+\tfrac{1-p}{2}\,\chi(\text{some true})
     =\tfrac{1-p}{2}(+1)+\tfrac{1-p}{2}(-1)=0.
   \]
   The equal weighting of the two opposite signs is exactly what makes this cancel.

4. **$i\notin S$, $i\notin U$, $i\notin V$ (value $1$).** Both factors are identically $1$, so the sum is just the total weight $w_p(\text{none})+2\cdot\tfrac{1-p}{2}=p+(1-p)=1$.

In every case the value matches the stated branch, which completes the proof. Mechanically this is one exhaustive case split followed by unfolding the definitions and a short ring computation; no auxiliary lemmas are needed.
