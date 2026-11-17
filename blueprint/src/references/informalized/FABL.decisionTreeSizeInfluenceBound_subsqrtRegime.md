<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.decisionTreeSizeInfluenceBound_subsqrtRegime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sub-square-root influence regime

**Claim.** The decision tree influence bound satisfies the sub-square-root regime conditions, including the bound by $(d+2)(\sqrt{\lceil\log_2(n+1)\rceil}+1)$.

**Proof.** The dimension and precision components of the regime follow directly from the hypotheses. For the influence estimate, put $L=\lceil\log_2(n+1)\rceil$ and $r=\lfloor\sqrt L\rfloor$. The integer square-root bound gives $L\le(r+1)^2$, while $d\le(d+1)^2$. Multiplying shows $dL\le((d+1)(r+1))^2$, and monotonicity of the integer square root therefore gives $\lfloor\sqrt{dL}\rfloor\le(d+1)(r+1)$. Since $r+1\ge1$, adding one yields $\lfloor\sqrt{dL}\rfloor+1\le(d+2)(r+1)$, which is the required envelope.
