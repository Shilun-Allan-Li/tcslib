<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.reciprocal_natFloor_one_div_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal Floor Bounds

**Claim.** For $0<\delta\le1/2$, if $m=\lfloor1/\delta\rfloor$, then $\delta\le1/m\le2\delta$ and $1/m-\delta\le2\delta^2$.

**Proof.** Since $1/\delta\ge2$, its floor $m$ is at least $2$, so in particular $m>0$. The defining floor bounds give $m\le1/\delta$ and $1/\delta-1<m$. Multiplying the first inequality by positive $\delta$ gives $m\delta\le1$; multiplying the second by $\delta$ and rearranging gives $1-\delta<m\delta$. Dividing the first of these bounds by positive quantities yields $\delta\le1/m$. The second implies $1<2m\delta$, which yields $1/m<2\delta$ and hence the claimed weak upper bound. Finally, $0\le1-m\delta\le\delta$. The identity $1/m-\delta=(1/m)(1-m\delta)$, together with $1/m\le2\delta$, gives $1/m-\delta\le2\delta^2$.
