<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.sqrt_average_of_sq_difference_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square-Root Average Bound

**Claim.** If $A,B\ge 0$ and $(A-B)^2\le 8c^2(A+B-2c^2)$, then $c\le (\sqrt A+\sqrt B)/2$.

**Proof.** Let $x=\sqrt A$ and $y=\sqrt B$, so $x,y\ge0$, $x^2=A$, and $y^2=B$. The assumed inequality implies $(4c^2-A-B)^2\le4AB$. Suppose, toward a contradiction, that $c>(x+y)/2$. Then $x+y<2c$, and hence $(x+y)^2<4c^2$. Since $(x+y)^2=A+B+2xy$, this gives $4c^2-A-B-2xy>0$. Also $4c^2-A-B+2xy>0$, because it exceeds the preceding positive quantity by $4xy\ge0$. Their product is therefore positive. But that product equals $(4c^2-A-B)^2-4AB$, contradicting the inequality already deduced. Thus $c\le(x+y)/2$.
