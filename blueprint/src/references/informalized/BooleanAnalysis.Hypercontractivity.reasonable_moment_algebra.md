<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.reasonable_moment_algebra -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment algebra inequality

**Claim.** If $R\ge9$, $a,b,C,D\ge0$, $A\le Ra^2$, $D\le b^2$, and $C^2\le AD$, then $A+6C+RD\le R(a+b)^2$.

**Proof.** First, $R\ge9$ implies $R\ge0$, so multiplying $A\le Ra^2$ and $D\le b^2$ using the nonnegative factors gives $C^2\le AD\le Ra^2b^2$. Also $9R\le R^2$. Multiplying this inequality by $a^2b^2\ge0$ and combining with the bound on $C^2$ yields $(3C)^2\le(Rab)^2$. Both $3C$ and $Rab$ are nonnegative, so $3C\le Rab$. Further, $RD\le Rb^2$. Now use $A\le Ra^2$, $RD\le Rb^2$, and $6C\le2Rab$ to obtain $A+6C+RD\le Ra^2+2Rab+Rb^2=R(a+b)^2$.
