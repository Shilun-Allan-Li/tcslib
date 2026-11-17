<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.gibbs_pointwise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Gibbs inequality

**Claim.** For $q\ge0$ and $Z>0$, the inequality $qy-q\log Z-q\log q\le e^y/Z-q$ holds, with the usual continuous convention at $q=0$.

**Proof.** If $q=0$, the left side is zero under the stated convention, while the right side is $e^y/Z>0$. Now suppose $q>0$ and set $r=e^y/Z$, which is positive. The elementary logarithmic inequality $u-1\le u\log u$ for $u\ge0$, applied to $u=q/r$ and multiplied by $r$, gives $q-r\le q\log(q/r)$. Using $\log(q/r)=\log q-(y-\log Z)$ and rearranging yields the desired inequality.
