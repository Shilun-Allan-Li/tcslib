<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.normalize_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit normal form

**Claim.** Every nonzero nonnegative function on the one-bit cube has the form $f(x)=c(1+a\sigma(x_0))$, where $c>0$ and $a\in[-1,1]$.

**Proof.** Let $u=f(0)$ and $v=f(1)$. Nonnegativity gives $u,v\ge0$. Moreover, $u+v>0$: if their sum were zero, both would vanish, and since the one-bit cube has only the two points $0$ and $1$ (the classification `boolCube_one_cases`), $f$ would be identically zero, contrary to hypothesis. Set $c=(u+v)/2$ and $a=(u-v)/(u+v)$. Then $c>0$. The inequalities $-1\le a$ and $a\le1$ follow respectively from $u-v\ge-(u+v)$ and $u-v\le u+v$, using $u,v\ge0$ and $u+v>0$. At the two cube points, the sign values are $\sigma(0)=1$ and $\sigma(1)=-1$ (`boolToSign_false`, `boolToSign_true`); substituting the chosen $c,a$ gives $c(1+a)=u$ and $c(1-a)=v$. Thus the claimed formula holds everywhere.

**Key facts.** `BooleanAnalysis.Hypercontractivity.boolCube_one_cases`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`.
