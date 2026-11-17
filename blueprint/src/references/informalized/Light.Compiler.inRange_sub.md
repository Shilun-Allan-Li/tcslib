<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.inRange_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range Bounds for Differences

**Claim.** If $x$ and $y$ each have absolute value at most the word limit, then both $x-y$ and $x-y-1$ satisfy the stated range bounds.

**Proof.** Write $L=Z.lim.word$. The absolute-value hypotheses give $-L\le x,y\le L$. Thus $x-y$ lies between $-2L$ and $2L$, while $x-y-1$ lies between $-2L-1$ and $2L-1$. Doubling these inequalities shows that for either value $v$, $-4L-2\le 2v\le 4L$. The word-fit condition $2(2L+2)<2^W$ says $4L+4<2^W$, so in particular $4L<2^W$ and $-2^W<-4L-2$. Hence $-2^W\le 2v<2^W$ in both cases.
