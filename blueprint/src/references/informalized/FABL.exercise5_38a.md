<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.exercise5_38a -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Large-parameter negativity

**Claim.** If $1\le C$, $0<\delta$, and $1/(10C)<\delta$, then $1-\delta/2-2\eta(C,\delta)<0$.

**Proof.** Put $x=C\delta$, so $x>0$ and the large-parameter hypothesis gives $x>1/10$. Also put $L=\log_2(1/x)$ and $M=\max\{L,1\}$. It suffices to show $1<32x^2M$, since $2\eta(C,\delta)=32x^2M$.

Split into ranges for $x$. If $x\le 1/9$, then $1/x\ge9$, so monotonicity of the base-two logarithm gives $L\ge\log_2 9>25/8$. Thus $M>25/8$, while $x^2>1/100$. These bounds imply $32x^2M>32(1/100)(25/8)=1$.

If $1/9<x\le1/8$, then $1/x\ge8$, giving $L\ge\log_2 8=3$ and hence $M\ge3$. Since $x^2>1/81$, we get $32x^2M>32(1/81)3>1$. If $1/8<x\le1/4$, use $1/x\ge4$ to obtain $M\ge L\ge\log_2 4=2$, and $x^2>1/64$; consequently $32x^2M>1$. Finally, if $x>1/4$, then $M\ge1$ and $x^2>1/16$, again giving $32x^2M>1$.

Therefore $1-\delta/2-32x^2M<0$, since $\delta>0$. Replacing $x$ and $M$ by their definitions proves the claim.

**Key facts.** `FABL.twentyFiveDivEight_lt_logb_two_nine`, `FABL.logb_two_eight`, `FABL.logb_two_four`.
