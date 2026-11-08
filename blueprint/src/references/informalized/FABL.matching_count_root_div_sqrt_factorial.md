<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.matching_count_root_div_sqrt_factorial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Matching Identity

**Claim.** For positive integers $r$ and natural numbers $k$, the $1/(2r)$-th power of $\bigl((2r-1)/r\bigr)^{rk}(rk)!$, divided by $\sqrt{k!}$, equals the matching improvement constant times $(\sqrt{2r-1})^k$.

**Proof.** Put $X=2r-1$, $R=r$, $F=k!$, $G=(rk)!$, $m=rk$, and $q=2r$. Write the left side as $A$ and the proposed right side as $T$. The hypotheses give $X\ge 0$ and $R>0$, while factorials are positive, so the quantities being rooted are nonnegative. Raising $A$ to the $q$-th power and using the defining property of the nonnegative square root gives $A^q=D/F^r$, where $D=(X/R)^mG$. Raising $T$ to the same power gives $T^q=E X^m/F^r$, where $E=G/(F^rR^m)$; here $(\sqrt X)^{kq}=X^m$. Since $R>0$, cancellation of $R^m$ shows $E X^m/F^r=D/F^r$. Thus $A^q=T^q$. Both $A$ and $T$ are nonnegative, and the map taking a nonnegative real to its $q$-th power is injective for positive $q$, so $A=T$. Unfolding the abbreviations and using the natural-to-real cast identity for $2r-1$ gives the stated formula.
