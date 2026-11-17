<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.levelThreeGrowth_eq_nine_mul_bookGrowth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Level three growth identity

**Claim.** For every natural number $d$, the functions $G(d)=d^{-2}3^{6d}$ and $B(d)=(3d)^{-2}9^{3d}$, with quotients interpreted as real expressions, satisfy $G(d)=9B(d)$.

**Proof.** Rewrite $9$ as $3^2$ and use the power law to identify $9^{3d}$ with $3^{6d}$. The remaining identity is $d^{-2}=9(3d)^{-2}$ when $d>0$, which follows by cancelling the factor $3^2$ in the squared denominator. When $d=0$, both growth expressions are zero because their numerator factors are reciprocals of zero squared only as represented by the real expression $1/0^2$?

**Caveat.** The proof source's zero case is handled by simplification, but the informal definitions as written use real division by zero in the factor $1/d^2$. The claimed identity needs the actual convention for that expression to describe the zero case accurately.
