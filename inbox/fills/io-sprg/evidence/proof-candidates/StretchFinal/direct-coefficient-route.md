# Preferred07: coefficient kept, monic normalization avoided — NOT RUN

Let s=seedBitsAt(k), m=outputLength(k), x=(k:Real), with x>=1.
Existing helper05 gives eventually s<=m*x^-epsilon, epsilon>0.

1. Public PolyExpr.eval_le for the composed actual output bound gives C,c and
   m<=C*(k+1)^c. Pointwise k+1<=2k and existing natural-power monotonicity give
   m<=D*x^c, D=max1(C*2^c)>=1. The coefficient D is RETAINED.
2. Set eta=epsilon/(2*(c+1))>0 and rho=1+eta>1. Field cancellation yields
   (c+1)*eta=epsilon/2, hence c*eta<=epsilon/2.
3. Existing tendsto_rpow_atTop at exponent epsilon/2, composed with the natural
   cast limit, gives a single cutoff after which D^eta<=x^(epsilon/2).
4. Real.rpow_le_rpow and mul_rpow then give
     m^eta <=D^eta*(x^c)^eta=D^eta*x^(c*eta).
   This is an ordinary real-power product estimate, not a new eventual monic
   output-power theorem. The generic public PadQuad statement is neither
   invoked nor rederived.
5. Since m>=1 from input Boolean stretch at n>=k>=1, all m-positive exponent
   identities apply. Raise s<=m*x^-epsilon to rho and calculate
     s^rho <=m*m^eta*x^(-epsilon*rho)
           <=m*D^eta*x^(c*eta)*x^(-epsilon*rho)
           <=m*x^(epsilon/2+c*eta-epsilon*rho)
           <=m.
   The final exponent is <=0 since c*eta<=epsilon/2 and epsilon<=epsilon*rho.
6. The maximum of the seed-gap cutoff, coefficient cutoff and1 works. Transfer
   s and m with existing jls field readers. Add SP-W3's k<=seedBits using the
   stronger all-k lower bound k+1<=seedBits (public residue count>=1).

Exact public APIs are in APIs.tsv; no new import is needed. This route follows
root's review and replaces old02/06. No source edits or Lean execution occurred.
