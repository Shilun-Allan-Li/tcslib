<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/DirectionalDerivatives.lean :: FABL.domainTranslate_booleanDerivative_eq_two_translates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translated Boolean Derivative

**Claim.** Translating the Boolean derivative in direction $y+y'$ by $y$ gives the function $x\mapsto f(x+y)+f(x+y')$.

**Proof.** Evaluate the translated derivative at $x$. By the definition of translation (`domainTranslate_apply`) and of the Boolean derivative, the result is $f(x+y)+f((x+y)+(y+y'))$. Associativity and commutativity of addition let us regroup the second argument as $x+y+(y+y')=x+(y+(y+y'))=x+((y+y)+y')$. In the Boolean cube, $y+y=0$, so this reduces to $x+y'$. The value is therefore $f(x+y)+f(x+y')$ at every $x$, proving equality of the functions.

**Key facts.** `FABL.domainTranslate_apply`.
