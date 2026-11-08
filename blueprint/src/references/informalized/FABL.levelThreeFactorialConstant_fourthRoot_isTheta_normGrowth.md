<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.levelThreeFactorialConstant_fourthRoot_isTheta_normGrowth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial growth and norm growth

**Claim.** As $d$ tends to infinity, the fourth root of the factorial constant is asymptotically of the same order as the stated norm growth.

**Proof.** The factorial constant and the book growth are nonnegative for every natural number. Taking their one-fourth powers preserves their asymptotic equivalence, by the power rule for asymptotic equivalence (`Asymptotics.IsTheta.rpow`) applied to the established equivalence between the factorial constant and the book growth (`FABL.levelThreeFactorialConstant_isTheta_bookGrowth`). For every positive $d$, the fourth root of the book growth equals the norm growth (`FABL.levelThreeBookGrowth_fourthRoot_eq_normGrowth`). Thus the two functions are eventually equal after this replacement, and therefore are asymptotically equivalent. In particular, their ratio is eventually bounded above and below by positive constants.

**Key facts.** `FABL.levelThreeFactorialConstant_isTheta_bookGrowth`, `FABL.levelThreeBookGrowth_fourthRoot_eq_normGrowth`.
