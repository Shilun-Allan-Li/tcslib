<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSolve_closed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Split Solver

**Claim.** For every pair of natural numbers $C$ and $e$, there is a finite Turing machine over the Boolean alphabet and a constant $c$ that computes the specified split encoding (or the empty word when no valid split exists), halts within $c(|w|+1)^{e+2}$ steps, and uses at most $c(|x|+1)^{e+1}$ space through every step.

**Proof.** The proof separates the constant case $e=0$ from the positive-exponent case. In each case it supplies a machine that fills a split bank with the required number of marker symbols, then applies the split-source construction (`f2_splitSolve_source`). That construction turns the bank routine into a machine which solves the split problem, with the stated polynomial time and space bounds, provided the routine’s running time satisfies its required bound.

1. When $e=0$, use the machine that catalogs a fixed prefix of $C$ markers. Its source routine completes in $C+1$ steps and leaves exactly $C$ markers in the bank (`f2_splitSource_constant`). This time is bounded by the source construction’s required expression $(C+1)(l+1)^0+1$ for every input length $l$. The split-source construction therefore gives the desired solver and bounds.

2. When $e$ is positive, write it as $e+1$ and use the polynomial unary catalog machine with parameter $e$. Its source routine completes in $f2\_catalogPolyCost(l+1,C,e+1)+1$ steps and leaves $C(l+1)^{e+1}$ markers in the bank (`f2_splitSource_poly`). The catalog cost estimate bounds the cost term by $(C+1+5(e+1))(l+1)^{e+1}$ (`f2_catalogPolyCost_le`); adding one gives the source-time bound required by the split-source construction. Applying that construction yields a solver with time exponent $(e+1)+2$ and space exponent $(e+1)+1$, as required for the successor case.

**Key facts.** `Turing.FinTM.f2_splitSolve_source`, `Turing.FinTM.f2_splitSource_constant`, `Turing.FinTM.f2_splitSource_poly`, `Turing.FinTM.f2_catalogPolyCost_le`.
