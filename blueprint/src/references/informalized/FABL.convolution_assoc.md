<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ProbabilityDensitiesAndConvolution.lean :: FABL.convolution_assoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Associativity of convolution

**Claim.** For functions on $(\mathbb{F}_2)^n$, convolution is associative: $f*(g*h)=(f*g)*h$.

**Proof.** Evaluate both sides at an arbitrary point $x$ and express convolution as a uniform average. Expanding the inner convolutions gives an iterated average over variables, with integrand involving $f$, $g$, and $h$. Interchanging the order of the finite averages puts the expression in a form where, for each fixed value $z$ of the outer variable, the change of variables $w=y+z$ reindexes the inner average without changing its value. Since every coordinate lies in $\mathbb{F}_2$, one has $z+z=0$, so the translated argument $x+z+(w+z)$ simplifies to $x+w$. The two iterated averages therefore agree at every $x$, proving associativity.

**Key facts.** `FABL.convolution_apply_add`.
