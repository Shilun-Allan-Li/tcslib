<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.two_mul_sq_le_two_pow_of_seven_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bound by a power of two

**Claim.** For every natural number \(m\ge 7\), \(2m^2\le 2^m\).

**Proof.** Proceed by induction from \(m=7\), where the inequality is checked directly. For the induction step, assume \(2m^2\le 2^m\). For \(m\ge7\), one has \((m+1)^2\le 2m^2\), as follows by expanding and comparing the two sides. Therefore \(2(m+1)^2\le 2(2m^2)\le 2\cdot 2^m=2^{m+1}\), which proves the next case.
