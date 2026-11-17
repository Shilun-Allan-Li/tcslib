<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Odometer.lean :: Light.incDigits_digitsLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incrementing a base expansion

**Claim.** For positive base $b$, incrementing the length-$n$ digit list of $c$ by the stated carry rule gives the length-$n$ digit list of $c+1$.

**Proof.** Proceed by induction on the length $n$, generalizing over $c$. At length zero both digit lists are empty. For the successor length, the digit list begins with $c\bmod b$, followed by the length-$n$ digit list of $c/b$ (`digitsLE_succ`). Since $b>0$, the first digit is less than $b$, so there are two cases.

If $(c\bmod b)+1<b$, there is no carry. The quotient and remainder formula for adding one below the next multiple of $b$ says that $(c+1)/b=c/b$ and $(c+1)\bmod b=(c\bmod b)+1$ (`Nat.succ_div_mod_of_lt`). Thus the first digit increments and the remaining digits stay the same, as required.

Otherwise the first digit is exactly $b-1$, so incrementing it causes a carry. The quotient and remainder formula at the boundary says that $(c+1)/b=c/b+1$ and $(c+1)\bmod b=0$ (`Nat.succ_div_mod_of_eq`). The first digit resets to zero, while the remaining digits are the incremented length-$n$ digit list of $c/b$ by the induction hypothesis. This is precisely the carry rule.

**Key facts.** `Light.digitsLE_succ`, `Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_eq`.
