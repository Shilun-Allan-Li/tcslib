<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.timeConstructible_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Constructibility

**Claim.** For natural numbers $C,c$ with $C>0$, the function $T(n)=C(n+1)^{c+1}$ is time constructible.

**Proof.** First, $(n+1)^{c+1}\ge n+1$, since $c+1\ge1$; and $C\ge1$. Hence $n\le T(n)$. For the machine, compose two computations. The identity time-constructibility result supplies a machine that outputs the binary representation of the input length in linear time ( `timeConstructible_id` ). The unary polynomial machine outputs a string of $T(|x|)$ true bits in time $A(|x|+1)^{c+1}$, where $A=C+5(c+1)+4$ ( `poly_unary_computes` ). Composing the unary polynomial machine with the length counter produces the binary representation of $T(|x|)$; the composition theorem gives a machine with a bound of the form $b(T_1(n)+T_2(T_1(n))+1)$ ( `computesFunInTime_comp` ). Here the second machine's time bound is monotone, as required by that theorem. Substituting the two bounds and using $T(n)\ge(n+1)^{c+1}$ shows that the composed runtime is at most $(b+1)(a+1)(A+1)(T(n)+1)$, where $a,b$ are the constants from the component and composition bounds. This is a positive constant multiple of $T(n)+1$, so the required machine and time constant exist; any smaller established runtime can be extended to this bound by `ComputesInTime.mono`.

**Key facts.** `Complexity.timeConstructible_id`, `Complexity.poly_unary_computes`, `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.ComputesInTime.mono`.
