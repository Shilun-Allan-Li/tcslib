<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.badInput_card_ge_half_of_small_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Many bad inputs at small cost

**Claim.** For $n\ge 300$, if the protocol cost is at most $\lfloor n/10\rfloor$, then at least $2^{n-1}$ inputs are bad.

**Proof.** Let the good inputs be those within Hamming distance less than $n/4$ of some answer vector, and let the bad inputs be their complement. First bound the number of good inputs. Each answer vector has at most $2\binom{n}{\lfloor n/4\rfloor}$ inputs in its relevant Hamming ball, so the number of good inputs is at most the number of answer vectors times this quantity (\texttt{goodInput\_card\_le}). The number of answer vectors is at most $2^c$ (\texttt{answerSet\_card\_le\_pow\_cost}), hence at most $2^{\lfloor n/10\rfloor}$ by the cost hypothesis. Also, $\binom{n}{\lfloor n/4\rfloor}\le 11^{\lfloor n/4\rfloor}$ for $n\ge300$ (\texttt{choose\_quarter\_le\_eleven\_pow}). Therefore $|\mathrm{good}|\le 2^{\lfloor n/10\rfloor+1}11^{\lfloor n/4\rfloor}$.\n\nSquare this estimate and use $11^2\le 2^7$ to obtain $|\mathrm{good}|^2\le 2^{2(\lfloor n/10\rfloor+1)+7\lfloor n/4\rfloor}$. For $n\ge300$, the exponent is at most $2(n-1)$, so $|\mathrm{good}|^2\le (2^{n-1})^2$. Since these quantities are nonnegative, $|\mathrm{good}|\le 2^{n-1}$. Finally, the good and bad inputs partition all $2^n$ Boolean strings, and $2^n=2^{n-1}+2^{n-1}$. Subtracting the good-input bound yields $|\mathrm{bad}|\ge2^{n-1}$.

**Key facts.** `CommunicationComplexity.Functions.Indexing.goodInput_card_le`, `CommunicationComplexity.Functions.Indexing.answerSet_card_le_pow_cost`, `CommunicationComplexity.Functions.Indexing.choose_quarter_le_eleven_pow`.
