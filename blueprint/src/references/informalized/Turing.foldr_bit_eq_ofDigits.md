<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.foldr_bit_eq_ofDigits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Folding Bits Gives Their Binary Digits

**Claim.** For every finite Boolean word $w$, folding its bits from the right with the binary place-value operation, starting from zero, gives the natural number whose base-two digits are the natural-number values of the bits of $w$, in their original order.

**Proof.** The base-two digit expansion is characterized by a right fold whose step sends a digit $d$ and tail value $n$ to $d+2n$. Rewriting the digit expansion by this fold and distributing the map from Boolean bits to natural numbers through the list fold reduces the claim to equality of the two step functions. For a Boolean bit, the two possibilities are $0$ and $1$; in either case, its natural-number value plus twice the tail is exactly the binary bit operation. Thus the folds, and hence the claimed numbers, agree.
