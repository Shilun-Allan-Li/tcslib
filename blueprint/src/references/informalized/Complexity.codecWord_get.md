<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecWord_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Boolean Value from Its Code

**Claim.** For finite $\alpha$, $L\ge |\alpha|$, and $a:\alpha\to\{\mathrm{false},\mathrm{true}\}$, the encoded Boolean list has value $a(i)$ at the position assigned to each $i\in\alpha$.

**Proof.** The enumeration of $\alpha$ identifies $i$ with an index strictly below $|\alpha|$. Since $|\alpha|\le L$, that index is also strictly below $L$, so it lies in the unpadded portion of the encoded list. By the definition of the encoding, the entry there is the value of $a$ at the element corresponding to that index; the enumeration sends this index back to $i$. Therefore the recovered entry is $a(i)$.
