<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.LogProg.vword_whole₃ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Register Whole-Input Encoding

**Claim.** For any bit string $u$, decider index, register indices $r,s,t$, states $l_1,l_0$, and assignment $V$, the virtual word in whole-input mode with registers $r,s,t$ is the encoded pair $(u,(V(r),(V(s),V(t))))$.

**Proof.** The whole-input mode makes the first segment $(u,\mathrm{true})$, so rendering it doubles every bit of $u$. The three register arguments are segmented in order: the first register word is doubled, while the second and third are grouped into the final segment and left undoubled. Since the virtual word inserts the separator $[\mathrm{false},\mathrm{true}]$ between successive segments, it consists of the doubled input, a separator, the doubled word $V(r)$, another separator, and the concatenation of the doubled word $V(s)$ with $V(t)$. The encoding identity $\operatorname{pairEncode}(x,y)=\operatorname{dbl}(x)++[\mathrm{false},\mathrm{true}]++y$ (\texttt{Turing.pairEncode\_eq\_dbl}) identifies this list with the stated nested pair encoding.

**Key facts.** `Turing.pairEncode_eq_dbl`.
