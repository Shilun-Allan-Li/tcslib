<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.vword_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Register Call

**Claim.** Calling the whole-input decider on input segment $x$ and the single register containing the bits of $i$ produces the encoded word $\langle x,\operatorname{bits}(i)\rangle$, independently of the state, decider, and successor states.

**Proof.** The sole argument register contains the word $\operatorname{bits}(i)$: the tape-to-word fact identifies the word represented by a buffer tape with the stored list (`tapeWord_bufferTape`). The whole-input mode renders the input segment by doubling each bit of $x$, while the single final argument is rendered without doubling. The virtual-word construction places the separator $[\mathrm{false},\mathrm{true}]$ between these segments. Consequently the result is $\operatorname{dbl}(x)\mathbin{++}[\mathrm{false},\mathrm{true}]\mathbin{++}\operatorname{bits}(i)$, which is the pair encoding by `pairEncode_eq_dbl`.

**Key facts.** `Complexity.LogProg.tapeWord_bufferTape`, `Turing.pairEncode_eq_dbl`.
