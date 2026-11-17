<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_binary_check -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Representation and Width

**Claim.** For $f:\mathbb{N}\to\mathbb{N}$ and Boolean words $w,s$ with $|s|\le |w|$, the binary digit words of $f(|s|)$ and the length of the suffix of $w$ after its first $|s|$ entries are equal exactly when $|s|+f(|s|)=|w|$.

**Proof.** The binary digit map is injective (`Turing.FinTM.emitter_bits_injective`), so equality of the two digit words is equivalent to equality of the natural numbers they represent: $f(|s|)=|(w.drop\ |s|)|$. The suffix length is $|w|-|s|$ when $|s|\le |w|$ (`List.length_drop`). Rearranging this equality gives $|s|+f(|s|)=|w|$, and the same arithmetic in reverse proves the converse.

**Key facts.** `Turing.FinTM.emitter_bits_injective`.
