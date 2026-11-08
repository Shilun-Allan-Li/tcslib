<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeWord_number -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack encoding of a sentinel code

**Claim.** For every Boolean string $xs$, the compiled stack-machine encoding of the singleton list containing its sentinel numeric code is the stack word of $xs$: the symbols for its bits, followed by the sentinel true-bit symbol and the list terminator.

**Proof.** First show that translating the sentinel number itself yields the symbols for the bits of $xs$, followed by the sentinel true-bit symbol. Proceed by induction on $xs$. For the empty string, the sentinel number is $1$, whose translation is the single true-bit symbol. For a string formed by prepending a bit $b$ to $xs$, the sentinel number is obtained by applying the binary constructor for $b$ to the code of $xs$. The code of $xs$ is positive, so its natural-number representation is a positive binary numeral; the induction hypothesis identifies its translated word. Applying the zero-bit or one-bit constructor places the corresponding bit symbol at the front, giving the claimed translated word for $b::xs$. Finally, translating a singleton list appends the list terminator to the translation of its number, yielding the stated stack word.

**Key facts.** `Turing.bridgeNumber_pos`.
