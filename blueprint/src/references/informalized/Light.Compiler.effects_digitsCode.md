<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.effects_digitsCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effects of Digit Code

**Claim.** If $c$ differs from the constant-one address and each digit in $L$ is binary, then digit code places the number represented by $L$ in cell $c$ and leaves all other memory cells unchanged.

**Proof.** Induct on the digit list. For the empty list, the code subtracts the contents of $c$ from themselves, so it writes zero there; all other cells remain unchanged. For a list with first digit $d$ and tail $L$, the induction hypothesis gives the value represented by $L$ at $c$, with no other changes. The code doubles that value. Since $d<2$, the digit is either $0$ or $1$. If it is $0$, no further instruction is needed; if it is $1$, the code adds the value at the constant-one address. That address still contains one because it differs from $c$ and the preceding code changed only $c$ (`WordRAM.AgreeOutside.read`). In either case, the result is twice the tail’s value plus $d$, exactly the value represented by the digit list (`Nat.ofDigits_cons`). Every instruction writes only to $c$, so the memory-preservation claim follows by composing the single-cell updates (`WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`).

**Key facts.** `WordRAM.effect_sub`, `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `WordRAM.effects_append`, `WordRAM.effect_add`, `WordRAM.AgreeOutside.read`.
