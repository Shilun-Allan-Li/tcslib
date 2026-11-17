<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrim_machine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machines for Primitive-Recursive String Functions

**Claim.** Every primitive-recursive function from Boolean strings to Boolean strings is computed by a finite Boolean-alphabet Turing machine in a number of steps depending only on the input length.

**Proof.** Encode a Boolean string as a natural number using the primitive-recursive numbering map. Composing the given function with this encoding, and then with the primitive-recursive inverse bridge, yields a primitive-recursive numerical function on the encoded input. The standard code theorem for primitive-recursive functions supplies a program whose evaluation returns the encoded output. Apply the binary machine-bridging result to that program: it produces a finite Turing machine and a time bound depending on input length, with the required computation property. For each string $x$, evaluate the program on the one-element input containing its number encoding; the bridge identity says that decoding this output recovers $x$'s image under the original function. Thus the machine returns exactly $f(x)$ within the asserted length-dependent time.

**Key facts.** `Turing.bridgePrimNumber`, `Turing.bridgePrimUnnumber`, `Turing.bridge_binary`, `Turing.bridgeUnnumber_number`.
