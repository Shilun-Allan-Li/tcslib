<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5WorkChoice_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Tape Choice

**Claim.** For every finite-state binary Turing machine and binary code for its optional states, the function selecting the work fragment according to its encoded work ordinal is polynomial-time computable.

**Proof.** List the work-fragment functions, one for each tape, evaluated at the quotient of the encoded work index by the number of tapes. The work-index result supplies a polynomial-time unary encoding of that index; division closure therefore gives one for the quotient. Each function in the finite list is polynomial-time computable by the work-fragment result. The selection closure result now makes the indexed choice polynomial-time computable, using the remainder of the work index as its selector. The remainder closure result supplies that selector. Pointwise, when the remainder is a valid tape index, the selected list entry is the corresponding work fragment; when it is not, both the selection convention and the definition return the empty string. Thus the selected function is the required one.

**Key facts.** `Complexity.clA5Indices_native`, `Complexity.clA5Div_native`, `Complexity.clA5WorkFragment_native`, `Complexity.clA5Mod_native`, `Complexity.clA5Select_native`.
