<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.adjoinRoot_mk_binaryMulMod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Binary Modular Multiplication

**Claim.** For positive $\ell$, if the monic binary modulus encoded by $m$ is irreducible, then the residue class encoded by the modular product of $x$ and $y$ equals the product of their residue classes in the quotient by that modulus.

**Proof.** Run the correctness statement for the multiplication state through its final stage $r=\ell$. Its first component says that the quotient class encoded by the accumulator is the class of the encoding of $x$ multiplied by the prefix encoding of $y$ of length $\ell$. The full encoding of a length-$\ell$ vector is exactly this prefix encoding (FABL.binaryAdjoinRootEncode_eq_prefix). Unfolding the final accumulator as the modular product and the encoding as the quotient class of the corresponding low polynomial gives the asserted equality.

**Key facts.** `FABL.binaryMulModState_correct`, `FABL.binaryAdjoinRootEncode_eq_prefix`.
