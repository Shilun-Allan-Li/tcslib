<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.mem_SigmaP_of_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Existential Polynomial Witnesses

**Claim.** For nonzero $i$, if membership in $L$ is equivalent to the existence of a polynomially bounded witness whose paired encoding belongs to a language $L'$ in $\Sigma_i^P$, then $L$ belongs to $\Sigma_i^P$.

**Proof.** 1. Write $i=j+1$ and unpack the given alternating-class representation of $L'$. It has a polynomial-time terminal language $V$ and its own polynomial witness bound. The proof combines the new witness for $L$ with the witnesses used in the representation of $L'$, while converting their lengths to fixed, input-dependent lengths.

2. Let $g_0(x)$ be a unary string whose length is the bound for the witness in the hypothesis, and let $\ell_2(x)$ be the bound for the inner witnesses when the first argument is $\langle x,g_0(x)\rangle$. Polynomial bounds on these lengths follow from the unary-bound closure facts (`Complexity.PolyHierarchy.unaryPT_poly`, together with identity and pairing computability). The proof then sets a single, larger length for the combined witness, namely the sum of the two padded block lengths plus a fixed delimiter allowance. The additivity of unary polynomial bounds (`Complexity.PolyHierarchy.UnaryPT.add`) ensures this combined length is still a permissible polynomial bound.

3. The combined witness is decoded into its two blocks using the polynomial-time splitting and padding-decoding maps. The proof packages these operations, together with the pair encodings, into a polynomial-time map (`Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.pairFstD`, `Complexity.PolyTimeComputable.pairSndD`, and `Complexity.PolyHierarchy.polyTimeComputable_padDecode`). The normal-form theorem for alternating classes (`Complexity.PolyHierarchy.mem_altClass_of_normal`) then shows that the language described by this combined existential block and the remaining $j$ alternating levels belongs to the required class.

4. To verify that this normal form describes exactly $L$, first suppose $x\in L$. Choose the witness $u$ from the hypothesis and then the witnesses from the representation of $L'$. Append a marker bit to each block and pad the combined encoding to the prescribed length. The marker-decoding identity (`Complexity.PolyHierarchy.padDecode_marker`) recovers both original witnesses. The inner witness bound agrees with $\ell_2(x)$ because the chosen outer witness has the required length; the pair-encoding length formula (`Turing.length_pairEncode`) verifies this calculation. The existential successor characterization (`Complexity.altQuant_true_succ`) now gives acceptance by the terminal language.

5. Conversely, a combined witness of the prescribed length can be split and decoded. Its first decoded block has the required length, so it supplies a witness for the hypothesis about $L$. The decoded second block satisfies the inner bound, and the same alternating-class representation of $L'$ then yields membership of the paired input in $L'$. Thus the existence of the combined witness implies $x\in L$, proving the reverse implication and the claimed class membership.

**Key facts.** `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.PolyHierarchy.polyTimeComputable_id`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyHierarchy.polyTimeComputable_padDecode`, `Complexity.PolyHierarchy.unaryPT_const`, `Complexity.PolyHierarchy.UnaryPT.add`, `Complexity.PolyHierarchy.mem_altClass_of_normal`, `Complexity.PolyHierarchy.padDecode_marker`, `Complexity.altQuant_true_succ`, `Turing.length_pairEncode`.
