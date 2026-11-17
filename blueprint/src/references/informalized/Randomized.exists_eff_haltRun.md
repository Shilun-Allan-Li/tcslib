<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.exists_eff_haltRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficient Verification of Halting Runs

**Claim.** For a finite nondeterministic machine N and natural numbers A,e, there is an efficient verifier that returns a bit exactly when the run on x with choices r halts with that singleton bit as output, whenever |r|=A(|x|+1)^e.

**Proof.** Construct two polynomial-time languages that recognize the accepting runs of N and of its output-flipped machine. The choice-verifier theorem gives the first language V₁, in P, whose membership on the encoding x appended to r means that N halts and outputs [true] (`Complexity.exists_choiceVerifier_mem_P`). Applying it to the output-flipped machine gives V₀, also in P, for runs that halt and output [false].

Define g on a string z by decoding its paired components and concatenating them. The decoder maps are polynomial-time computable, and their concatenation is polynomial-time computable (`Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.append`). On a pair encoding of x and r, decoding and concatenating recovers x appended to r (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). Therefore the preimages of V₁ and V₀ under g lie in P (`Complexity.preimage_mem_P`); closure of P under complements and intersections also ensures the two output cases can be handled by polynomial-time decision procedures (`Complexity.compl_mem_P`, `Complexity.inter_mem_P`).

The verifier returns true if x appended to r belongs to V₁; otherwise it returns false if it belongs to V₀; if neither test succeeds, it returns undefined. Decoding the pair encoding shows that these tests are precisely membership in the two preimage languages. The halt-run characterization identifies a run with haltRun equal to a singleton precisely when it halts and has that singleton output (`Turing.FinNDTM.haltRun_eq_some_iff`). For the false case, flipping the machine's output maps each halted output list by bitwise negation (`Turing.FinNDTM.haltRun_flipOutput`), so the V₀ test detects exactly the runs outputting [false]. The two cases and the undefined case exhaust the possibilities, proving the required equivalence for either bit.

**Key facts.** `Complexity.exists_choiceVerifier_mem_P`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.append`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.preimage_mem_P`, `Complexity.compl_mem_P`, `Complexity.inter_mem_P`, `Turing.FinNDTM.haltRun_eq_some_iff`, `Turing.FinNDTM.haltRun_flipOutput`.
