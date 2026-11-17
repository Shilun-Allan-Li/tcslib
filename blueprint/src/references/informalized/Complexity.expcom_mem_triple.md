<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_mem_triple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of Encoded Triples in EXPCOM

**Claim.** An encoding of α, x, and n true bits belongs to EXPCOM exactly when the machine decoded from α halts on x, outputs [true], and uses exactly 2ⁿ steps.

**Proof.** For the forward implication, membership supplies some witness words β and y and some padding length m, together with an equality identifying the input encoding with their nested encoding. Injectivity of pair encoding (pairEncode_injective) first identifies the outer components, and then identifies the inner components. Equality of the replicated true-bit blocks gives n = m by comparing their lengths. Replacing the witnesses by α, x, and n in the supplied machine computation proves the desired condition. Conversely, if that computation holds, choose α, x, and n themselves as the witnesses in the definition of EXPCOM; the required encoding equality is reflexive.

**Key facts.** `Turing.pairEncode_injective`.
