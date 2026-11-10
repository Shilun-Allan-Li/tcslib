# Approved Pei16 and Wu24 source matches for draft #250

The Gate 15 source is `8b3187bdaf0c634c086313a727a7210dca14bfeb`. The approved matches cover 49
declarations. Three existing LWE foundation attributions carry forward from PR #236.
The Pei16 source uses physical pages 20, 21, 24 and 36–38. The Wu24 source uses
physical pages 85–86. The existing approved excerpts supply the earlier anchors.
The new excerpts cover Pei16 §§5.1–5.2.1 and Wu24 Lecture 21's public-key
construction, bounded-error correctness and security. The changes add scoped
passages to the two existing reference documents.

| Declaration | Source block | Approved scope |
|---|---|---|
| `Encoding.DyadicLinearAlgebra.dotPoly_encodeVector` | P20, P24 | Representation correspondence. The source uses modular products and inner products. Lean checks that the scheduled word loops produce those products on canonical inputs. |
| `Encoding.DyadicLinearAlgebra.matVecPoly_encodeMatrix` | P20, P24 | Representation correspondence. The source uses modular products and inner products. Lean checks that the scheduled word loops produce those products on canonical inputs. |
| `Encoding.DyadicUniform.bitsToResidue` | P24 | Representation adaptation for the uniform residue objects in the LWE experiments. The source supplies the target law. The MSB-first blocks and dyadic restrictions are repository choices. |
| `Encoding.DyadicUniform.bitsToVector` | P24 | Representation adaptation for the uniform residue objects in the LWE experiments. The source supplies the target law. The MSB-first blocks and dyadic restrictions are repository choices. |
| `Encoding.DyadicUniform.bitsToMatrix` | P24 | Representation adaptation for the uniform residue objects in the LWE experiments. The source supplies the target law. The MSB-first blocks and dyadic restrictions are repository choices. |
| `Encryption.PublicKey.Regev.keygen` | P37, W86a | The same common-secret key and binary subset-sum ciphertext formulas, with the sample matrix transposed and noise drawn from an explicit finite law. |
| `Encryption.PublicKey.Regev.encrypt` | P37, W86a | The same common-secret key and binary subset-sum ciphertext formulas, with the sample matrix transposed and noise drawn from an explicit finite law. |
| `Encryption.PublicKey.Regev.decrypt` | P37, W86a | Cancel the secret inner product. The residue is the bit codepoint plus the integer error subset sum. Lean specifies the nearest-codepoint decoder. |
| `Encryption.PublicKey.Regev.encrypt_residual` | P37, W86a | Cancel the secret inner product. The residue is the bit codepoint plus the integer error subset sum. Lean specifies the nearest-codepoint decoder. |
| `Encryption.PublicKey.Regev.subsetError_bound` | P38a, W86a | Extract the deterministic integer subset-sum estimate $mB$ under an entrywise error bound. |
| `LWE.binaryErrorSum_bound` | P38a, W86a | Extract the deterministic integer subset-sum estimate $mB$ under an entrywise error bound. |
| `Encryption.PublicKey.Regev.decrypt_encrypt` | P37, P38a, W86a | The source gives bounded-error correctness. Lean assumes strict $2mB<\lfloor q/2\rfloor$ and proves correctness for every relevant finite seed and subset. |
| `Encryption.PublicKey.Regev.decrypt_keygen_encrypt` | P37, P38a, W86a | The source gives bounded-error correctness. Lean assumes strict $2mB<\lfloor q/2\rfloor$ and proves correctness for every relevant finite seed and subset. |
| `Encryption.PublicKey.Regev.view` | P38b, W86b | The fixed-bit passive view and the exact first-hybrid simulation. Lean compares finite advantages and threads independent subset and test coins. |
| `Encryption.PublicKey.Regev.realView` | P38b, W86b | The fixed-bit passive view and the exact first-hybrid simulation. Lean compares finite advantages and threads independent subset and test coins. |
| `Encryption.PublicKey.Regev.uniformKeyView` | P38b, W86b | The fixed-bit passive view and the exact first-hybrid simulation. Lean compares finite advantages and threads independent subset and test coins. |
| `Encryption.PublicKey.Regev.reduction` | P38b, W86b | The fixed-bit passive view and the exact first-hybrid simulation. Lean compares finite advantages and threads independent subset and test coins. |
| `Encryption.PublicKey.Regev.real_uniformKey_advantage` | P38b, W86b | The fixed-bit passive view and the exact first-hybrid simulation. Lean compares finite advantages and threads independent subset and test coins. |
| `Encryption.PublicKey.Regev.hashParameters` | P37, P38c, W86b | The augmented key has $n+1$ output coordinates and $m$ input bits. Lean reuses its binary matrix hash and expresses the ciphertext as the hash plus a last-coordinate shift. |
| `Encryption.PublicKey.Regev.augmented` | P37, P38c, W86b | The augmented key has $n+1$ output coordinates and $m$ input bits. Lean reuses its binary matrix hash and expresses the ciphertext as the hash plus a last-coordinate shift. |
| `Encryption.PublicKey.Regev.encrypt_augmented` | P37, P38c, W86b | The augmented key has $n+1$ output coordinates and $m$ input bits. Lean reuses its binary matrix hash and expresses the ciphertext as the hash plus a last-coordinate shift. |
| `Encryption.PublicKey.Regev.extractionError` | P38c, W86b | Finite strong leftover-hash specialization with an explicit error. The ideal key and ciphertext are independent, and fixed translation preserves the ideal. |
| `Encryption.PublicKey.Regev.uniformKey_uniform_advantage_le` | P38c, W86b | Finite strong leftover-hash specialization with an explicit error. The ideal key and ciphertext are independent, and fixed translation preserves the ideal. |
| `Encryption.PublicKey.Regev.distAdv_encrypt_le` | P38b, P38c, W86b | Quantify the two-bit hybrid comparison by two decision-LWE terms and two extraction terms. The explicit width and security slack are repository bounds. |
| `Encryption.PublicKey.Regev.two_extractionError_le` | P38b, P38c, W86b | Quantify the two-bit hybrid comparison by two decision-LWE terms and two extraction terms. The explicit width and security slack are repository bounds. |
| `Hashing.SIS.collisionAt` | P21, P36 | The collision-to-SIS argument and its asymptotic consequence under the corresponding independent SIS assumption. The raw padded machine domain, uniform coin transport and dyadic profile are disclosed Lean adaptations. |
| `Hashing.SIS.negligible_collisions_of_SIS` | P21, P36 | The collision-to-SIS argument and its asymptotic consequence under the corresponding independent SIS assumption. The raw padded machine domain, uniform coin transport and dyadic profile are disclosed Lean adaptations. |
| `Hashing.SIS.dyadic_collision_negligible` | P21, P36 | The collision-to-SIS argument and its asymptotic consequence under the corresponding independent SIS assumption. The raw padded machine domain, uniform coin transport and dyadic profile are disclosed Lean adaptations. |
| `Hashing.SIS.rawCollisionProbability_le_successProbability` | P20, P21 | Use the binary matrix map and signed collision difference. Lean proves the raw word implementation and a same-coin finite comparison to its decoded SIS witness. |
| `Hashing.SIS.hashPoly_encodeMatrix` | P20, P21 | Use the binary matrix map and signed collision difference. Lean proves the raw word implementation and a same-coin finite comparison to its decoded SIS witness. |
| `Hashing.SIS.hash_difference_probability` | P38c | Support the regularity argument by showing the difference of distinct binary hashes is uniform. The exact finite collision count and use of a unit coefficient for every allowed modulus are Lean subclaims. |
| `Hashing.SIS.isUniversal_hash` | P38c | Support the regularity argument by showing the difference of distinct binary hashes is uniform. The exact finite collision count and use of a unit coefficient for every allowed modulus are Lean subclaims. |
| `Hashing.SIS.strong_leftover_hash` | P38c | The seed-published matrix product uses the leftover hash lemma. Lean gives an explicit finite error, a bound for randomized tests, and sufficient entropy slack. |
| `Hashing.SIS.distAdv_hash_uniform_le` | P38c | The seed-published matrix product uses the leftover hash lemma. Lean gives an explicit finite error, a bound for randomized tests, and sufficient entropy slack. |
| `Hashing.SIS.leftover_error_le` | P38c | The seed-published matrix product uses the leftover hash lemma. Lean gives an explicit finite error, a bound for randomized tests, and sufficient entropy slack. |
| `LWE.bitNoise` | P24 | The source specifies an integer-valued error law. Lean instantiates that slot with a finite sampler, keeps preimage multiplicities, and gives a local centered bit-difference profile. |
| `LWE.bitNoise_probability` | P24 | The source specifies an integer-valued error law. Lean instantiates that slot with a finite sampler, keeps preimage multiplicities, and gives a local centered bit-difference profile. |
| `LWE.centeredValue` | P24 | The source specifies an integer-valued error law. Lean instantiates that slot with a finite sampler, keeps preimage multiplicities, and gives a local centered bit-difference profile. |
| `LWE.sampleFromBits` | P24 | The real common-secret batch and uniform comparison are encoded using disjoint full-width bits. Lean supplies the exact dyadic representation and finite noise seeds. |
| `LWE.uniformFromBits` | P24 | The real common-secret batch and uniform comparison are encoded using disjoint full-width bits. Lean supplies the exact dyadic representation and finite noise seeds. |
| `Pseudorandom.Generators.LWE.generate` | P24 | Reuse the common-secret sample map as a generator. The exact finite advantage identity and encoded adversary consequence use the repository's fixed-sample DLWE formulation. |
| `Pseudorandom.Generators.LWE.prgAdv_generate` | P24 | Reuse the common-secret sample map as a generator. The exact finite advantage identity and encoded adversary consequence use the repository's fixed-sample DLWE formulation. |
| `Pseudorandom.Generators.LWE.pseudorandom_under_DLWE` | P24 | Reuse the common-secret sample map as a generator. The exact finite advantage identity and encoded adversary consequence use the repository's fixed-sample DLWE formulation. |
| `Pseudorandom.Generators.LWE.seedBitLength` | P24 | Count the bits for the public matrix, one secret, and the independent error seeds in the encoded common-secret experiment. |
| `Pseudorandom.Generators.LWE.seed_cardinality` | P24 | Count the bits for the public matrix, one secret, and the independent error seeds in the encoded common-secret experiment. |
| `Pseudorandom.Generators.LWE.generateBits` | P24 | Pack and unpack the same common-secret sample experiment without changing its noise law. The source supplies the real and ideal experiments. The exact word equivalence and advantage transport are Lean representation results. |
| `Pseudorandom.Generators.LWE.generateBits_advantage` | P24 | Pack and unpack the same common-secret sample experiment without changing its noise law. The source supplies the real and ideal experiments. The exact word equivalence and advantage transport are Lean representation results. |
| `Pseudorandom.Generators.LWE.flatSeedEquiv` | P24 | Pack and unpack the same common-secret sample experiment without changing its noise law. The source supplies the real and ideal experiments. The exact word equivalence and advantage transport are Lean representation results. |
| `Pseudorandom.Generators.LWE.generateFlat` | P24 | Pack and unpack the same common-secret sample experiment without changing its noise law. The source supplies the real and ideal experiments. The exact word equivalence and advantage transport are Lean representation results. |

The block identifiers and exact declaration paths are in the matching record.
The registry already contains both references. The approval covers the 49
attributions and the exact two-file excerpt diff.
