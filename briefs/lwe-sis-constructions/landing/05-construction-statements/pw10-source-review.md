# Approved PW10 source matches for draft #250

I reviewed the rendered author PDF on physical and printed pages 33–39.
The PDF and all seven page fingerprints match the pinned manifest. The five
Lean modules containing these declarations are byte-identical between the
recovered candidate census at `713093c36ac66f7e56e9354581f0bb3f59772341`
and the Gate 15 source at `8b3187bdaf0c634c086313a727a7210dca14bfeb`.

The approval covers 35 attributions from the 60-declaration census. Thirty
already have PW10 docstring tags and five are extracted consequences or
supporting adaptations. The other 25 entries remain Lean implementation
and reader context. The block labels expand to the stable PDF anchors in the scoped reference. Lean
names are relative to `TCSlib.Cryptography.TrapdoorFunctions`.
[Scoped reference](../../../../blueprint/src/references/peikert-waters-2010-lossy-tdf.md)

The review records two source slips. The p. 33 sampling bullet gives the
secret the public matrix's row count, while the dimensions of the product
and the proof on p. 34 require the number of concealed columns. The p. 35
gadget row formula gives the block count as the range for the inner index.
The tensor shape and the length of the powers column give the block width.
At p. 39, the signed lift uses the decoded integer branch product.

| Lean declaration | PDF blocks | Approved correspondence |
|---|---|---|
| `Lossy.conceal` | 33.1, 34.1 | The concealed block is the public matrix times the transposed secret plus the modular image of the integer error. The secret has one row per concealed column. |
| `Lossy.concealedSampler` | 33.1, 34.1 | The public pair uses one common public matrix, independent secret rows and independent error seeds. Lean gives the public projection of the sampler using its finite noise law. |
| `Lossy.columnHybrid` | 34.1 | The first $k$ columns are real and the remainder uniform, with $k=0$ the uniform endpoint. The public matrix is common to all columns. |
| `Lossy.columnTest` | 34.1 | Insert a common-secret $h$-sample challenge as zero-based column $k$, with earlier real and later uniform columns. Lean threads the test's finite coin type through the experiment. |
| `Lossy.concealed_advantage_le` | 33.1, 34.1 | Quantify the adjacent-hybrid proof as a sum of fixed-sample DLWE advantages for a finite test. |
| `Lossy.shiftedSampler` | 36.2, 38.2, 39.2 | Translate the second block by a fixed matrix. The gadget, zero shift and negative designated-branch shift are the source's key-mode instances. |
| `Lossy.shifted_advantage_le` | 34.1, 37.1, 39.2 | Uniform translation gives a common ideal. Lean compares two arbitrary fixed shifts by one finite column-hybrid sum per shift. |
| `Lossy.encode` | 36.1 | With $p=2^b$ and $q=p2^a$, the source's rounded scaling is exact multiplication by $2^a$. |
| `Lossy.decode` | 36.1 | Nearest-scale decoding uses the canonical representative, a half-scale offset, and quotient reduction modulo $p$. The implementation fixes the tie convention. |
| `Lossy.encode_intCast` | 36.1 | Exact-divisibility refinement. Changing an integer representative by $p$ changes its scaled image by $q$, including for signed representatives. |
| `Lossy.decode_encode_add` | 34.2, 36.1, 37.1 | Replace the probabilistic noise and encoding-rounding estimates with exact divisibility and the deterministic premise $a>0,\ 2\lvert e\rvert<2^a$. |
| `Lossy.gadget` | 35.1 | Each binary block contributes its powers of two in its own column. Lean uses the same row shape with a transpose action on column inputs. |
| `Lossy.digits` | 35.1, 36.3 | The finite block equivalence reads the little-endian positional integer in $[0,p-1]$. This is the digit map unpacked in the source inversion. |
| `Lossy.gadget_mulVec` | 35.1, 36.3 | Extract the coordinate identity $G^\mathsf{T}x=\operatorname{digits}(x)$ over the integers. |
| `Lossy.injectiveKey` | 36.2 | Add the exact dyadic encoding of the gadget to the concealed block. The Lean function takes the finite key ingredients as inputs. |
| `Lossy.evaluate` | 36.2 | Read the two blocks of the row product $xY$ as a pair of transpose actions on the binary input. |
| `Lossy.residual` | 36.3 | Cancel the secret product by subtracting $Tz_1$ from the second output coordinate vector. |
| `Lossy.recover` | 36.1, 36.3 | Decode the residual and unpack its positional representatives through the finite block equivalence. This is the finite recovery map. |
| `Lossy.residual_conceal` | 36.2, 36.3, 37.2 | Extract the lossy-mode cancellation identity. The resulting residue is the cast of the signed error subset sum. |
| `Lossy.residual_injectiveKey` | 36.2, 36.3, 37.1 | The injective residual is the scaled digit plus the signed error sum. Exact scaling allows the gadget sum inside the encoder. |
| `Lossy.recover_evaluate` | 34.2, 36.3, 37.1 | The source proves recovery with overwhelming probability over errors. Lean proves recovery on every binary input for a fixed key with entrywise bound $B$, $a>0$, and $2wbB<2^a$. |
| `Lossy.evaluate_injective` | 36.3, 37.1 | Extract injectivity from the same deterministic left inverse on the finite domain. |
| `Lossy.lossy_range_card` | 37.2 | Count the first output and the bounded integer error vector. The interval $[-NB,NB]$ gives the deterministic image bound $q^d(2NB+1)^w$. |
| `Lossy.lossy_bits` | 37.2 | Express residual leakage as an image-size inequality after multiplication by $2^k$. Lean assumes the separate numerical budget $q^d(2NB+1)^w2^k\le 2^N$. |
| `AllButOne.antiCyclic` | 38.1 | Each row is a signed wrapped shift of the integer coefficient vector. |
| `AllButOne.antiCyclic_mulVec_injective` | 38.1 | Use the cyclotomic power-basis argument for a nonzero integer coefficient vector. Lean concludes injectivity of the transpose action and also covers width one. |
| `AllButOne.branch_difference_injective` | 38.1, 39.1 | Apply full rank to the nonzero integer difference of two distinct binary branches. |
| `AllButOne.branch_message_bound` | 38.1, 39.1, 39.3 | The dot product has $w$ terms of magnitude at most $p-1$, giving $w(p-1)$ for each coordinate of the signed integer product of the packed digits. |
| `AllButOne.branchGadget` | 35.1, 38.2 | Multiplying the binary gadget by the anti-cyclic matrix gives the expanded branch matrix, with each branch coefficient weighted by its block power of two. |
| `AllButOne.allButOneKey` | 38.2 | Subtract the encoded designated-branch gadget. Lean uses $p'=2pw$ and $q=2^a p'$ on supplied finite key ingredients. |
| `AllButOne.evaluateBranch` | 39.1 | Add the queried branch's encoded shift and use the two-block evaluator. |
| `AllButOne.evaluate_lossy_branch` | 39.1 | Extract the exact cancellation when the queried and designated branches agree. |
| `AllButOne.residual_branch` | 39.3 | After cancelling the secret product, exact dyadic scaling turns the difference of encoded shifts into the encoding of the signed branch product. The original integer error sum remains. |
| `AllButOne.evaluateBranch_injective` | 38.1, 39.1, 39.3 | The source uses rounding, signed lifting and a full-rank solve. Lean uses deterministic separation $a>0,\ 2(2^u b B)<2^a$, the signed lift and integer rank to prove finite injectivity. |
| `AllButOne.lossy_branch_range_card` | 37.2, 39.1, 39.4 | At the designated branch the shifts cancel. Apply the finite concealed-map count $q^d(2NB+1)^w$ at the enlarged dyadic modulus. |

The registry addition attaches this scoped reference under
`PW10`. The approval covers attribution and the registry entry. Efficient
trapdoor recovery, family-level security and the CPA and CCA2 bridges have
separate obligations.
