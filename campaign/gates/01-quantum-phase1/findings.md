This report audits the definitions, theorem statements and remaining admissions in TCSlib's quantum phase 1 statement gate at commit `d2d72d18ed5b5845ff25ae028490ee45600ae38f` on `quantum/p1-basic`. It records **0 blockers, 2 majors, 6 minors and 3 notes**. I found no counterexample to a literal Lean theorem among the 72 directly admitted statements; the majors concern the scope of no-cloning and a false claim about raw quantum gate entries being GapP functions. **Resolve the major findings before closing this gate.** This is not a blanket approval.

The report contains a restatement and source comparison for all **63 definition-like declarations** (including structures, abbreviations and the anonymous decidability instance), a separate **2–5 sentence argument for every one of the 72 directly sorried theorems**, **21 adversarial cases**, and answers to **all 13 questions**. It also inventories the other theorem statements and checks the supplied evidence and duplication ledger.

The first-pass restatements were recorded from comment-stripped source before reading the corresponding docstrings. The comparison column was added only afterward; where the first reading left a convention open, the comparison records its resolution. Tactic proofs were not reviewed. The four received foundation files were read to interpret the new declarations, not re-audited.

# Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
| - | - | - | - | - | - |
| 1 | major | TCSlib/Quantum/Basic/Protocols.lean · no_cloning (67); Divergences (38–39) | The theorem is true but its unrestricted exact-vector specification admits a phase-only trivialization; presenting it as the same standard physical no-cloning statement is materially misleading. | For any normalized ψ, linearity sends −ψ⊗e to the negative of the output for ψ⊗e, whereas (−ψ)⊗(−ψ)=ψ⊗ψ. This already forbids the specified map in dimension one, where the unique physical pure state can certainly be cloned. | Add a companion forbidding cloning up to an input-dependent unit-modulus scalar, preferably the two-state version with overlap modulus strictly between 0 and 1. Alternatively rename and document this as only an exact-vector corollary, and remove the claim that its strength is the same. |
| 2 | major | TCSlib/Complexity/Counting/GapP.lean · module introduction (18–19) | The statement that each quantum gate entry is a gap function is false for the gates defined in this very bundle. | IsGapP is integer-valued. H has entry 1/√2 and S has entry i; neither is an integer. Acceptance also involves squared amplitude moduli, or a channel representation, rather than an unqualified amplitude sum. | Describe GapP integer numerator functions after the chosen scaling and real/imaginary or channel encoding. State the denominator explicitly in the later construction; revise this explanation now so downstream work cannot use the false raw-entry claim. |
| 3 | minor | TCSlib/Quantum/Basic/Protocols.lean · denseCode (178), superdenseState (187), Divergences | The superdense message labels differ from the cited Nielsen–Chuang §2.3 without an explicit deviation notice. | NC sends 01 with Z and 10 with X; denseCode sends 01 with X and 10 with Z. At 11, XZ=−iY also differs from NC's iY by a global sign. The library's own decoder correctly outputs its own labels. | Document the bit-label interchange and harmless phase. Keep the current code and probability theorem, which are internally consistent. |
| 4 | minor | TCSlib/Quantum/Basic/ApplyOn.lean · applyOn_commute_of_disjoint proof sketch (138–142) | The final sentence gives the wrong intermediate assignment for one multiplication order and purports to use it for both. | For A1A2, z equals x on w1 and y on w2. With X on wire 0, X on wire 1, x=00 and y=11, the intermediate is 01; the reversed product uses 10. | Correct the explanatory sketch to distinguish the two intermediate labels. The formal commutation statement needs no change. |
| 5 | minor | TCSlib/Complexity/Counting/GapP.lean · coinFill docstring (169–171) | The prose states the acceptance formula without its necessary random-string length condition and omits the default on a missing next bit. | With M always none, p=0 and zero random bits, coinFill returns false and accepts with probability 0, whereas the unqualified prose formula gives 1/2. randProb_coinFill correctly assumes p(\|x\|)+1 ≤ m. | State the fresh-bit length condition in the docstring and mention the false default on short lists. Keep the definition and theorem unchanged. |
| 6 | minor | Audit pack · Suggested adversarial instantiations | The request to confirm all six closure hypotheses for Eff ≡ False is itself incorrect. | The five preservation implications are vacuous, but HasConstVerifiers requires efficient constVerifier true and false, which is impossible when Eff is False. | Change the expected result: five closure implications hold, HasConstVerifiers fails, and no PP or GapP witness exists. No Lean theorem needs changing. |
| 7 | minor | Audit pack · measured inventory and style attestations; campaign_style_lint.log | The campaign-style log covers 11 files, and the declaration count omits an anonymous public instance. | The log totals 6+1+4 files, omitting Quantum.lean, Complexity/Promise.lean and Complexity/Counting.lean. The source has 193 named declarations plus ApplyOn.lean:69's Decidable instance, for 194 explicit declarations; the axiom log does include the generated instance name. | Report campaign-style coverage as 11 or rerun it on all 14. Label 193 as the named-declaration count or include the instance; retain the separate 14-file ordinary style-lint result. |
| 8 | minor | TCSlib/Complexity/Counting/PP.lean · InPP (55), module source comparison | The cited Arora–Barak convention includes ties on the yes side, unlike the present strict threshold; this equivalent convention change is not recorded. | AB09 Definition 17.6, p.345, uses accepting count ≥ half the seeds. InPP and Watrous use > half. A verifier accepting exactly half its seeds therefore has different membership predicates under the two raw definitions. | Cite AB09 Definition 17.6 precisely and record the tie convention. Explain the equivalence at polyTimeModel by shifting an integer gap by one; do not claim the same verifier or arbitrary-model equivalence. |
| 9 | note | Register, Gates, ApplyOn and Protocols · 19 definitions inheriting sorryAx | The inherited sorry dependencies are through well-formedness proofs, not through selection of amplitudes or matrix entries. | The definitions explicitly provide their vectors and matrices; wrappers, coercions, group operations and relabellings expose those data. The 19-dependent-definition count is consistent with the supplied axiom census. | Accept this only as a statement skeleton, conditional on the normalization and unitarity lemmas being filled later. No need to force those proofs before the statement review closes solely to clean the axiom display. |
| 10 | note | TCSlib/Complexity/Counting/GapP.lean · IsGapP | The abstention model has the intended mathematical GapP meaning at polyTimeModel, but that bridge is not yet a formal theorem. | Accepting and rejecting seed counts give two #P functions; conversely canonical nondeterministic path transcripts plus unique false padding preserve counts, and abstentions can be replaced by cancelling accept/reject branches. | Add a bridge to a named difference-of-#P-counts predicate when that predicate is available. The absence of this bridge does not falsify a current statement. |
| 11 | note | Duplication ledger; plan FD-1, FD-2, OQ-1 and OQ-6 | No additional unacknowledged wholesale duplication was found in the audited surface; the disclosed overlap remains real. | The checked Physlib files overlap with the Ket design and gate facts. The plan's 2026-11-06 owner-approved decision explicitly accepts this temporary overlap and deletes it on adopting Physlib; the existing QuantumHamming X/Z definitions are also recorded. | Retain the existing acknowledgment and scheduled dependency-switch resolution. No new human acknowledgment is requested here; a namespace collision screen alone should not be presented as a complete semantic duplication check. |

# Scope and source checks

All fourteen audited Lean sections in the bundle were compared with the corresponding files fetched at the exact commit above; their source contents matched. The manifest pins Mathlib to `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` with Lean 4.25.0. The source-content comparison is not a new elaboration run.

The supplied logs report all fourteen modules elaborating and give a consistent census of 228 constants: 119 without sorryAx, 90 theorem constants with sorryAx, and 19 data definitions with sorryAx. Of those 90 theorem constants, 72 are direct admissions and 18 are definitional equations with transitive dependencies. The source inventory independently accounts for those 72 admissions. These elaboration and axiom claims remain the maintainer's supplied execution evidence; this audit did not rerun Lean at the pinned toolchain.

Independent finite checks were executed in JavaScript: 13,608 exhaustive small counting assertions, all successful, plus boundary and quantum matrix checks. Integer counting and the tested dyadic probabilities were exact; quantum complex arithmetic used tolerance 10⁻¹². These checks support the mathematical arguments below and do not replace proofs or test Lean casts and elaboration.

Source abbreviations in the comparisons:

- **Wat**: the attached Watrous PDF, arXiv:0804.3401 v1. Checked §II.1 (pp.3–4), §III.2/Figs.3–4 (pp.8–9), and §IV.5 (pp.16–17). [Attached text](https://chatgpt.com/library?file_id=libfile_fde3_f-ea97dc9594108191bcbe2f6bd4783d57_26dc31675afc8191a7391c098a3c0f7c\&account_id=personal).

- **dW**: the attached de Wolf PDF, arXiv:1907.09415 v6, dated August 27, 2026. Checked §§1.2–1.5 (printed pp.3–11; PDF pp.15–23), §2.1.2 (printed pp.14–15), and App. A, particularly the inner-product, unitary and tensor sections. [Attached text](https://chatgpt.com/library?file_id=libfile_fde3_f-5924ae8cbe4c8191abac1b85bfcc5e97_26dc31675afc8191a7391c098a3c0f7c\&account_id=personal).

- **NC**: Nielsen–Chuang, 10th anniversary edition, §2.3, pp.97–98, checked in a [textual reproduction of the book](https://studylib.net/doc/27523452/michael-a.-nielsen--isaac-l.-chuang---quantum-computation...). Box 12.1's two-state argument was also checked in an [earlier-edition reproduction](https://djvu.online/file/KwUJCWp0156wY); edition-specific identity of that box was not independently verified. The phase objection in finding 1 is an independent mathematical calculation.

- **FR**: Fortnow–Rogers, [author-hosted paper](https://lance.fortnow.com/papers/files/quantum.pdf), §2.4, Theorem 2.2 and Definition 2.3. Its strict negative no-side normal form is compatible with the integer-gap shifts described below.

- **AB**: Arora–Barak, [2009 book reproduction](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press\(2009\).pdf), Definitions 2.1, 7.3 and 17.6. Definition 17.6's non-strict threshold was also checked in the page image.

- **WZ**: Wootters–Zurek, [original article reproduction](https://painterlab.caltech.edu/wp-content/uploads/2019/06/qe_wotters_no_cloning.pdf), pp.802–803. Its apparatus-inclusive discussion is broader than the present two-register exact-vector theorem.

- **Physlib**: the two source files named in the plan, at commit `cdfa6094901b8956a378151f64088bcf5a5f8bcb`; the Ket design, phase conventions and gate overlap were compared. Mathlib's `finTwoEquiv` was checked at the manifest pin.

Statements about textbook equivalence are mathematical comparisons. They are not claims that a Lean theorem connecting the formal library to an external machine model has already been proved.

# Audited inventory

| File | Lines | Named declarations | Direct admissions |
| - | - | - | - |
| [TCSlib/Quantum.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum.lean) | 24 | 0 | 0 |
| [TCSlib/Quantum/Basic.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic.lean) | 31 | 0 | 0 |
| [TCSlib/Quantum/Basic/Register.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Register.lean) | 231 | 24 | 8 |
| [TCSlib/Quantum/Basic/Gates.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Gates.lean) | 308 | 45 | 12 |
| [TCSlib/Quantum/Basic/ApplyOn.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/ApplyOn.lean) | 194 | 17 | 9 |
| [TCSlib/Quantum/Basic/Measure.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Measure.lean) | 120 | 11 | 6 |
| [TCSlib/Quantum/Basic/Protocols.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Protocols.lean) | 208 | 22 | 7 |
| [TCSlib/Complexity/Promise.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Promise.lean) | 23 | 0 | 0 |
| [TCSlib/Complexity/Promise/Basic.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Promise/Basic.lean) | 146 | 13 | 3 |
| [TCSlib/Complexity/Counting.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting.lean) | 32 | 0 | 0 |
| [TCSlib/Complexity/Counting/PP.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/PP.lean) | 111 | 6 | 2 |
| [TCSlib/Complexity/Counting/GapP.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/GapP.lean) | 363 | 41 | 13 |
| [TCSlib/Complexity/Counting/PolyTime.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/PolyTime.lean) | 141 | 10 | 8 |
| [TCSlib/Complexity/Counting/Inclusions.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/Inclusions.lean) | 85 | 4 | 4 |

There are 193 named declarations: 57 definitions, 3 abbreviations, 2 structures and 131 theorems. Adding the anonymous `Decidable (AgreeOff …)` instance gives **194 explicit declarations**. The four facade files introduce no definitions or theorems; their imports cover the scoped content. `TCSlib.lean` exports the three new facade imports, as the pack states.

# Per definition restatements and source comparison

The restatement column preserves the independent first reading. Each row is followed by a comparison with its docstring and the relevant cited source; purely representational helpers are identified as such rather than attributed to a textbook definition.

## Register

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Register.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D01: `Qubit` (line 67) | A classical computational-basis label with exactly two values, represented by Fin 2. | Matches the computational labels 0 and 1 in dW §1.2.1 and Physlib Qubit. The name denotes a basis label, not a two-dimensional state vector; the docstring makes that distinction. |
| D02: `Reg` (line 70) | An n-bit basis label is a function from the n wire positions to Fin 2; at n=0 there is one label. | Matches the n-bit computational basis in dW §1.3. A function representation fixes wire positions without a numerical endianness convention. The empty register is one-dimensional, not an empty Hilbert space. |
| D03: `qubitEquivBool` (line 79) | The named Mathlib equivalence finTwoEquiv between the two Fin labels and Booleans; its precise false/true orientation must be checked in Mathlib. | Mathlib at the manifest pin sends 0 to false and 1 to true. This resolves the orientation left open in the first reading; the docstring and intended Boolean bridge agree. |
| D04: `basisOf` (line 86) | Convert a Boolean label at each wire using the inverse of qubitEquivBool. | Matches conversion of a classical bit string to its basis label (dW §1.3). With the checked equivalence, false maps to 0 and true to 1; no reversal is hidden in the inverse. |
| D05: `regAppendEquiv` (line 97) | Identify a pair of k- and m-wire labels with one (k+m)-wire label by the Fin-sum equivalence; the k-wire label occupies the left summand. | Matches concatenation of tensor factors, dW §2.1.2 and App. A.6: the first k positions read the first component and the last m read the second. The inverse used for relabelling is consequently essential. |
| D06: `Ket` (line 164) | A complex amplitude function on a finite basis with sum of squared absolute values equal to one; states retain global phase. | Matches normalized ket representatives in dW §1.2.1 and the checked Physlib fields. It does not identify global phases (dW §1.2.2); this is suitable for amplitudes but matters for no_cloning (finding 1). Over an empty basis there are no such kets. |
| D07: `Ket.basis` (line 175) | The normalized delta vector at the chosen basis index. | Matches the computational basis states of dW §1.2.1. Supplying an index already ensures a nonempty basis, so no additional Nonempty assumption is missing. |
| D08: `Ket.relabel` (line 185) | Pull amplitudes back along an equivalence from the new basis to the old basis. | Matches Physlib's pullback direction and ordinary change of index. An equivalence from new labels to old labels is required; this is relabelling, not application of the forward permutation matrix. |
| D09: `Ket.prod` (line 195) | The product-index amplitude at (i,j) is the product of the two amplitudes. | Matches the tensor entries in dW App. A.6. It constructs product states only, without claiming all states on a product basis factor; entangled kets remain representable by Ket. |
| D10: `Ket.evolve` (line 205) | Multiply the amplitude column by the supplied unitary matrix. | Matches column-vector evolution in dW §1.2.3. Matrix multiplication means the rightmost factor acts first; explicit unitary membership is the needed norm-preservation hypothesis. |

## Gates

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Gates.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D11: `permMat` (line 79) | Column x has its single one in row sigma(x), with zeros elsewhere. | Matches the linear extension of a reversible basis permutation, dW §1.4. Its row/output and column/input convention is forward, not inverse; the docstring agrees. |
| D12: `Gate` (line 111) | The group of complex unitary matrices on n-bit labels, with matrix multiplication. | Matches finite-dimensional unitary gates, dW §1.2.3. Arbitrary unitary matrices are allowed here; no claim of uniformity or efficient circuit synthesis is built into this type. |
| D13: `Gate.ofPerm` (line 118) | Bundle the forward permutation matrix as a unitary. | Matches the reversible-gate specialization of the preceding matrix. Its data is permMat even though its unitarity proof is sorried; no proof is used to select a matrix. |
| D14: `Gate.ofPhase` (line 125) | Bundle a diagonal matrix whose diagonal entries have complex modulus one. | Matches a diagonal phase operation, dW §1.4 and App. A.4. The explicit modulus-one hypothesis is exactly sufficient; a vanishing phase cannot be bundled. |
| D15: `flipAt` (line 137) | Change only coordinate i, adding one in Fin 2. | Matches the bit-flip action of X in dW §1.4. Fin 2 addition wraps modulo two, and all other coordinates are preserved. |
| D16: `cnotMap` (line 151) | Preserve coordinate 0 and add it modulo two into coordinate 1. | Matches CNOT in dW §1.4, first wire control and second target. This convention agrees with teleportation. |
| D17: `toffoliMap` (line 164) | Preserve coordinates 0 and 1 and add their product modulo two into coordinate 2. | Matches Watrous §III.2 Fig. 3 after the declared wire naming: the last bit flips iff both first bits are 1. No distinctness premise is needed for the three fixed positions. |
| D18: `hadamardMat` (line 179) | A two-by-two matrix with entry 1/sqrt(2) except for row 1, column 1, whose entry is negative. | Matches the displayed H matrix in dW §1.4 and Watrous Fig. 3. The exponent's Fin 2 multiplication is 1 exactly when both bits are 1, so using its natural-number value causes no sign error. |
| D19: `zPhase` (line 194) | Assign phase +1 to the zero label and -1 to the one label. | Matches the diagonal entries of Z in dW §1.4. The phase function is indexed by a one-wire register rather than Fin 2 directly. |
| D20: `sPhase` (line 206) | Assign phase +1 to the zero label and i to the one label. | Matches Watrous's phase gate P and dW's Rφ at φ = π/2. The name S is an explicitly disclosed convention. |
| D21: `Gate.H` (line 222) | Bundle hadamardMat as a one-wire unitary. | Matches H in dW §1.4 and Watrous §III.2, including its positive normalization factor. |
| D22: `Gate.X` (line 228) | The permutation unitary that flips the sole bit. | Matches X in dW §1.4, through the Reg 1 versus Fin 2 identification. This is the disclosed overlap with QuantumHamming.sigmaX. |
| D23: `Gate.Z` (line 236) | The diagonal one-wire unitary with entries 1,-1. | Matches Z in dW §1.4. This is the disclosed overlap with QuantumHamming.sigmaZ, not a new independent Pauli convention. |
| D24: `Gate.S` (line 242) | The diagonal one-wire unitary with entries 1,i. | Matches Watrous P = diag(1,i), called S here. S is not its inverse. |
| D25: `Gate.CNOT` (line 248) | The permutation unitary with control wire 0 and target wire 1. | Matches the control-0, target-1 CNOT in dW §1.4. Its permutation is an involution, so the inverse used to construct the equivalence does not reverse the gate. |
| D26: `Gate.Toffoli` (line 256) | The permutation unitary with controls 0,1 and target 2. | Matches the controls-0,1, target-2 Toffoli of Watrous §III.2. The specified map is its own inverse. |

## ApplyOn

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/ApplyOn.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D27: `AgreeOff` (line 62) | The input and output labels agree at every wire outside the embedding's image. | An implementation predicate with no separate textbook definition. It expresses exactly the identity factors in the tensor placement of dW §2.1.2; outside the image, output equals input. |
| D28: `Decidable AgreeOff` (line 69) | A decision procedure for that finite universal equality predicate. | An implementation instance, not a mathematical source claim. The predicate ranges over finite wires and decidable equalities, so it is decidable; there is no additional semantic assumption. |
| D29: `applyOn` (line 75) | Use the local matrix entry at the restricted output/input labels if all untouched wires agree, and zero otherwise. | Equivalent to tensoring with the identity and reordering factors, dW §2.1.2/App. A.6. Injectivity prevents repeated-wire aliasing. At k=0 it multiplies the global identity by the sole local matrix entry. |
| D30: `applyOnU` (line 121) | Bundle applyOn applied to a unitary gate, asserting the extended matrix is unitary. | The same placement restricted to unitary inputs, matching local unitary evolution. The bundled proof adds no change to the explicit matrix. |
| D31: `wire` (line 178) | Embed the only position in Fin 1 into the chosen global wire i. | A representation helper for placing a one-qubit gate, as in dW §1.4. A map out of Fin 1 is injective; its supplied i : Fin n excludes n=0 automatically. |

## Measure

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Measure.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D32: `Ket.prob` (line 50) | The squared modulus of the selected amplitude, as a real number. | Exactly the computational-basis Born probability of dW §1.2.2. The modulus is squared as a real number; amplitude phase is discarded. |
| D33: `Ket.probQubit` (line 73) | Sum squared moduli over all basis labels with the selected bit value at wire i. | Exactly the projective Born marginal of dW §1.2.2 and §1.3. It sums probabilities, not amplitudes, and does not assume the wire is unentangled. |

## Protocols

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Quantum/Basic/Protocols.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D34: `bellVec` (line 75) | Amplitude 1/sqrt(2) on 00 and 11, and zero on 01 and 10. | Matches the EPR vector in dW §1.5. Equality of the two bit values selects precisely 00 and 11, with the same positive amplitude. |
| D35: `bell` (line 89) | Package bellVec as a normalized two-wire ket. | The normalized EPR ket of dW §1.5. It is entangled even though its type is the same Ket type used for product states. |
| D36: `wires01` (line 97) | Embed the two local positions into the first two positions of a three-wire register. | A wire-index helper for Alice's two wires in dW §1.5. It maps 0 to 0 and 1 to 1, leaving Bob's wire 2 out. |
| D37: `teleportInit` (line 104) | Concatenate an input ket on wire 0 with the Bell ket on wires 1,2. | Matches the ordering in dW §1.5: the unknown state, Alice's EPR half, Bob's EPR half. The inverse append equivalence gives the intended pullback on amplitudes. |
| D38: `teleportState` (line 116) | Apply CNOT from wire 0 to wire 1, then H on wire 0, to teleportInit; no measurement has yet occurred. | Matches Alice's premeasurement circuit in dW §1.5. Its name does not assert that measurement or classical communication has already happened. |
| D39: `bobVec` (line 155) | Select the amplitude slice where Alice's first two labels are the specified outcomes; leave Bob's wire free, without renormalizing. | Matches the unnormalized projected branch in dW §1.5. Its squared norm is 1/4, so it is deliberately a vector and not a Ket; normalization is a subsequent conditional-state operation. |
| D40: `denseCode` (line 178) | Apply Z to exponent b0 first, then X to exponent b1, on one wire. | Correct encoding for the library's decoded wire order. Compared with NC §2.3, the 01 and 10 labels are exchanged and the 11 operator differs by a global sign; this undeclared harmless convention is finding 3. |
| D41: `superdenseState` (line 187) | Encode the first half of bell with denseCode, then CNOT 0-to-1 and H on wire 0. | Correct Bell measurement implemented by CNOT then H on the first wire. NC §2.3 uses the alternative message labels noted in finding 3; the library's own encoding and decoding are consistent. |

## Promise Basic

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Promise/Basic.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D42: `Problem` (line 64) | Two disjoint sets of finite Boolean strings, with no requirement that their union contain every string. | Exactly the disjoint yes/no sets of Watrous §II.1. Neither decidability nor totality is required of an arbitrary promise problem; the promise may even be empty. |
| D43: `ofLanguage` (line 74) | Use the language as the yes set and its complement as the no set. | Exactly the standard embedding of a language as a total promise problem, Watrous §II.1. Its disjointness proof is logically sound and the complement is taken in all finite Boolean strings. |
| D44: `Problem.IsTotal` (line 87) | Every Boolean string belongs to either the yes set or the no set. | The additional assertion that the promise covers all inputs. Together with the structure's disjointness, the no set is then the complement of the yes set; this is not imposed on all promises. |
| D45: `InPromiseP` (line 101) | There exists a language in the received P class that includes every yes instance and excludes every no instance. | Equivalent to a total polynomial-time decider correct on the promise, Watrous §II.1. This uses the received P characterization; no computability of promise membership is required. |
| D46: `InPromiseBPP` (line 120) | One E-efficient total Boolean verifier and a monomial random-bit schedule accept every yes input with probability at least 2/3 and reject every no input with probability at least 2/3. | Matches Watrous §II.1 for polyTimeModel. For a Boolean verifier, rejection at least 2/3 is equivalent to acceptance at most 1/3; on other abstract models this is explicitly a relative class. |

## Counting PP

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/PP.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D47: `InPP` (line 55) | One E-efficient Boolean verifier and schedule represent language membership exactly by acceptance probability strictly exceeding one half. | Matches Watrous §II.1 for polyTimeModel: strict acceptance above 1/2 and ties on the no side. Rational probabilities are exact; no rounding or positive lower bound on the bias is imposed. AB09 Definition 17.6 instead assigns ties to yes; equality of the classes needs the conventional bias adjustment, not literal equality of the tests (finding 8). |
| D48: `InPromisePP` (line 73) | An E-efficient Boolean verifier exceeds one half on yes instances and is at most one half on no instances; off-promise behavior is unrestricted. | Matches promise PP in Watrous §II.1. The two implications impose no off-promise constraint, and the asymmetric strict/weak threshold is intentional. |

## GapP

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/GapP.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D49: `gap` (line 70) | The integer number of length-m seeds on which the verifier returns some true minus the number on which it returns some false; none contributes zero. | Matches accepting-minus-rejecting path counts in Watrous §IV.5 after the explicit abstention encoding. Counts are cast separately to integers before subtraction, so negative gaps are retained. |
| D50: `IsGapP` (line 83) | An integer-valued function equals the gap of one E-efficient verifier on one monomial schedule at every input. | For polyTimeModel it describes standard GapP via canonical path transcripts and cancelling abstentions; see answer 7. For arbitrary E it is only a relative class, as the docstring states. |
| D51: `negVerifier` (line 106) | Swap some true and some false, preserving none. | Implements sign reversal of a gap, consistent with FR §2.4. Leaving abstention unchanged is necessary for exact negation. |
| D52: `padVerifier` (line 116) | Run M on the first p(\|x\|) bits only when every remaining bit is false; otherwise return none. A short seed is passed to M intact. | Implements gap-preserving padding using a unique all-false suffix. This is an encoding construction, not ordinary random-bit padding; the source length p must be no larger than the counted length in the preservation lemma. |
| D53: `sumVerifier` (line 128) | Abstain on the empty seed; otherwise use its first bit to choose M1 for true and M2 for false on the tail. | Implements the sum of two gaps by a leading choice bit, consistent with FR's additive closure. The true/false order has no effect on the sum; the empty-seed behavior is explicitly none. |
| D54: `prodVerifier` (line 145) | Split at p(\|x\|); if both verifiers answer, return true for equal answers and false for unequal answers, otherwise abstain. | Implements multiplication of the signs of two independent path choices. Equality of two answers means a positive product, including two rejections; any zero sign remains zero. |
| D55: `constVerifier` (line 162) | On the all-false seed, including the empty seed, return the fixed answer b; on any other seed abstain. | Implements constant gap, not constant output on every seed. There is exactly one all-false seed of each length, including zero; the docstring explains this specialization. |
| D56: `coinFill` (line 172) | Run M on the first p(\|x\|) bits; retain its answer, or replace none with the next bit, defaulting to false if that bit is absent. | Correct total implementation of filling abstentions by a fresh bit. The docstring omits the short-seed default and the length guard for its probability claim; the formal probability lemma has the right guard (finding 5). |
| D57: `ClosedUnderGapNeg` (line 251) | E-efficiency is preserved by swapping accept and reject. | An explicit assumption needed for relative-model negation; a conventional polynomial-time model satisfies it. No textbook claims it for every arbitrary efficiency predicate. |
| D58: `ClosedUnderPad` (line 259) | E-efficiency is preserved by padVerifier at every schedule a(n+1)^k+c, with all parameters fixed natural numbers. | An explicit efficiency assumption for the given padding helper. The added constant c is useful for the selector bit in addition, and every fixed a,k,c gives polynomial-time preprocessing. |
| D59: `ClosedUnderGapSum` (line 269) | The first-bit choice between two efficient verifiers remains efficient. | An explicit efficiency assumption for choosing between two efficient verifiers. It corresponds to a polynomial-time conditional, not a claim that arbitrary models are automatically closed. |
| D60: `ClosedUnderGapProd` (line 277) | Combining the signs of two efficient verifiers split at any monomial schedule remains efficient. | An explicit efficiency assumption for the sign-product helper with a polynomial split. It is sufficient for the multiplication theorem; stronger general computable split points are not silently assumed. |
| D61: `HasConstVerifiers` (line 288) | Both sparse constant-sign verifiers are efficient; unlike the closure implications, this requires efficient verifiers to exist. | An existence assumption for two efficient verifiers, unlike the five closure implications. It is false when Eff is identically False, contrary to the pack's suggested test (finding 6). |
| D62: `ClosedUnderCoinFill` (line 295) | Replacing abstentions by the bit after a monomial prefix gives an efficient Boolean verifier. | An explicit efficiency assumption for a Boolean totalization using one more bit. On short lists the default remains polynomial-time; unbiasedness is asserted only with the separate length guard. |

## PolyTime

[Source file](https://github.com/Shilun-Allan-Li/tcslib/blob/d2d72d18ed5b5845ff25ae028490ee45600ae38f/TCSlib/Complexity/Counting/PolyTime.lean)

| Declaration | Independent mathematical restatement | Docstring and source comparison |
| - | - | - |
| D63: `certVerifier` (line 113) | Return some true exactly when the concatenation x++u belongs to V; otherwise abstain. | Matches the received NP definition's x++u certificates. It counts successful certificates by abstaining on failures; V ∈ P is needed only for the separate efficiency theorem, not for this noncomputable definition. AB09 Definition 2.1 likewise uses exact polynomial-length certificates and explicitly allows length zero; the concatenation encoding is the received library convention. |

The notation `ψ ⊗ᵠ φ` abbreviates `Ket.prod ψ φ` and introduces no further semantics. The generated structure projections and constructors expose the fields already restated in D06 and D42; extensionality identifies equal data with proof fields ignored. Generated recursors and injection lemmas add no new physical or complexity-theoretic specification.

# Literal validity of every directly sorried theorem

Each entry below addresses the statement with its actual hypotheses. “True” here means a mathematical argument was found for the literal statement; it does not change the admitted status in Lean. The counterexamples identified in the findings attack explanatory claims or stronger informal readings, not the 72 formal conclusions.

## Quantum Basic Register

**S01 · `regAppendEquiv_apply_castAdd` · line 105 · True as stated.** The append equivalence first identifies a pair of functions with a function on the disjoint union of their domains, and then transports that domain along the Fin addition equivalence. A castAdd index is in the left summand, so evaluating the transported function returns the original first component; if k=0 there is no such index and the universally quantified assertion is harmless.

**S02 · `regAppendEquiv_apply_natAdd` · line 113 · True as stated.** A natAdd index belongs to the right summand of the same Fin addition equivalence. Transporting it back therefore evaluates the second component at the original index, including when the left block has length zero.

**S03 · `sum_norm_sq_basisVec` · line 127 · True as stated.** The delta vector has exactly one nonzero coordinate, at the supplied index, and that coordinate has modulus squared one. Every other summand is zero, so the finite sum is one; a nonexistent index on an empty type is not an admissible input.

**S04 · `sum_norm_sq_comp_equiv` · line 134 · True as stated.** An equivalence gives a bijection between the summation indices and preserves each summand after reindexing. Hence the two finite sums are equal, including the empty-index case where both are zero.

**S05 · `sum_norm_sq_mul_prod` · line 142 · True as stated.** The squared modulus of a product is the product of the squared moduli. Summing over a Cartesian product and distributing finite sums factors the total into the two stated sums, with the same identity when either index type is empty.

**S06 · `sum_norm_sq_mulVec_of_mem_unitaryGroup` · line 152 · True as stated.** The sum of squared complex moduli is the Hermitian inner product of the vector with itself. Since unitary membership supplies UᴴU=I, the inner product of Uv with itself equals that of v with itself; this holds for every vector and also for the zero-dimensional space.

**S07 · `evolve_mul` · line 216 · True as stated.** On amplitudes, associativity gives (UV)v = U(Vv), exactly the stated rightmost-first order. Equality of amplitude functions gives equality of Kets because their remaining fields are propositions, so no comparison of normalization proofs is required.

**S08 · `evolve_one` · line 223 · True as stated.** The identity matrix fixes every amplitude function. Extensional equality of the data fields then identifies the two normalized kets, regardless of which normalization proof their constructors used.

## Quantum Basic Gates

**S09 · `permMat_mem_unitaryGroup` · line 90 · True as stated.** Each column and each row of a permutation matrix has a unique one and otherwise zeros. Their Hermitian inner products are the corresponding Kronecker deltas, giving both unitary identities; the empty matrix also satisfies these identities.

**S10 · `permMat_mulVec_basis` · line 96 · True as stated.** Multiplication by a delta vector selects column x. That column has its one exactly at σ(x), so the result is the delta vector at the forward image, not at the inverse image.

**S11 · `diagonal_mem_unitaryGroup` · line 104 · True as stated.** Multiplying the diagonal matrix by its adjoint gives a diagonal matrix with entries equal to the squared moduli of the phases. The modulus-one hypothesis makes every such entry one and the off-diagonal entries remain zero, proving unitarity in either multiplication order.

**S12 · `flipAt_involutive` · line 147 · True as stated.** The first update leaves every other coordinate unchanged, and the second update again affects only the selected coordinate. At that coordinate, adding one twice in Fin 2 returns the initial value, so the whole function is restored.

**S13 · `hadamardMat_mem_unitaryGroup` · line 190 · True as stated.** In basis order 0,1 the matrix is [[1,1],[1,-1]]/√2. Its columns have norm one and inner product zero because (√2)²=2, which proves unitarity without an omitted positivity assumption.

**S14 · `norm_zPhase` · line 202 · True as stated.** The single bit is either zero or one, so the phase is either 1 or −1. Both complex numbers have modulus one, proving the universal assertion.

**S15 · `norm_sPhase` · line 214 · True as stated.** The exponent is zero or one, so the phase is respectively 1 or i. Both have modulus one, and no other exponent can occur for a Fin 2 value.

**S16 · `H_mul_H` · line 269 · True as stated.** Multiplication of [[1,1],[1,-1]]/√2 by itself gives the identity matrix. Equality of the underlying matrices establishes equality in the unitary group, so the theorem is exact rather than only up to a phase.

**S17 · `S_mul_S` · line 276 · True as stated.** The two diagonal entries square to 1 and i²=−1. Thus S² has exactly Z's matrix and the bundled group elements are equal.

**S18 · `H_mul_Z_mul_H` · line 283 · True as stated.** Matrix multiplication gives HZH = [[0,1],[1,0]]. This is precisely the forward bit-flip permutation used to define X, with no conjugation or global phase adjustment.

**S19 · `X_eq_H_mul_S_mul_S_mul_H` · line 290 · True as stated.** Substituting S²=Z reduces the right-hand side to HZH. The preceding explicit matrix identity gives X, with associativity accounting for the written group product.

**S20 · `Toffoli_apply_of_control_one` · line 301 · True as stated.** Fixing both input and output wire 0 to one restricts the Toffoli permutation to the slice on which its remaining action is (x1,x2) ↦ (x1,x2+x1). This is exactly CNOT on the two succ-indexed wires, so the two matrix entries agree; fixing only the input wire would not justify dropping the output slice condition.

## Quantum Basic ApplyOn

**S21 · `applyOn_one` · line 89 · True as stated.** For the local identity matrix, a nonzero entry requires equality on the selected wires. Together with AgreeOff this is equality on every wire, so the extended matrix is the global identity; for k=0 the same condition comes entirely from AgreeOff.

**S22 · `applyOn_mul` · line 100 · True as stated.** If input and output disagree off the selected wires, every summand in the product is zero. Otherwise, the intermediate registers compatible with those fixed outside bits correspond bijectively to local labels through restriction along the embedding, and the resulting sum is the local matrix product.

**S23 · `applyOn_conjTranspose` · line 108 · True as stated.** AgreeOff is symmetric in input and output, and taking the conjugate transpose swaps those indices and conjugates the matrix entry. Applying these two operations to the entrywise definition yields exactly the placement of the local adjoint.

**S24 · `applyOn_mem_unitaryGroup` · line 116 · True as stated.** Placement preserves multiplication, adjoints and identity by the preceding three statements. Applying it to both unitary equations for U therefore gives both unitary equations for the extended operator, without any extra hypothesis on the chosen wire subset.

**S25 · `applyOn_refl` · line 132 · True as stated.** Every global wire is in the image of the identity embedding, so the outside-wire condition imposes nothing. Restriction along this embedding leaves both labels unchanged, recovering U entry by entry, including n=0.

**S26 · `applyOn_commute_of_disjoint` · line 143 · True as stated.** For A1A2 at entry (y,x), the intermediate label equals x on w1, y on w2, and their common value outside the union; if outside values differ, the entry is zero. Thus the entry is U1(y∘w1,x∘w1)U2(y∘w2,x∘w2), while A2A1 has the reversed scalar product and the opposite intermediate assignment. Complex multiplication is commutative, so arbitrary local matrices commute when placed disjointly; the theorem is true but its supplied sketch swaps the first intermediate assignment (finding 4).

**S27 · `applyOn_castAdd_eq_reindex_kronecker` · line 158 · True as stated.** Write a global label as append(a,b), where a occupies the first k wires. The placed entry between append(a,b) and append(a′,b′) is U(a,a′) if b=b′ and zero otherwise, exactly the entry of U⊗I transported from the product index type to the register index type. This also gives the scalar-times-identity interpretation when k=0 and the identity transport when m=0.

**S28 · `applyOn_mulVec_basis` · line 172 · True as stated.** Multiplication by a basis vector selects the corresponding input column of the placed matrix. Its entry at y is therefore precisely the stated conditional local entry, with all off-wire disagreement sent to zero.

**S29 · `applyOn_wire_X_mulVec_basis` · line 189 · True as stated.** The local X matrix changes the selected bit by one modulo two. The placement rule forces every other bit to remain fixed, leaving a unique output label, flipAt i x, of amplitude one.

## Quantum Basic Measure

**S30 · `prob_nonneg` · line 58 · True as stated.** A ket's basis probability is a real squared norm. Both the norm and its square are nonnegative, independently of normalization.

**S31 · `prob_le_one` · line 68 · True as stated.** The selected squared norm is one nonnegative term of the finite sum of all squared norms. That sum is one by normalization, so no single term can exceed one.

**S32 · `probQubit_nonneg` · line 83 · True as stated.** The marginal is a finite sum of nonnegative squared norms over a filtered set. Each summand is nonnegative and hence so is the sum.

**S33 · `probQubit_zero_add_one` · line 91 · True as stated.** Every basis label has bit value either zero or one at the selected wire, and cannot have both. The two filtered sums therefore partition the full normalized probability sum, giving one.

**S34 · `probQubit_basis` · line 99 · True as stated.** A basis ket has probability one at its own label and zero everywhere else. The filter includes that unique nonzero term exactly when the selected bit of the label equals the requested outcome, yielding the stated indicator.

**S35 · `probQubit_evolve_applyOnU_of_forall_ne` · line 113 · True as stated.** The hypothesis places the measured wire outside the gate's image, so the operator preserves each subspace with a fixed value of that wire. Within each fixed assignment of all untouched wires it applies a copy of the same unitary, preserving the sum of squared amplitudes; summing these norms gives the original marginal. This argument allows entangled inputs and claims no independence of outcomes on different wires.

## Quantum Basic Protocols

**S36 · `no_cloning` · line 67 · True as stated.** Choose distinct basis labels i,j and their normalized equal superposition. If a linear U clones the two basis kets, applying it to that superposition gives (|ii⟩+|jj⟩)/√2, whose (i,j) amplitude is zero, whereas the proposed tensor square has amplitude 1/2. The literal statement is therefore true, but it is also provable using ψ and −ψ alone on any inhabited basis; that phase-based trivialization is finding 1, not a counterexample to the statement.

**S37 · `sum_norm_sq_bellVec` · line 85 · True as stated.** Exactly two of the four two-bit labels have equal bits. Each of their amplitudes has squared modulus 1/2 and the other amplitudes vanish, so the total is one.

**S38 · `teleportInit_vec` · line 110 · True as stated.** The inverse append equivalence sends y to its wire-0 label paired with its wires-1,2 label. The tensor-product amplitude is the product of the two factor amplitudes at those labels, giving exactly the displayed formula.

**S39 · `teleportState_vec` · line 135 · True as stated.** For y=(a,b,c), the CNOT followed by H gives amplitude (−1)^(a(b⊕c)) ψ(b⊕c)/2 by direct summation over the input bit. Applying X^b Z^a to ψ gives that same sign and shifted coordinate, since Z acts before X. This verifies all four measurement labels and the exact complex phase.

**S40 · `teleport_outcome_prob` · line 148 · True as stated.** For fixed Alice outcomes a,b, the amplitude slice is one half of a unitary Pauli operation applied to ψ. Its squared norm is therefore 1/4 times the normalized squared norm of ψ, and the filtered sum in the statement is precisely this slice norm.

**S41 · `teleport_correct` · line 168 · True as stated.** The preceding amplitude formula makes bobVec equal to (1/2)X^b Z^a ψ. Left multiplication by Z^a X^b cancels the adjacent X factors and then the Z factors because a,b are bits and X²=Z²=I. The remaining vector is exactly (1/2)ψ; normalization of a conditioned state would multiply it by two.

**S42 · `superdense_decode` · line 205 · True as stated.** Directly applying the stated encoder and decoder to the Bell vector gives (−1)^(b0 b1) times the basis ket labelled (b0,b1). Its target amplitude has squared modulus one for all four inputs, including 11 where the amplitude itself is −1. Thus the probability statement is correct and intentionally avoids a false unsigned vector equality.

## Complexity Promise Basic

**S43 · `ofLanguage_isTotal` · line 95 · True as stated.** For every string, either it belongs to L or it belongs to the complement of L. These are exactly the two components of ofLanguage L, so their union is all strings.

**S44 · `inPromiseP_ofLanguage_iff` · line 112 · True as stated.** If a P language separates L from its complement, it contains every member of L and contains no other string, so it equals L. Conversely, when L itself belongs to P, choosing it as the separator satisfies both inclusions.

**S45 · `inPromiseBPP_ofLanguage_iff` · line 142 · True as stated.** Substituting the yes set L and the no set Lᶜ turns the two promise implications into the two clauses of the received InBPP definition. The same Boolean verifier, efficiency witness and schedule work in both directions.

## Complexity Counting PP

**S46 · `inPromisePP_ofLanguage_iff` · line 95 · True as stated.** On members of L the promise condition supplies acceptance probability above 1/2, and on nonmembers it supplies probability at most 1/2. Since the rational order is linear, these clauses are equivalent to membership iff acceptance is above 1/2, using exactly the same witnesses.

**S47 · `randProb_cast_eq_sum` · line 106 · True as stated.** The rational probability is the count of successful seeds divided by 2^m. Casting to reals preserves this quotient, and the finite count is the sum of its real zero-one indicators, so division can be distributed inside the sum. At m=0 there is one empty seed and the denominator is one, making the identity valid without a positive-m assumption.

## Complexity Counting GapP

**S48 · `gap_boolVerifier` · line 99 · True as stated.** A Boolean verifier has no abstaining seeds, so its accepting and rejecting counts add to 2^m. Subtracting the latter count yields twice the accepting count minus 2^m; rewriting the count as 2^m times its rational probability gives the stated identity.

**S49 · `gap_negVerifier` · line 188 · True as stated.** The negated verifier's accepting set is the original rejecting set and vice versa. Abstentions remain abstentions, so the difference of the two cardinalities changes sign at every seed length.

**S50 · `gap_padVerifier` · line 199 · True as stated.** The length hypothesis makes each length-p seed extend to exactly one surviving length-m seed, by appending only false bits. That bijection preserves each accept/reject answer and all other extended seeds abstain, so both signed counts and their difference are unchanged.

**S51 · `gap_sumVerifier` · line 210 · True as stated.** A seed of length m+1 is uniquely a selector bit and a tail of length m. One selector value contributes the entire first gap and the other the entire second gap, so addition is exact even at m=0.

**S52 · `gap_prodVerifier` · line 220 · True as stated.** A seed of the specified total length splits bijectively into a first block of length p(|x|) and a second of length m. Giving accept, reject and abstain the signs +1, −1 and 0, the combined verifier's sign is the product of the two signs, and distributing the double sum yields the product of the two gaps.

**S53 · `gap_constVerifier` · line 230 · True as stated.** Exactly one seed at any length is all false, including the empty seed at length zero. Only this seed contributes, with sign +1 or −1 according to b, so the result is the stated constant independent of the length.

**S54 · `randProb_coinFill` · line 242 · True as stated.** Let T,F,N count accepting, rejecting and abstaining prefixes of length p, so T+F+N=2^p. The fresh bit gives 2T+N accepting extensions out of 2^(p+1), which equals 1/2+(T−F)/2^(p+1); additional suffix bits repeat every case equally. The hypothesis guarantees that fresh bit exists, so the short-list default does not affect this probability.

**S55 · `IsGapP.neg` · line 311 · True as stated.** Take the verifier and schedule witnessing the given gap function. The assumed negation closure makes the negated verifier efficient, while gap_negVerifier changes its gap to the required pointwise negative on that same schedule.

**S56 · `IsGapP.add` · line 322 · True as stated.** For schedules a1(n+1)^k1 and a2(n+1)^k2, set A=a1+a2, K=max(k1,k2), and q(n)=A(n+1)^K, which dominates both source lengths even at n=0. Padding each verifier with an all-false suffix preserves its gap at length q, and the selector construction gives the sum at q+1. A final application of ClosedUnderPad with source length q+1 (its constant c=1) preserves this sum on the admissible schedule (A+1)(n+1)^K, which is at least q+1.

**S57 · `IsGapP.mul` · line 331 · True as stated.** Pad both witnesses to q(n)=(a1+a2)(n+1)^max(k1,k2), preserving their gaps and efficiency. The product closure permits splitting at this q, and gap_prodVerifier gives the product at length 2q, itself a valid monomial schedule with coefficient 2(a1+a2). The argument also covers coefficient zero, where both independent seed blocks are empty.

**S58 · `isGapP_one` · line 338 · True as stated.** HasConstVerifiers supplies efficiency of constVerifier true. Choose a=0 and k=0, and gap_constVerifier gives one at every input on the resulting zero-length schedule.

**S59 · `isGapP_neg_one` · line 345 · True as stated.** HasConstVerifiers also supplies efficiency of constVerifier false. Its unique all-false seed contributes −1, in particular on the zero-length monomial schedule, witnessing the required constant function.

**S60 · `inPP_iff_exists_isGapP` · line 359 · True as stated.** Forward, the Boolean verifier already witnessing InPP is an efficient Option Bool verifier through boolVerifier, and gap_boolVerifier identifies positivity with the strict probability threshold. Backward, coinFill applied to a gap witness is efficient by the stated hypothesis and has acceptance bias with exactly that gap's sign. Using schedule (a+1)(n+1)^k supplies at least the needed a(n+1)^k+1 bits, and ignored remaining bits leave the probability unchanged.

## Complexity Counting PolyTime

**S61 · `polyTimeModel_closedUnderGapNeg` · line 60 · True as stated.** Under the received definition, an efficient Option verifier has P languages for its accepting and rejecting outputs. Swapping those two languages characterizes the swapped outputs of negVerifier, establishing efficiency with no separate computation of an arbitrary M.

**S62 · `polyTimeModel_closedUnderPad` · line 70 · True as stated.** For fixed a,k,c, the prefix length a(|x|+1)^k+c, take, drop and the all-false test are computable in polynomial time in the encoded pair length. Preimages of the original accepting and rejecting P languages under the prefix map, intersected with the suffix test, give the two required P languages. This also handles short seeds, where drop is empty and take returns the original seed.

**S63 · `polyTimeModel_closedUnderGapSum` · line 79 · True as stated.** Testing whether the seed is empty and reading its first bit and tail are polynomial-time operations. A finite union of the appropriate selector-restricted preimages of each original output language gives the accepting language, and the same construction gives the rejecting language; on an empty seed neither applies.

**S64 · `polyTimeModel_closedUnderGapProd` · line 88 · True as stated.** The polynomial split and the two list projections are polynomial-time. The accepting language is the union of the accept/accept and reject/reject combinations of the two original P languages, and the rejecting language is the union of the two opposite-sign combinations. Closure of P under these fixed Boolean operations and preimages establishes efficiency, including split zero.

**S65 · `polyTimeModel_hasConstVerifiers` · line 96 · True as stated.** The all-false condition on a finite seed is decidable by a linear scan. For fixed b, use that P language for output some b and the empty language for the other output; these characterize constVerifier on every encoded pair.

**S66 · `polyTimeModel_closedUnderCoinFill` · line 105 · True as stated.** Run the two P output-language deciders on the polynomial prefix and test the next bit, using false if it is absent. Accept when the accepting prefix predicate holds, or when neither output predicate holds and the next bit is true; reject on the complementary Boolean cases. These are polynomial-time predicates, so the total Boolean verifier is efficient on all pairs, not only sufficiently long seeds.

**S67 · `gap_certVerifier` · line 126 · True as stated.** This verifier never returns some false, so its rejecting count is zero. Its accepting seeds are exactly the length-m strings whose concatenation with x lies in V, which is the finite count on the right; no efficiency assumption on V is needed for this equality.

**S68 · `polyTimeModel_eff_certVerifier` · line 137 · True as stated.** Decode the pair and concatenate its two components, a polynomial-time transformation on the received pair encoding. The preimage of V under this transformation is in P and characterizes acceptance on valid encoded pairs, while the rejecting language is empty, supplying precisely the received efficiency witness.

## Complexity Counting Inclusions

**S69 · `InBPP.inPP` · line 52 · True as stated.** On members, the BPP acceptance probability is at least 2/3 and hence exceeds 1/2. On nonmembers, Boolean acceptance plus rejection equals one and rejection is at least 2/3, so acceptance is at most 1/3 and cannot exceed 1/2. Keeping the same efficient verifier and schedule proves the equivalence required by InPP for every model E.

**S70 · `InPP.compl` · line 61 · True as stated.** The assumed coin-filling property converts the given PP witness to an integer gap f with membership iff f>0. Using the supplied constant, negation, padding and addition hypotheses gives the gap g=1−2f, and integrality yields g>0 iff f≤0. The sign characterization applied again therefore recognizes the complement, including all tie inputs; a product-closure hypothesis is not needed.

**S71 · `inPP_polyTimeModel_compl` · line 69 · True as stated.** Each hypothesis of the abstract complement theorem is supplied by the corresponding stated polynomial-time efficiency fact. Instantiating them gives complement closure for polyTimeModel without any additional language assumption.

**S72 · `inPP_polyTimeModel_of_mem_NP` · line 81 · True as stated.** Let c(x) count successful certificates of the exact length C(|x|+1)^c provided by the received NP witness. The certificate verifier makes this a nonnegative gap, and the established polynomial-time closures make 2c(x)−1 a gap positive exactly when at least one certificate exists. If C=0, there is one possible empty certificate, so the transformed gap is either −1 or +1; x=[] causes no other change.

# Other theorem statements and generated declarations

The remaining 59 named theorems were checked as statements, without examining their tactic proofs. Fifty-six are direct equation, coercion or membership-characterization lemmas: their assertions match the corresponding definition restatements above, including the 18 whose constants transitively inherit sorryAx. The three other statements have the following meanings and checks.

- `cnotMap_involutive`: the control bit is unchanged and XORing it into the target twice restores the target.

- `toffoliMap_involutive`: both controls are unchanged and XORing their product into the target twice restores the target.

- `Ket.sum_prob`: the total probability is exactly the normalization field already required of a ket.

| File | Statements checked |
| - | - |
| TCSlib/Quantum/Basic/Register.lean | `qubitEquivBool_eq` (82); `basisOf_apply` (89); `basis_vec` (180); `relabel_vec` (190); `prod_vec` (201); `evolve_vec` (210) |
| TCSlib/Quantum/Basic/Gates.lean | `permMat_apply` (83); `ofPerm_coe` (121); `ofPhase_coe` (129); `flipAt_eq` (140); `cnotMap_eq` (154); `cnotMap_involutive` (157); `toffoliMap_eq` (167); `toffoliMap_involutive` (170); `hadamardMat_apply` (183); `zPhase_eq` (197); `sPhase_eq` (209); `H_coe` (225); `X_coe` (231); `Z_coe` (239); `S_coe` (245); `CNOT_coe` (251); `Toffoli_coe` (259) |
| TCSlib/Quantum/Basic/ApplyOn.lean | `agreeOff_iff` (66); `applyOn_apply` (80); `applyOnU_coe` (125); `wire_apply` (181) |
| TCSlib/Quantum/Basic/Measure.lean | `prob_eq` (53); `sum_prob` (62); `probQubit_eq` (77) |
| TCSlib/Quantum/Basic/Protocols.lean | `bellVec_eq` (78); `bell_vec` (92); `wires01_apply` (100); `teleportState_eq` (120); `bobVec_apply` (159); `denseCode_eq` (181); `superdenseState_eq` (193) |
| TCSlib/Complexity/Promise/Basic.lean | `ofLanguage_yes` (80); `ofLanguage_no` (83); `Problem.isTotal_iff` (90); `inPromiseP_iff` (105); `inPromiseBPP_iff` (129) |
| TCSlib/Complexity/Counting/PP.lean | `inPP_iff` (63); `inPromisePP_iff` (82) |
| TCSlib/Complexity/Counting/GapP.lean | `gap_eq` (75); `isGapP_iff` (88); `negVerifier_eq` (110); `padVerifier_eq` (122); `sumVerifier_eq` (136); `prodVerifier_eq` (153); `constVerifier_eq` (166); `coinFill_eq` (178); `closedUnderGapNeg_iff` (255); `closedUnderPad_iff` (264); `closedUnderGapSum_iff` (273); `closedUnderGapProd_iff` (282); `hasConstVerifiers_iff` (291); `closedUnderCoinFill_iff` (300) |
| TCSlib/Complexity/Counting/PolyTime.lean | `certVerifier_eq` (118) |

The constructors, projections, extensionality and injection statements generated for `Ket` and `Promise.Problem` reflect their explicit data fields and proof fields. They do not assert an additional normalization law, quantum model equivalence or complexity-class inclusion.

# Answers to the thirteen phase questions

## 1 Definitions inheriting sorryAx

This is acceptable for a statement skeleton. The vector or matrix data in all nineteen definitions is explicit: delta functions, finite products, matrix entries, matrix-vector products and compositions; the sorried normalization/unitarity facts are used only to justify membership in a structure or subtype. Permutation equivalences also use involutivity in proof fields, while their forward maps remain explicit.

I would not require these small proofs before closing a statement gate merely to remove transitive sorryAx from definitional equations. I would require the gate record to retain the distinction between 72 admitted theorem statements, 18 equation theorems transitively depending on them, and 19 affected data definitions. This audit supplies mathematical plausibility arguments, not kernel certification of the admitted statements.

## 2 Placement of local operators

The entrywise definition is exactly U on the selected ordered wires and identity on the complement. Injectivity of w is essential: for any chosen local label and fixed outside bits there is one compatible global label, giving the bijection needed for multiplication and norm preservation.

The Kronecker bridge is oriented correctly. Under regAppendEquiv k m, the entry between (a,b) and (a′,b′) is U(a,a′) times the indicator of b=b′, which is U⊗I with U on the first k wires. For k=0 the local label type has one element, and AgreeOff requires y=x; the result is the sole scalar entry times the global identity, including when n=0.

## 3 Gate and matrix conventions

The conventions are consistent: matrix columns are input labels, rows are output labels, permMat σ maps the basis vector at x to the basis vector at σ(x), and evolve is left matrix multiplication. H has the usual matrix [[1,1],[1,−1]]/√2; Fin 2 arithmetic inside its exponent gives the intended sign.

Accordingly, a product X^b Z^a applies Z first. The teleportation slice is (1/2)X^b Z^a ψ and its inverse correction is Z^a X^b. This agrees with dW §1.4–1.5. Watrous's P is the gate called S here, as explicitly disclosed.

## 4 Teleportation and superdense strengths

All four protocol statements are correct under the declared wire order: wire 0 holds the unknown input, wire 1 Alice's EPR half and wire 2 Bob's half. The amplitude theorem determines the entire premeasurement state. The filtered probability theorem says every Alice outcome has probability 1/4, and the corrected branch is (1/2)ψ because bobVec is unnormalized; dividing by its norm 1/2 gives the conditional state ψ.

These statements provide a precise pure-input protocol correctness result. They do not themselves state correctness when the input is entangled with an external reference, which dW also discusses; that follows from the linear operator identity behind the branch formula and could be added later. The current use of bobVec does not accidentally assert normalization.

For superdense coding, the actual decoded vector is (−1)^(b0 b1) times the basis ket at (b0,b1), so probability one is the right phase-insensitive claim. The message labels differ from NC §2.3 as recorded in finding 3; this is a convention change, not a decoding failure.

## 5 No cloning

The literal theorem is true, and its two-basis-vector superposition argument works. However, requiring exact copying of every ket representative also rules out a map for the unphysical reason that ψ and −ψ represent the same physical state but have different linear input signs and identical tensor squares. Consequently Nontrivial is unnecessary for the current assertion; an inhabited one-element basis already gives a contradiction.

I would strengthen the specification now, while it has no downstream users, by adding the following assertion: no unitary can send every ψ⊗|e⟩ to cψ(ψ⊗ψ), where cψ may depend on ψ and has modulus one. Better still, prove the two-state obstruction for 0 < |⟨ψ,φ⟩| < 1, allowing a separate phase for each output. Unitarity would imply t=t² for the overlap modulus t, contradicting that interval. This permits phases and does not need a quotient-of-kets infrastructure; it also makes the expected one-dimensional exception meaningful.

## 6 One-wire measurement

probQubit is the Born probability for the projector onto basis labels with the designated bit value. It correctly sums squared amplitude moduli rather than taking the squared modulus of their sum, so it works for entangled states as well as product states.

The hypothesis ∀j, w j ≠ i says exactly that i is outside the gate's image. The invariance theorem is a no-signalling statement for the measured marginal, not a statement that two measurement outcomes are independent. For instance the Bell state's two outcomes are correlated, even though a unitary on one wire cannot alter the other wire's marginal.

## 7 Abstention and standard GapP

At polyTimeModel this is the intended standard GapP class, mathematically. From the verifier formulation, the two P output predicates give two #P seed-count functions, and their difference is the specified gap. Equivalently a nondeterministic machine guesses the scheduled seed, evaluates the verifier, halts with its answer, and replaces each abstention with one accepting and one rejecting branch; this adds zero rather than multiplying a signed contribution.

Conversely, choose a polynomial bound on the number of nondeterministic choices. A seed canonically describes a computation by recording its actual choices and requiring all unused padding bits to be false; invalid choices or noncanonical padding abstain. Each original computation path then has exactly one counted seed of the desired sign. Encoding a fixed finite branching alphabet with bits introduces only invalid codes, which likewise abstain. Fixed polynomial bounds can be dominated by a monomial schedule using the same unique-padding construction.

A formal bridge theorem should eventually make this correspondence explicit. A difference-of-two-polynomial-witness-counts predicate would already give a useful internal sanity theorem without first formalizing an entire nondeterministic machine model. The identically abstaining verifier merely witnesses the zero function when it is efficient; zero is a legitimate gap, and each witnessed gap still has absolute value at most 2 raised to its seed length.

## 8 Closure hypotheses and vacuity

All six hypotheses are mathematically valid for polyTimeModel. The five closure implications express polynomial-time operations on two output predicates, and HasConstVerifiers supplies two actual efficient witnesses; they are not all vacuous implications. For Eff identically True, every hypothesis holds and every language is in the relative InPP class; for Eff identically False, only the five implications hold, while HasConstVerifiers and all PP/GapP membership witnesses fail.

The padding predicate is correctly restricted to a fixed polynomial source-prefix length a(n+1)^k+c. The extra c is used to preserve the selector bit in the addition construction before its final padding to a monomial schedule. Its probability/counting preservation law requires the counted seed to be at least as long as that prefix; its efficiency law correctly covers all inputs, including shorter seeds.

Coin filling also remains efficiently total on short strings by returning the default false when no bit is available; unbiasedness only holds under the separate fresh-bit guard. The product split a(n+1)^k is polynomial-time and includes zero. These properties are sufficient, conventional assumptions on the intended model; some individual theorems use only a subset, but no impossible assumption or hidden all-model closure is present. Efficient preprocessing more generally remains a deliberate future addition, not an unstated current hypothesis.

## 9 The PP definition

InPP polyTimeModel is the usual strict-majority PP of Watrous §II.1. The probability is an exact rational uniform average, so a tie at 1/2 belongs to the no side and the code does not accidentally demand a bounded gap. The Boolean verifier is total on every pair, while its polynomial-time status comes from the received two-output-language characterization.

The monomial schedule restriction is harmless for the intended polynomial-time model: dominate the original polynomial coin bound by a(n+1)^k and ignore the excess bits, replicating each old computation equally often and preserving its acceptance probability. This argument relies on efficient simulation/preprocessing in that model, and should not be asserted as a generic equivalence for every abstract E. FR's presentation with strictly negative gaps on no instances is an equivalent normal form at polyTimeModel, obtained from an integer sign witness by the appropriate unit offset, not a reason to replace the present weak no-side threshold.

There is a source-convention difference to record: AB09 Definition 17.6 (p.345) uses acceptance at least 1/2. This defines the same standard polynomial-time class, but is not the same test on a fixed verifier. If f is the integer gap for an AB witness, use f+1 to obtain the strict-positive test; conversely f−1 converts a strict-positive integer test to a nonnegative one. See finding 8.

## 10 NP inside PP at the boundaries

The sketch works exactly. For the received NP verifier language V and certificate length p(x)=C(|x|+1)^c, let N(x) count successful certificates. The certificate verifier has gap N(x), and 2N(x)−1 is positive precisely when a certificate exists; the stated GapP closures and the sign characterization supply a PP verifier.

At x=[] the schedule is C, so there is no zero-base-power anomaly. At C=0 there is one candidate certificate, the empty list; N(x) is zero or one and the transformed gap is −1 or +1. This also covers both conditions simultaneously.

## 11 Promise problems

Problem is exactly a pair of disjoint yes/no sets without a totality requirement, as in Watrous §II.1. Empty yes and no sets are allowed; a promise problem need not come with an algorithm deciding whether an input lies on the promise.

A total polynomial-time machine correct on the promise accepts some P language separating the two sets, and any P separator supplies such a machine. Thus the separator definition is equivalent under the standard total polynomial running-time convention. On ofLanguage L, separation forces the separator to equal L, and the BPP clauses reduce to the received language definition. The analogous PP reduction is also correct, including ties.

## 12 The rational to real probability bridge

The lemma has exactly the right finite-average form: each of the 2^m seeds contributes either zero or 2^(−m) to a real sum. Its rational-to-real coercion preserves division, and m=0 gives a single term with denominator one.

This is the needed scalar equality for a later reversible simulation of a randomized computation initialized with Hadamard coin qubits. That later circuit must retain orthogonal coin records or otherwise justify the absence of interference between different seeds, as well as prove its uniform construction and running time. The present averaging identity supplies none of those circuit claims, and does not purport to.

## 13 Missing machine-checkable sanity statements

The highest-value additions are: a phase-invariant no-cloning statement; explicit zero-wire placement; a noncontiguous and reversed-order two-wire placement example; X ≠ I; a Boolean gap/count formula in integers; and an exact witness-count bridge for IsGapP polyTimeModel. Concrete proposed assertions and test instances follow in the sanity-statements section.

I would also add qubitEquivBool's values at 0 and 1, the cardinality of Reg n, the absence of a Ket on an empty basis, and empty-seed equations for the counting helpers. These distinguish an empty basis from a zero-qubit register and protect the subtle conventions without reproducing every implementation equation. A simple deterministic PP language such as the strings whose first bit is true would exercise the intended model rather than the degenerate Eff=True model.

# Adversarial instantiations

Negative controls below deliberately violate a formal hypothesis only when marked as such. They check that the guard is necessary, rather than purporting to refute a theorem that contains it.

| ID | Target | Concrete instance | Result | Evidence |
| - | - | - | - | - |
| A01 | Zero qubits | n=0; the unique function Fin 0 → Fin 2 is the only basis label. | Reg 0 has cardinality one. A ket is a unit-modulus complex scalar, not an empty vector; Gate 0 contains all unit phases. Normalization and identity evolution remain meaningful. | Mathematical calculation; scalar placement also executed. |
| A02 | No selected wires | k=0, n=3, local matrix [i]; also n=0 with raw local matrix [2+3i]. | Placement is iI on three qubits and [2+3i] on the zero-qubit register. No hypothesis requires a raw matrix to be unitary. | Independent matrix checks passed. |
| A03 | Phase-only copying obstruction | In the admissible d=Fin 2 case compare a basis ket ψ and −ψ. Separately inspect Ket Unit and the proposed assertion without Nontrivial. | The exact universal copying condition contradicts linearity already on these two representatives. On Unit the same contradiction holds after dropping the unavailable Nontrivial hypothesis, although the identity clones the unique physical ray. | Concrete derivation; finding 1, not a counterexample to the Lean theorem. |
| A04 | Empty basis | d is empty, as distinct from Reg 0. | A normalized ket would require 0=1, so no ket exists. Raw norm/unitarity identities over the empty basis still hold; no_cloning also cannot receive a blank e. | Mathematical calculation. |
| A05 | Reversed and noncontiguous wires | n=3, w(0)=2, w(1)=0, U=CNOT, input 011. | The output is 111: wire 2 controls wire 0 and wire 1 remains 1. This detects a reversed control/target convention or implicit sorted-wire convention. | Independent matrix check passed. |
| A06 | Nonunitary local operators | Place A=[[2+i,−1+3i],[−2i,4]] on wire 0 and B=[[2i,1],[3,−2+i]] on wire 1. | The placed operators commute, confirming that the theorem's raw-matrix generality is correct. Placing X and Z on the same wire fails to commute, but then disjointness is false. | Both positive and negative-control matrix checks passed. |
| A07 | Intermediate label in commutation | X on each of two separate wires; x=00, y=11. | The product with wire-0 X on the left uses intermediate 01; the reversed product uses 10. Final products agree, but one common intermediate assignment is incorrect. | Direct basis tracing; finding 4. |
| A08 | Entangled measurement | Bell ket; apply X on wire 1 and measure wire 0. | The wire-0 marginal stays 1/2. Joint probability of 00 changes from 1/2 to 0, demonstrating why the theorem must be read as marginal invariance, not joint independence. | Independent probability checks passed. |
| A09 | Complex teleportation input | ψ=(1/√3, i√(2/3)); each of 00,01,10,11 as Alice's outcomes. | All four branch vectors match (1/2)X^bZ^aψ, all probabilities are 1/4, and correction Z^aX^b returns (1/2)ψ exactly. This tests complex phase as well as normalization. | Twelve independent branch/correction/probability checks passed. |
| A10 | Superdense negative phase | Encode every message, with special attention to 11. | The exact output is (−1)^(b0 b1) times the target basis vector. In particular 11 yields −\|11⟩ and still has target probability one. | Four independent exact-phase checks passed. |
| A11 | Zero random bits | Use constant outputs some true, some false and none at m=0; inspect both sparse constVerifiers. | The unique empty seed gives gaps +1, −1 and 0. Each sparse constant verifier has the stated ±1 gap, not zero; a one-bit sum uses its selector on the empty tail. | Direct finite counting; zero-block products executed. |
| A12 | Zero split in products | p=0,m=0 and all nine ordered pairs of outputs in {some true,some false,none}. | The output signs are the products of the two signs, including two rejections giving +1 and either abstention giving zero. | All nine cases executed successfully. |
| A13 | Padding a too-short seed | M always some true, p=1, m=0. | The padded gap is 1 but the original length-1 gap is 2. This is a counterexample to the unguarded claim only; gap_padVerifier excludes it by p≤m. | Negative-control check passed. |
| A14 | Missing fresh coin | M always none, p=0, m=0; then compare m=1. | With no seed bit, acceptance is 0 by the false default; with one bit it is 1/2. The formal lemma's p+1≤m guard is necessary and sufficient. | Both cases executed; finding 5 concerns only prose. |
| A15 | Extreme abstract models | Eff identically True and Eff identically False, with the irrelevant two-witness field chosen arbitrarily. | The first permits any characteristic-function verifier, so every language is relatively in PP. The second has no witnesses; five closure implications hold, but HasConstVerifiers fails. | Quantifier-level derivation; finding 6. |
| A16 | Empty and universal languages | polyTimeModel with Boolean verifier constantly false or true and a=0. | Acceptance is respectively 0 or 1, so the intended model represents both boundary languages. Their Boolean gaps are −1 and +1, and complement exchanges them. | Direct counting; complements also covered by the integer test. |
| A17 | Exact PP tie | One random bit; M returns that bit on all x. | Acceptance is 1/2, hence this verifier witnesses the empty language under InPP. Negating its output still ties and cannot witness the complement; 1−2f with f=0 instead gives positive gap one. | Concrete tie calculation; integer complement test passed for f from −50 to 50. |
| A18 | Zero schedule coefficients | Addition witnesses have a1=a2=0, k1=k2=0; input is []. | The common prefix length is 0, the sum needs its one selector bit, and the final monomial length is 1. The product has total length 0. Neither closure silently loses the needed selector or invents an extra product bit. | Arithmetic and zero-seed calculation. |
| A19 | Empty NP certificate | C=0 and x=[]; take V accepting [] or rejecting []. | There is one candidate certificate, so its count is 1 or 0 and the PP sign witness is +1 or −1. No positivity assumption on C is missing. | Direct finite counting. |
| A20 | Empty promise | yes=no=∅. | All correctness clauses on the promise are vacuous, as the standard definition permits, but randomized membership still requires an efficient verifier. At polyTimeModel one exists; at Eff=False it does not. | Quantifier-level derivation. |
| A21 | Exhaustive small counting functions | All 81 maps from two-bit seeds to {accept,reject,abstain}, and all 6,561 ordered pairs. | Padding and coin filling were tested at multiple valid lengths; sums and products were checked for every pair. The 13,608 exact integer and dyadic-rational assertions passed. | Independent exhaustive JavaScript calculation. |

# Proposed machine checkable sanity statements

The following are proposed statements, not added or re-elaborated Lean declarations. Their purpose is to distinguish the intended mathematical model from nearby incorrect encodings.

1. **Basis and empty-space distinctions.** State `qubitEquivBool 0 = false`, `qubitEquivBool 1 = true`, and `Fintype.card (Reg n) = 2^n`. Add `IsEmpty (Ket d)` when `IsEmpty d`, and exhibit a ket on `Reg 0`; these must not be conflated.

2. **Zero-wire placement.** For `w : Fin 0 ↪ Fin n`, let `e : Reg 0` be the unique empty function and state `applyOn w U = U e e • (1 : Matrix (Reg n) (Reg n) ℂ)`. This tests the scalar behavior without restricting U to unitary matrices.

3. **Nontrivial gates and wire order.** State `Gate.X ≠ 1`, `Gate.X * Gate.X = 1` and `Gate.Z * Gate.Z = 1`. For the embedding with local wires (0,1) mapped to global wires (2,0), state that placed CNOT sends a basis label x to the label with wire 0 equal to x0+x2 and all other wires unchanged.

4. **Stronger no cloning.** With the same finite basis and fixed blank, replace the exact cloning predicate by the displayed phase-permitting predicate and prove its negation under `Nontrivial d`. A two-state theorem with overlap modulus strictly between zero and one is stronger and exposes the substantive obstruction.

```lean
∃ U : Matrix.unitaryGroup (d × d) ℂ,
  ∀ ψ : Quantum.Ket d, ∃ c : ℂ, ‖c‖ = 1 ∧
    (U : Matrix (d × d) (d × d) ℂ) *ᵥ
        (Quantum.Ket.prod ψ (Quantum.Ket.basis e)).vec =
      c • (Quantum.Ket.prod ψ ψ).vec
```

This is proposed signature syntax, not a claim of successful elaboration in the pinned environment. The elementary modulus-of-inner-product argument in answer 5 proves the intended mathematics.

5. **Integer Boolean gap formula and a bound.** State, without a rational cast, that the gap of `boolVerifier M` is twice its accepting-seed count minus `(2 : ℤ)^m`. Also state `|gap M m x| ≤ (2 : ℤ)^m`; the two disjoint counted sets partition a subset of all seeds.

6. **Empty and short seeds.** Add the explicit three-way equation for `gap M 0 x`, the empty-seed equation for `coinFill`, and the all-none valid-length coin-fill probability 1/2. Negative examples A13–A14 can be preserved as small regression lemmas showing why the guards cannot be deleted.

7. **Standard GapP bridge.** Introduce a counting predicate for the number of polynomial-length witnesses accepted by a P predicate. State that `IsGapP polyTimeModel f` is equivalent to f being a difference of two such count functions; exact false-suffix padding handles different schedules. This is the appropriate formal connection before later code treats the abstract class as standard GapP.

8. **A concrete polynomial-time PP language.** State membership of `{x | x.headD false = true}` in `InPP polyTimeModel`, using a deterministic verifier and zero random bits, together with membership of ∅ and univ. The first-bit language contains [true] and excludes [], so the example cannot be discharged by confusing it with either boundary language.

9. **Explicit source-threshold bridge.** Define the variant with acceptance at least 1/2 and prove its equivalence to `InPP polyTimeModel`; do not quantify over all efficiency predicates without closure assumptions. This would turn finding 8's source adjustment into a named result.

10. **Phase and measurement checks.** State the exact superdense vector equation including `(−1)^(b0.val*b1.val)`, and state that the probability of a product-basis outcome in a tensor ket factors. Keep the Bell example showing correlation, so the marginal-invariance theorem cannot be mistaken for independence.

# Evidence and cumulative duplication ledger

The evidence was checked at three different levels: supplied execution records, source inspection at the recorded commit, and independent mathematical or finite checks. They should not be treated as interchangeable.

| Attestation | Audit result |
| - | - |
| Fourteen-module elaboration sweep | The supplied log has fourteen exit-zero entries and a total of 72 direct sorry warnings, matching the source inventory. No new pinned Lean run was performed. |
| Axiom census | The supplied census contains exactly 228 entries, with the reported 119 clean, 90 sorry-dependent theorem constants and 19 sorry-dependent definitions. The only listed axiom names are the three standard ones and sorryAx; this is consistency of the evidence, not a rerun of its Lean generator. |
| Definitions with inherited proof admissions | Direct normalized-vector constructors: Ket.basis, Ket.relabel, Ket.prod, Ket.evolve, bell. Unitary constructors and named gates: Gate.ofPerm, Gate.ofPhase, Gate.H, Gate.X, Gate.Z, Gate.S, Gate.CNOT, Gate.Toffoli, applyOnU. Composites exposing the same explicit data: teleportInit, teleportState, bobVec, denseCode, superdenseState. Total: 19. |
| Style coverage | Ordinary style_lint.log reports fourteen files. The campaign-specific log reports only eleven, as finding 7 records; these are separate claims. |
| Tree and namespace screen | The fetched repository tree contains the recorded 936 Lean files. The supplied namespace screen is a name-collision check; it cannot establish absence of semantically equivalent declarations in other namespaces. |
| Numerical evidence | The supplied log reports 27 successful checks. This audit independently executed the exhaustive and boundary cases described above; its additional computation is not represented as execution of the bundled Python scripts. |
| Received dependencies | Randomized.Classes, Randomized.PolyTimeModel, ClassP.P and ClassNP.NP were read as required. The 82-module dependency elaboration statement remains supplied maintainer evidence; auditing those modules or their tactic proofs was outside this request. |
| Hosts and other future infrastructure | The P1 surface introduces no search host, machine interpreter or recursive runner. The model-relative efficiency predicates do not construct a machine host. Circuits, BQP, QMA and later plan items were not audited. |

The cumulative overlap is the Ket/standard-gate/Born-rule layer shared conceptually with Physlib, together with the existing root-level sigmaX and sigmaZ in QuantumHamming. The checked QuantumHamming file uses the expected two-by-two Pauli matrices; the nearby existing QuantumSingleton material does not provide a parallel copy of the new PP/GapP or placement interfaces. The two Physlib sources at the cited commit establish that the overlap is substantive, rather than merely similar naming.

The plan's decision log, in its November 6 FD-1/FD-2 revision, already records owner approval of this temporary Physlib overlap and its deletion upon adopting the dependency. OQ-1 records that dependency-switch resolution; OQ-6 records the Pauli cleanup. There is therefore no new unacknowledged wholesale duplication found here to which the pack's mandatory “major / human acknowledgment required” debt finding would apply. This conclusion concerns the audited surface and the checked ledger entries; it is not a claim that every one of the repository's 936 files has been exhaustively compared for semantic equivalence.

The major findings require specification or documentation repair, not a claim that the admitted Lean mathematics is inconsistent. Under the supplied gate workflow, their resolution should be followed by the required re-audit. None of the finite checks, supplied logs, or this report changes a sorry into a proof.
