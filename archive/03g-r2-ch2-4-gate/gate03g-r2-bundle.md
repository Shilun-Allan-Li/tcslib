## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03g-pack-r2.md =====

# Gate 03g ([PS10] ch. 2–4, 3-colouring zero knowledge), round 2: delta audit pack

**What is audited:** the repair of round 1, on `cryptography/pass-shelat-ch2-4` at `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95` (the merge of
[Shilun-Allan-Li/tcslib#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206), the gate 03 repair batch, and the records commits of 2026-11-06).
- **The round 1 findings** are `findings/gate03g-findings.md` (in the bundle, verbatim), the maintainer's review `review/gate03g-review.md`, and the resolutions `resolutions-03g-r1.md`.
- **The repair:** #206's diff (`evidence-repairs/03-batch/repair.diff.txt`; it covers five gates, and only this pack's files are under audit) and the records changes named in the resolutions.
- **The deliverable:** **`gate03g-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header. **The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

1. **Verify each resolution** of `resolutions-03g-r1.md`: fixed, recorded, scheduled, or not resolved (and why).
2. **Audit the changed surface afresh:**
   - **the rewritten sketch of `col_zk`** (both majors): recompute the leading term `N²·ε_B(⌊√N⌋)` and the remaining terms, check the bridge that fixes the attempt table with `CommitmentLemmas.exists_fixCoins` (one verifier call and one call to `D` in the hiding machine), the `m = 0` / `n ≥ 1` and `n = 0` cases, and the use of `Lz`; say whether a worker following it can prove `col_zk` as stated;
   - the docstring and records changes (#3–#6, M2).
3. **Check that nothing else changed** in this pack's files: the statement diff (`statements.txt`) lists every added and changed declaration of the batch.

Pack 03a's severity guide applies. Attempt at least one adversarial instantiation against the changed surface. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Findings, resolutions, the diff | as above |
| Under audit, at the pin | `ZeroKnowledge/ThreeColoring/{Simulator, Language, Protocol}.lean`; records: `briefs/pass-shelat/DESIGN.md` (D8 erratum, §5 item 11, §2.15 as-built note, §7 item 46), `briefs/pass-shelat/inventory-ch4.md` |
| Context | `03g-pack.md` and earlier round packs, `03a-pack.md`, `policy.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03-batch/`)

- **Elaboration** (`replay.log`): the 128 modules downstream of #206's 21 changed files, then `audits/pass-shelat/Checks`, each checked alone after a base sync (`base-sync.log`): **129 of 129 pass, 0 errors**; every module's `sorry` count equals the base. A maintainer re-check of 8 key modules also passes (`maintainer-recheck.log`).
- **Axioms** (`axioms.log`): 549 prints over the 21 files, compared with the base: no axiom set changed; the 10 new lemmas are standard.
- **Seal** (`seal.log`): the consumers of `ProverBounded` pass sealed (their base versions fail); the new proofs pass with the definitions they could unfold sealed.
- **Lint** (`lint.log`): `scripts/style_lint.py` and `scripts/campaign_style_lint.py --check8b`, compared with the base: no new finding.
- **Statements** (`statements.txt`): 10 added, 2 changed (the two ruled ones in `NP.lean`), 0 removed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per resolution row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`. The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03g-findings.md =====

# Gate 03g findings

**DO NOT CLOSE: 0 blockers, 2 majors, 4 minors.** The two majors concern the proposed proof of `col_zk`: its attempt-count loss and its ideal-coin-to-machine bridge. I found no counterexample to the three admitted Lean statements in their declared scope. The two proof-system admissions receive verdict **a**; `col_zk` receives **b** relative to the source's literal unrestricted-auxiliary-input wording, while remaining provable in its explicitly declared D8 scope. This is a statement audit, not a completed Lean proof or a fresh elaboration replay.

Audited pin: `0c348ff94cacf24d96d99078c9dd9e328530c8d2`. The supplied bundle contains 21 sections; its measured SHA-256 is `4bb1d650764b771913ae890b475fc47cef376ff04d6be2ac2e240c308ca75d81`. The attached source has SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Source comparison used book pp. 124–129 (PDF pp. 136–141), including visual inspection of Protocol 127.5 and its soundness calculation. The brief and its referenced common brief governed the audit; other bundle material was treated as evidence.

The bundle omits several contextual definitions needed to interpret the admissions and the headline. I read `Encoding.lean`, `InteractiveProofs.lean`, `Defs.lean`, `Commitment.lean`, and `NP.lean` directly at the same pin in [Shilun-Allan-Li/tcslib](https://github.com/Shilun-Allan-Li/tcslib/tree/0c348ff94cacf24d96d99078c9dd9e328530c8d2/TCSlib/Cryptography/ZeroKnowledge). They were used to resolve interfaces and check the requested P11/headline dependencies, not to expand the audit into unrelated gates. Locations below are file-relative line numbers, not bundle line numbers; `ThreeColoring/` abbreviates `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/`.

In the quantitative entries, `n` is the vertex count, `m` the ordered-edge count, `N = n²` the length of a valid graph encoding, and `K = n m` the active iteration/attempt count. Rows 1–6 are findings; the remaining notes give admission verdicts, adversarial tests, repair checks, inventory dispositions, and exhaustive grouped declaration coverage. A grouped statement assessment applies to each listed declaration; exceptions are explicitly identified. An **a** verdict does not certify that a supplied sketch is already correct or that a `sorry` has been filled.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix | Sorry verdict |
|---|---|---|---|---|---|---|
| 1 | major | `ThreeColoring/Simulator.lean:733–760` · `col_zk` proof sketch | The advertised hiding-loss calculation uses the false inequality `n m ≤ N`, where `N = n²` and `m = edgeCount G`. The theorem has no explicit error formula, so this is a repairable defect in its load-bearing sketch, not a counterexample to its Lean conclusion. | Take the symmetric triangle: `n = 3`, `m = 6`, `N = 9`, but the simulator makes `n m = 18` attempts. More generally, the properly 3-coloured complete tripartite graph with three parts of size `t` has `n = 3t`, `m = 6t²`, `N = 9t²`, and `n m / N = 2t`. Thus step (4), `n m ε_B(n) ≤ N ε_B(√N)`, does not follow from the stated hiding bound. `exists_colSimRed_ge` really loses the number of attempts. | Use `n m ≤ n³ ≤ N²` for `n ≥ 1`, and replace the leading term by `N² ε_B(⌊√N⌋)`, or explicitly enlarge the negligible hiding bound by the missing polynomial before naming it. Handle `N = 0` separately. Keep the additional repair in row 2. No change to the qualitative `col_zk` statement is needed. | a (statement); sketch defective |
| 2 | major | `ThreeColoring/Simulator.lean:551–580, 729–760` · `exists_colSimRed_ge` → `col_zk` | The concrete reduction is an ideal finite-space sampler; the sketch does not validly identify it with a strict fair-bit `NUPPT` reduction. | `colSimRed` samples an attempt table containing independent `Fin m` indices and `Equiv.Perm (Fin 3)` permutations. For positive attempt count its full coin-space cardinality contains a factor 3, whereas a fixed-length fair-bit tape has cardinality `2^b`. Consequently the claimed equality “up to the coin bijection” cannot hold for those coin spaces. `NUPPT.exists_split` only splits bit tapes; the already-accounted sampling error for `colSim` does not supply this separate reduction bridge. The concrete theorem itself is correctly stated and does not claim machine efficiency. | One lossless repair is to fix all auxiliary coins of `colSimRed` as non-uniform advice: if its signed acceptance gap is the average of gaps at fixed auxiliary coins, its absolute value is at most the largest absolute fixed-coin gap. Choose that table at each vertex count, together with the worst instance, witness, bounded auxiliary input, hybrid index, edge, permutation, and distinguisher advice. Its size is polynomial because there are at most `n³` attempts. Prove polynomial-time evaluation on this encoded advice and give a bound including encoding overhead. Alternatively rejection-sample the reduction and propagate its own approximation error through the attempt loss. Neither repair requires an extra cryptographic hypothesis. | a (statement); bridge missing |
| 3 | minor | `ThreeColoring/Simulator.lean:674–682` · `Negligible.comp_sqrt` docstring | The threshold printed in the sketch does not imply the inequality used next. | The sketch chooses `N ≥ max ((n₀ + 1)², 4^c · 4)` and then needs `⌊√N⌋ ≥ 4^c`. At `c = 3`, `n₀ = 1`, `N = 256`, the premise holds but `⌊√N⌋ = 16 < 64`. The theorem is true; the adjacent implementation chooses the squared maximum instead. | State `K = max(n₀, 4^c, 1)` and `N ≥ K²`, matching the actual threshold. Then `N < (n+1)² ≤ 4n²` and `N^c ≤ 4^c n^(2c) ≤ n^(2c+1)` are justified. | — |
| 4 | minor | `ThreeColoring/Language.lean:303–306` · `sampleEdgeIdx` docstring | The strict upper inequality for the rejection-sampling bit width is wrong at powers of two. | For positive `m`, Lean's `Nat.size m` is the bit length. If `m = 2^j`, then `2^(Nat.size m) = 2m`, including `m = 1`. The claimed `2^k < 2m` therefore fails. The proved sampler theorem correctly uses `2^k ≤ 2m`, which still gives acceptance probability at least `1/2`. | Replace the strict upper inequality by `≤ 2m` and explicitly attach this description to `m > 0`. Keep the total default at `m = 0`. | — |
| 5 | minor | `ThreeColoring/Simulator.lean:631–638` · `colSim` deviation note | Truncation at `n m` attempts is attributed as a departure from Algorithm 128.7, although the source already includes that cutoff. | Attached source, book p. 128 / PDF p. 140, Algorithm 128.7 steps 4–5 explicitly stop after at most `n\|E\|` attempts and output failure. The formal cutoff is faithful; the difference is fair-bit sampling and the declared protocol model, not replacement of an unbounded loop in this particular algorithm. | Remove “instead of restarting until success” from this attribution. Retain the strict-PPT description and distinguish this simulator from any unbounded rewinding presentation elsewhere. | — |
| 6 | minor | `briefs/pass-shelat/DESIGN.md` · D8, §2.15, §5 item 11; `inventory-ch4.md` · Thm-124.1 / Claim-124.d | The audit records are not fully synchronized with the repaired interfaces and the computational 3COL result. | D8 and §5 item 11 call both GI and 3COL statistical ZK. Here the 3COL conclusion is computational `ZK`, relying on computational commitment hiding. The §2.15 signature block still omits the message bound in `InteractiveProof.complete` and the `boundedP` field of `EfficientProverProof`. The inventory's form-(A) prose omits `hLR` and overstates a single ZK proof; the pinned `NP.lean` explicitly separates one-iteration ZK from repeated soundness under DQ5. These are record defects, not failed repairs in the current Lean statements. | Update the records to the current signatures, distinguish GI statistical ZK from 3COL computational ZK, and retain `hLR`, length-regular nonshrinking Levin reductions, and the DQ5 composition debt in the headline description. | — |
| 7 | note | `ThreeColoring/Protocol.lean:838` · `R3COL_witnessRelation` | True as stated and provable from the definitions; this admission does express a genuine polynomially bounded, polynomial-time witness relation. | For `x = encGraph G` and `y = encColoring c`, lengths are `n²` and `2n`, with `2n ≤ 2n²` also valid at `n = 0`. The decision procedure first checks that both words equal the re-encodings of their decoded values, then checks `c(u) ≠ c(v)` at every set matrix entry. Canonical re-encoding excludes nonsquare graph words, excess/short witnesses, and the unused colour code `11`. There are only `n² ≤ length(x)` edge checks; no search for a colouring is required. | Fill the admission with this decider and its polynomial-time certificate. | a |
| 8 | note | `ThreeColoring/Protocol.lean:914` · `colRep_efficientProverProof` | True as stated under the declared D8/D10 model; the efficient prover receives the witness as its auxiliary input. | The protocol has `K = n m ≤ N²` active iterations within `4N²` moves, with fresh disjoint coin blocks. Binding fixes a partial colouring after each commitment, so conditional acceptance is at most `1 − 1/m` for an ideal fresh challenge. Multiplication gives `(1 − 1/m)^K ≤ exp(−n)`. Replacing all edge samplers adds at most `K 2^(−N) ≤ N² 2^(−N)`. Add a positive negligible `2^(−N)` for the strict rejection inequality. Invalid encodings and noncolourable one-vertex graphs reject outright; edgeless graphs are yes-instances. The new uniform message bounds supply both completeness and `boundedP`. | Fill the execution/history bookkeeping and the product-distribution comparison. Phrase the latter as statistical replacement or coupling, rather than “conditioning on samplers being uniform.” | a |
| 9 | note | `ThreeColoring/Simulator.lean:764` · `col_zk` | The computational ZK assertion is provable from `Commitment`; rows 1–2 identify repairs needed in the proposed argument. Its source comparison is restricted to the explicitly declared polynomial-auxiliary-input D8 formulation. | The quantifiers are `∀ V′ efficient, ∃ S uniform, ∀ Lz D, ∃ negligible ε, ∀ x y z` with `R3COL x y` and `length(z) ≤ Lz(length(x))`. The simulator precedes the auxiliary-input bound and distinguisher. Literally, `V′.Efficient` supplies a uniform next-message machine; polynomial non-uniform verifier advice is represented as part of `z`, while `D` is directly an arbitrary `NUPPT`. A uniform wrapper can read that advice from `z`; no separate native non-uniform-strategy equivalence theorem is supplied. For positive edge count, the ideal chain is real view → truncated full-colouring hybrid → truncated partial-colouring hybrid → simulated view, using the proven conditional-law and hybrid lemmas. For zero edges, only the unopened commitment vector changes and multi-value hiding applies. The explicit simulator is strict polynomial time. Literal unrestricted `z` on the source page is not what this predicate states. | Repair rows 1–2 and fill the admission. Preserve the explicit D8 restriction; do not advertise a literal all-length-auxiliary-input theorem or ZK of the repeated protocol. | b (true in declared D8 scope; weaker than literal all-z source) |
| 10 | note | Adversarial instantiation · challenge outside the graph | An arbitrary malicious challenge cannot select a nonedge in the formal protocol. | For `m > 0`, every word `w` decodes to `length(w) mod m < m`; `edgeAt_adj` ensures the selected endpoints form an actual ordered edge. Thus even a word purporting to encode a nonedge, or a very long word, is totalized to a legal edge. In the full-colouring hybrid this index remains independent of the guessed edge, giving success probability exactly `1/m`. This is an encoding convention, not a premise that the adversary follows the honest syntax. | None. | — |
| 11 | note | Adversarial instantiation · edgeless, empty, malformed, and looped inputs | The exceptional cases do not falsify either proof-system admission or the ZK statement. | An edgeless graph is colourable by a constant assignment; the verifier accepts and the simulator uses its all-zero-commitment branch. A nonsquare-length word fails `colWellFormed`. A one-vertex loop is a no-instance and is rejected by `2 ≤ n`; loops at larger vertex counts cannot pass binding with two different padded colours. At the empty graph, the simulator has zero allocated blocks despite taking attempt 0, so its encoded verifier tape may differ from the real tape if `V′.coinLen 0 > 0`. This is a real finite-length mismatch, not an exact-law claim: ZK permits error at `N = 0`, and the displayed exponential term equals 1 there. | Keep the separate zero-length case in the `col_zk` fill; an exact-law assertion at that length would require extra coins. | — |
| 12 | note | Adversarial instantiation · advice-controlled repetitions and long auxiliary input | The simulator's efficiency does not rely on advice bounding the number of trials. | `colIterations x = n m` depends only on the decoded graph; `n ≤ N`, `m ≤ N`, hence `K ≤ N²` on every word, including malformed ones. `exists_colSimulator` produces a uniform machine, and `colSimCoins` depends only on `N`, the fixed commitment polynomial, and `V′.coins`. The existential polynomial bound `Lz` constrains inputs for the security assertion and the non-uniform hiding reduction, not the simulator's loop. A verifier sending an arbitrarily long challenge is still polynomial in its supplied activation input; with honest bounded commitments and polynomial `z`, that input is polynomial in `N`. | None. | — |
| 13 | note | Adversarial instantiation · missing witnesses in a Levin reduction | Run-3a P11-1 is repaired in the pinned contextual `NP.lean`. | The old counterexample uses identity instance reduction from `(L3COL, False)` and the constant empty witness map. Witness preservation alone is vacuous, while the resulting constant colouring fails on a graph with an edge. The current transfer theorems and both form-(A) wrappers require `hLR : ∀ x ∈ L, ∃ y, R x y`, excluding this instance. The NP wrappers obtain that fact from `WitnessRelation.mem_iff`. The source-strength correction of P11-2 and the ordered-edge convention of P11-3 are also present; they are not reopened. | None. | — |
| 14 | note | `ThreeColoring.lean`; contextual `ZeroKnowledge/NP.lean:584–645` · headline and dependency accounting | The tied form-(A) theorem has the advertised conditional, two-protocol conclusion, not the full source theorem for one protocol. | It needs a commitment (or the OWP-to-commitment theorem), an explicit polynomial-time witness-preserving reduction with exact polynomial output length and nonshrinking parameter, and `hLR`. Its repeated-proof conjunct directly consumes `colRep_efficientProverProof`; its ZK conjunct consumes `col_zk`; its single-round-error conjunct is proved independently of those admissions. `R3COL_witnessRelation` is a separate NP-membership admission and is not referenced by these form-(A) bodies. DQ5 explicitly reserves sequential ZK composition for ch. 7; string-level Levin NP-hardness remains an assumption for the universal-NP form. Consequently neither the facade nor form (A) proves the literal full Thm 124.1 yet. | Keep the two live admission dependencies distinct from the separate witness-relation admission and retain the explicit composition and NP-hardness qualifications. | — |
| 15 | note | `evidence/g/{replay.log,axioms.log,admissions.txt,lint.log}` | The numerical attestations reconcile with the supplied files; they remain maintainer execution evidence. | There are 115 distinct replayed modules, all `rc=0`, 0 errors, and 21 sorry warnings. The axiom list has 258 distinct public-theorem entries: 252 with only the standard axioms (or none), and 6 with `sorryAx`: `R3COL_witnessRelation`, `colRep_efficientProverProof`, `colRep_interactiveProof`, `col_zk`, `col_hvzk`, `col_zeroKnowledgeProof`. The three direct admissions match `admissions.txt`. Thus the gate-03l attestation repair covers every public theorem, including machine helpers; this is not just a headline-only list. No Lean/lake executable or complete replay tree was supplied locally, so I did not independently re-run elaboration. | Fill gates must replace the three admissions and refresh the dependency evidence; this statement audit is not a fresh kernel replay. | — |
| 16 | note | `evidence/g/lint.log`; `policy.md` §§2–3 | The 20 disclosed style findings are not additional mathematical failures. | Source-derived claims carry precise PS10 locations, and technical encoding/machine glue is identifiable as such. The lint list includes missing module headings, four undocumented recursion equations, and missing explicit sketch labels or sketches; several flagged docstrings already describe the construction. Some definitions and proved glue are shadowed or duplicated in named internal namespaces, as the module documentation discloses. This audit does not certify a separate human duplication-approval ledger or review tactic-level reuse. | Resolve the disclosed documentation flags and retain the duplication accounting required by policy; no new theorem-strength finding is inferred from the lint count. | — |
| 17 | note | `inventory-ch4.md` · Thm-124.1, Def-124.a, Claim-124.d | Only the explicitly conditional, DQ5-scoped forms are represented; the current Lean signatures are more qualified than the inventory prose. | The Levin-reduction structure supplies instance and witness maps, polynomial-time evaluation, language preservation, witness preservation, exact length regularity, and nonshrinking length. Transfer of proof-system completeness additionally uses `hLR`; transfer of ZK uses the auxiliary-input simulation. Form (A) combines repeated soundness with single-iteration computational ZK. See rows 6 and 13–14 for the verified repair and source-strength limitation. | None. | — |
| 18 | note | `inventory-ch4.md` · Claim-124.b, Claim-124.c, Claim-124.e | Explicitly deferred, not silently formalized by this gate. | String-level NP-hardness of 3COL and the polynomial-time witness map from 3SAT are not proved here; the general-one-way-function variant is also deferred. The relation admission supplies NP membership only. The attached source's broader Thm 124.1 is therefore not licensed by these rows alone. | None. | — |
| 19 | note | `inventory-ch4.md` · Def-124.f, Claim-125.a, Prot-127.5 | Faithful with the declared graph and sampling conventions. | The language requires canonical adjacency encodings and proper three-colour witnesses. Boolean relations generalize simple graphs; ordered pairs double the edge count on symmetric loopless inputs. The numerical exponential bound is correct. The protocol uses `n m` active iterations, two-bit colours padded to the vertex security parameter, explicit opening checks, rejection-sampled choices, and total edge-index decoding. The helper documentation exception is row 4. | None. | — |
| 20 | note | `inventory-ch4.md` · Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6 | Completeness, binding-based bad edges, and ideal adaptive soundness are represented correctly; the end-to-end repeated proof remains an admission. | Proper colouring and permutation injectivity give every honest opening. Binding plus `n ≥ 2` makes each padded colour unique, and a noncolourable graph has a bad edge for every partial colouring. The adaptive escape inequality and its application permit arbitrary previous-challenge dependence. Repetition and sampling costs give row 8. `col_zeroKnowledgeProof` assembles separate single-round ZK and repeated soundness; it does not assert repeated ZK, as DQ5 declares. | None. | — |
| 21 | note | `inventory-ch4.md` · Alg-128.7, Claim-128.a, Prop-128.8 | The simulator algorithm and its strict efficiency are represented; the computational-security admission needs the two sketch repairs. | The machine tries the correct graph-dependent number of attempts, returning the first successful encoded view and defaulting to failure. Its efficiency theorem is unconditional on any hiding or soundness argument once `Com` and the verifier are efficient. `col_zk` is the declared D8 formulation of Prop-128.8; rows 1–2, 5, and 9 state the limitations precisely. | None. | — |
| 22 | note | `inventory-ch4.md` · Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d | The ideal finite-distribution statements are faithful and have the necessary hypotheses. | Permutations biject with ordered unequal colour pairs, giving equal laws for the ideal S/S′ attempts and truncations. With `m > 0` and nonempty verifier coin space, S″ fails with probability `(1−1/m)^K` and conditioned success has the ideal honest-view law. The hybrid reduction loses exactly `K` and plants a worst edge/permutation without an extra `6m` loss. These exact finite-space results must not be silently read as fair-bit machine identities; that remaining bridge is row 2. | None. | — |
| 23 | note | `ThreeColoring/Language.lean` · `ProperColoring` (L85); `ThreeColorable` (L93); `Graph.ofSimpleGraph` (L96); `threeColorable_ofSimpleGraph_iff` (L101) | Colouring predicates and the SimpleGraph bridge have their intended meaning. | `ProperColoring` requires different colours at every true ordered adjacency entry; `ThreeColorable` existentially chooses such a map. `Graph.ofSimpleGraph` is the Boolean adjacency indicator. `threeColorable_ofSimpleGraph_iff` identifies precisely this existence claim with Mathlib colourability. Loops are consequently forbidden in a yes-instance, without needing a separate loopless hypothesis. | None. | — |
| 24 | note | `ThreeColoring/Language.lean` · `L3COL` (L111); `R3COL` (L115); `mem_L3COL_iff` (L120); `encGraph_mem_L3COL_iff` (L129) | Canonical string membership and witness existence agree with the docstrings. | `L3COL` contains encodings of some colourable graph; `R3COL` additionally requires the witness to be exactly the encoding of a proper colouring of that same graph. `mem_L3COL_iff` is the equivalence with witness existence. `encGraph_mem_L3COL_iff` identifies membership with colourability of the supplied graph; graph decoding prevents collisions across vertex counts. | None. | — |
| 25 | note | `ThreeColoring/Language.lean` · `edgeList` (L152); `edgeCount` (L158); `mem_edgeList_iff` (L161); `edgeOf` (L167); `edgeOf_adj` (L170); `exists_edgeOf_eq` (L175); `edgeAt` (L182); `edgeAt_eq_some_edgeOf` (L185); `edgeAt_adj` (L191); `edgeAt_isSome` (L196); `edgeAt_eq_none_iff` (L201) | The edge definitions and each enumeration/decoding lemma state the advertised ordered-edge facts. | `edgeList` filters the lexicographic list of all vertex pairs; `edgeCount` is its length, and `edgeOf` selects an in-range entry. `edgeAt` reduces a natural index modulo the count, then uses optional lookup. Membership is exactly adjacency; every adjacency has an index; both selections return adjacent endpoints. The in-range selections agree, and the optional selection exists exactly when the edge count is positive. | None. | — |
| 26 | note | `ThreeColoring/Language.lean` · `threeColorable_of_edgeCount_eq_zero` (L216); `edgeCount_pos_of_not_threeColorable` (L224) | The two edgeless-graph implications are correct, including zero vertices. | `threeColorable_of_edgeCount_eq_zero` supplies a constant colouring because there are no edge constraints; `edgeCount_pos_of_not_threeColorable` is its contrapositive over natural numbers. Neither asserts that every graph with an edge is noncolourable. | None. | — |
| 27 | note | `ThreeColoring/Language.lean` · `one_sub_inv_pow_mul_le_exp` (L233); `exp_neg_le_inv_two_pow` (L246); `encColor` (L254); `decColor` (L257); `decColor_encColor` (L260) | Both numerical soundness inequalities have the stated strength. | `one_sub_inv_pow_mul_le_exp` requires positive `m` and includes `n = 0`, where both sides are 1. For positive `n`, `(1−1/m)^(nm) ≤ exp(−nm/m) = exp(−n)`. `exp_neg_le_inv_two_pow` follows from `e ≥ 2`, also with equality at zero. | None. | — |
| 28 | note | `ThreeColoring/Language.lean` · `padColor` (L266); `encColor_getD_ne` (L269); `padColor_injective` (L276); `sampleIdx` (L290); `perm3Equiv` (L294) | Colour encodings and the injection hypothesis match their mathematical use. | `encColor` is the two-bit one-vertex colouring word; `decColor` reads its first two positions with the total modulo-three convention. `padColor` keeps/truncates that word to `n` bits and pads with zeros. The decoder is a left inverse on encoded colours; distinct valid colours differ in a first-two-bit position; padding is injective when `n ≥ 2`. No injection at security parameters 0 or 1 is claimed. | None. | — |
| 29 | note | `ThreeColoring/Language.lean` · `samplePerm3` (L300); `sampleEdgeIdx` (L306); `sampleEdgeIdx_lt` (L310); `edgeMsg` (L317); `edgeIdxOfMsg` (L321); `edgeIdxOfMsg_edgeMsg` (L324); `edgeIdxOfMsg_lt` (L328) | The sampler and challenge definitions are correct; the bit-width prose exception is row 4. | `sampleIdx` scans `T` consecutive `k`-bit windows and returns the first in-range value. `perm3Equiv` chooses an enumeration of the six permutations; `samplePerm3` maps accepted samples through it and defaults to identity. `sampleEdgeIdx` samples using `Nat.size m` and defaults to zero, which is in range when `m > 0`. `edgeMsg` writes a unary index; `edgeIdxOfMsg` uses only length modulo `m`. Its inverse and in-range lemmas carry exactly the required positive/range hypotheses. | None. | — |
| 30 | note | `ThreeColoring/Language.lean` · `tapeEquiv` (L333, private); `ofFn_getD_tape` (L344, private); `sampleIdx_ofFn` (L354, private) | The private tape conversion and its two reading identities are faithful. | `tapeEquiv` curries a `T k`-bit tape into a table of trials using the product-index bijection. `ofFn_getD_tape` identifies a table entry with the corresponding list position. `sampleIdx_ofFn` therefore identifies the tape sampler with rejection sampling on that table, without claiming that rejection sampling itself is a bijection. | None. | — |
| 31 | note | `ThreeColoring/Language.lean` · `statClose_samplePerm3` (L368); `statClose_sampleEdgeIdx` (L390) | Both statistical-distance statements correctly include the rejection failure. | The permutation sampler is within `4^(−T)` of the ideal uniform permutation and the positive-size edge sampler is within `2^(−T)` of a uniform index. These are inequalities, not exact-uniformity statements. At zero trials their bound is 1, so the deterministic defaults cause no contradiction. | None. | — |
| 32 | note | `ThreeColoring/Machines.lean` · `ptc_congr` (L78); `ptc_comp` (L87) | The two closure facts agree with their descriptions. | `ptc_congr` transfers polynomial-time computation across pointwise equality; `ptc_comp` closes polynomial-time functions under composition. Both retain the computation hypotheses and introduce no claim about arbitrary functions. | None. | — |
| 33 | note | `ThreeColoring/Machines.lean` · `polyTimeComputable_loopState'` (L95); `flatMap_range_ite` (L135); `polyTimeComputable_flatMap_range` (L151) | The loop and emitted-output claims have sufficient growth hypotheses. | `polyTimeComputable_loopState′` assumes a polynomial bound along every relevant orbit and a unary polynomial-time iteration count. `flatMap_range_ite` keeps precisely the chunks with indices below both bounds. `polyTimeComputable_flatMap_range` assumes polynomial-time chunks on unary indices and a unary polynomial-time range; the polynomial number of polynomial-length chunks makes the total output polynomial. The prime in the actual first identifier is ASCII. | None. | — |
| 34 | note | `ThreeColoring/Machines.lean` · `iterSnd_poly` (L181); `ilayout` (L213); `efficient_of_polyTime` (L220) | Projection iteration and the efficiency bridge match their docstrings. | `iterSnd_poly` repeatedly applies a length-nonincreasing projection a unary polynomial number of times. `ilayout` encodes the parameter, common input, auxiliary input, received messages, empty advice, and tape. `efficient_of_polyTime` requires equality with a polynomial-time evaluator on this layout and then supplies a uniform strategy implementation; it does not infer efficiency merely from a polynomial coin count. | None. | — |
| 35 | note | `ThreeColoring/Machines.lean` · `argX` (L229); `argZ` (L232); `argM` (L235); `argX_ilayout` (L238); `argZ_ilayout` (L243); `argM_ilayout` (L248); `inCoins_ilayout` (L253); `argX_poly` (L258); `argZ_poly` (L262); `argM_poly` (L266); `zeros_poly` (L272) | The layout projections and their equations are accurate. | `argX`, `argZ`, and `argM` select respectively the common word, auxiliary word, and encoded received-history word. Their layout equations recover exactly those fields; `inCoins_ilayout` recovers the tape. Their three polynomial-time theorems follow the same projections. `zeros_poly` outputs a zero word of a length already available in unary polynomial time. | None. | — |
| 36 | note | `ThreeColoring/Machines.lean` · `padTo` (L283); `padTo_poly` (L286); `length_padTo` (L292); `getD_padTo` (L296); `ofFn_padFin` (L307); `ofFn_getD_add` (L318) | Padding is truncating zero extension, not an unbounded append. | `padTo L w` takes the first `L` bits after appending `L` zeros. Its output length is exactly `L`; every position below `L` is the original bit with false default. `ofFn_padFin` identifies the typed and string padding, and `ofFn_getD_add` identifies a tape window with padding after a drop. `padTo_poly` assumes its requested length is unary polynomial time. | None. | — |
| 37 | note | `ThreeColoring/Machines.lean` · `countTrue` (L328); `countTrue_zero` (L332); `countTrue_succ` (L334); `countTrue_le` (L338); `countTrue_mono` (L347); `countTrue_poly` (L360) | The bit-count recurrence and all its bounds match the intended prefix count. | `countTrue x j` sums the truth indicators of positions below `j`, with false default beyond the word. The zero and successor equations state that recurrence; `countTrue_le` bounds it by `j`, and `countTrue_mono` enlarges the scanned prefix. `countTrue_poly` assumes polynomial-time input and unary bound, so emitting the count is polynomial time. The two recursion equations lack docstrings, as the supplied lint records. | None. | — |
| 38 | note | `ThreeColoring/Machines.lean` · `nthTrue` (L395); `nthTrue_poly` (L400); `filter_range_succ` (L415); `length_filter_range` (L421); `getElem?_filter_range` (L431); `exists_nth_set` (L452); `nthTrue_spec` (L474); `getElem?_filter_range_nthTrue` (L486) | Selection by rank has the stated success and failure conventions. | `nthTrue x N e` is the first set position below `N` with exactly `e` earlier set positions, defaulting to `N`. Its computation theorem assumes unary polynomial-time bounds and rank. Filtering a range appends its last position exactly when that bit is set; the filter length equals `countTrue`. The lookup theorem, existence theorem, specification, and lookup-at-`nthTrue` theorem all retain the needed in-range or count hypotheses. | None. | — |
| 39 | note | `ThreeColoring/Machines.lean` · `flatMap_range_mul` (L495); `map_product_finRange` (L509); `map_edgeList` (L527); `edgeCount_eq` (L539); `edgeOf_val` (L547); `decGraph_apply` (L569); `encGraph_decGraph_eq_take` (L573) | The graph/word enumeration identities agree with the encoding. | `flatMap_range_mul` and `map_product_finRange` identify row-major pair indices with a consecutive range. `map_edgeList` filters those indices by matrix bits; `edgeCount_eq` counts them and `edgeOf_val` decodes their quotient and remainder. `decGraph_apply` supplies the required matrix-bit equation. `encGraph_decGraph_eq_take` re-encodes exactly the first `floor(sqrt(length(x)))²` bits, which also explains the well-formedness test. | None. | — |
| 40 | note | `ThreeColoring/Machines.lean` · `natOfBits` (L592); `natOfBits_zero` (L596); `natOfBits_succ` (L598); `natOfBits_lt` (L602); `bitsToNat_eq_natOfBits` (L611); `natOfBits_poly` (L627) | The window value and unary-computation claim have the necessary exponential-size guard. | `natOfBits` reads a window most-significant-bit first by doubling and adding the next bit. Its zero/successor equations, upper bound `< 2^k`, and equality with `bitsToNat` express this value. `natOfBits_poly` additionally requires a polynomial majorant for `2^k`, so it does not claim polynomial-time unary output for unrestricted binary integers. The two recursion equations lack docstrings, as disclosed. | None. | — |
| 41 | note | `ThreeColoring/Machines.lean` · `findSome?_finRange_eq` (L661); `firstTrial` (L689); `sampleVal` (L693); `map_val_sampleIdx` (L698); `map_val_sampleIdx_getD` (L714); `sampleVal_poly` (L723) | First-accepted-trial semantics and the sampler implementation statements agree. | `findSome?_finRange_eq` returns the value at the first accepted index or none. `firstTrial` searches for a window value below `m`; `sampleVal` returns that value or the supplied default. The two `map_val_sampleIdx` identities equate this numeric procedure with the typed optional sampler and its default. `sampleVal_poly` retains unary bounds and the polynomial upper bound on `2^k`; it makes no exact-uniformity claim. | None. | — |
| 42 | note | `ThreeColoring/Machines.lean` · `permTable` (L757); `tableOfIdx` (L762); `tableOfIdx_perm3Equiv` (L769); `permTable_samplePerm3` (L774); `tableOfIdx_poly` (L786); `colorFromTable` (L802); `encColor_eq` (L806); `colorFromTable_permTable` (L810); `colorFromTable_poly` (L815) | The finite colour-permutation lookup agrees with the typed sampler. | `permTable` concatenates the two-bit images of colours 0, 1, 2. `tableOfIdx` selects one of six such tables and uses identity outside the range. Its index equation and sampler equation match that default. `colorFromTable` reads the indicated two positions, and its permutation-table equation returns the image colour. `encColor_eq` gives the quotient/remainder bits. Both lookup computation theorems require unary polynomial-time indices. | None. | — |
| 43 | note | `ThreeColoring/Machines.lean` · `colorVal` (L826); `decColoring_val` (L830); `decColor_val` (L845); `colorVal_poly` (L850); `encColorOfVal` (L864); `encColor_eq_ofVal` (L867); `encColorOfVal_poly` (L870) | Numeric colour conversion is total and correctly constrained where it describes an actual colour. | `colorVal` reads two bits and reduces their value modulo 3; the two decoder-value equations match this convention. `encColorOfVal` writes the quotient/remainder tests for a natural number; only the theorem on `Fin 3` identifies it with a genuine colour encoding. Both computation claims are polynomial time on unary indices/values. They do not assert an inverse on arbitrary naturals. | None. | — |
| 44 | note | `ThreeColoring/Machines.lean` · `pairEncode_eq_append_nil` (L882); `encodeMsgs_eq_flatMap` (L887); `ofFn_eq_map_range` (L894); `iterate_pairSndD_encodeMsgs` (L903); `encodeMsgs_eq_nil_iff` (L917); `length_le_length_encodeMsgs` (L924); `getD_eq_pairFstD_iterate` (L934); `getLastD_eq_getD` (L940) | The message-list encoding identities have their advertised directions and defaults. | `pairEncode_eq_append_nil` separates a self-delimiting first component from the second. `encodeMsgs_eq_flatMap` concatenates those delimiters; `ofFn_eq_map_range` replaces typed indexing by a matching natural-index extension. Iterated second projection drops that many messages, empty encoding is equivalent to empty history, and history count is bounded by encoded length. The defaulted element and last-element equations use empty-word default, including empty histories. | None. | — |
| 45 | note | `ThreeColoring/Machines.lean` · `histLen` (L945); `histLen_encodeMsgs` (L949); `histLen_poly` (L962); `encodeMsgs_ofFn_eq_flatMap` (L970); `edgeAt_eq_some_of_pos` (L976) | The history counter and final reading lemmas are accurate. | `histLen` finds the first iterated second projection equal to the empty word, searching below encoded length plus one. On encoded histories it is exactly the number of messages and is unary polynomial time. `encodeMsgs_ofFn_eq_flatMap` states the typed-to-natural-index encoding identity under matching values. `edgeAt_eq_some_of_pos` expresses optional decoding as the edge at the index modulo its positive count. | None. | — |
| 46 | note | `ThreeColoring/Parties.lean` · `ptc_apply_unary` (L55); `length_pairSndD_le` (L62); `length_argX_le` (L66) | The unary-index substitution and layout-size bounds are correctly stated. | `ptc_apply_unary` substitutes a unary polynomial-time index into a polynomial-time evaluator on encoded index/data pairs. `length_pairSndD_le` and `length_argX_le` bound their respective projections by the original word length. | None. | — |
| 47 | note | `ThreeColoring/Parties.lean` · `nOf` (L75); `LOf` (L78); `mOf` (L81); `tblOf` (L84); `colBits` (L88); `blk` (L92); `comAt` (L96); `commitStr` (L100); `openStr` (L104); `proverStr` (L111) | The string prover components implement the typed prover, with the witness in the auxiliary slot. | `nOf` is the square-root vertex count; `LOf` evaluates the commitment randomness polynomial there; `mOf` counts set matrix bits. `tblOf` samples a colour-permutation table, `colBits` applies it to a decoded witness colour, and `blk` reads the vertex randomness with padding. `comAt` commits to that padded colour; `commitStr` encodes all vertex commitments. `openStr` opens the edge indexed by the first challenge length modulo the count. `proverStr` sends commitments on empty history, an empty opening when there are no edges, and that opening otherwise. `openStr` alone is total even outside its intended positive-edge use. | None. | — |
| 48 | note | `ThreeColoring/Parties.lean` · `nOf_poly` (L115); `LOf_poly` (L119); `mOf_poly` (L123); `tblOf_poly` (L127); `colBits_poly` (L135); `blk_poly` (L141); `comAt_poly` (L156); `commitStr_poly` (L162); `openStr_poly` (L167); `proverStr_poly` (L182) | Each prover-component computation theorem matches its documented function. | The count, randomness length, edge count, permutation table, permuted colour, randomness block, vertex commitment, complete commitment message, opening, and prover activation are polynomial-time functions in the declared layouts. The commitment-related claims explicitly require polynomial-time `Com`; the opening requires no further commitment evaluation. Indexed components use unary vertex indices. | None. | — |
| 49 | note | `ThreeColoring/Parties.lean` · `eOf` (L189); `eOf_poly` (L193); `checkStr` (L207); `checkStr_poly` (L218) | The challenge and check computations agree with their uses in the protocol. | `eOf` is the rejection-sampled numeric edge index with default zero; its unary computation theorem uses the polynomial bound on the sampling width. `checkStr` decodes the two opening colours/randomness strings, locates the numerically indexed set bit, checks both commitments and randomness lengths, and requires unequal colours. It does not independently verify that arbitrary parameters `n,m,x` describe a graph with an edge; the bridge to `colVerify` supplies that condition. `checkStr_poly` correctly assumes all word inputs and unary parameters are polynomial time. | None. | — |
| 50 | note | `ThreeColoring/Parties.lean` · `verdictStr` (L258); `verdictStr_poly` (L265); `verifierStr` (L279); `verifierStr_poly` (L286) | The one-iteration verifier dispatch and decision match their descriptions. | `verdictStr` tests canonical graph length, then accepts no-edge graphs or checks an opening when there are at least two vertices. `verifierStr` sends false on empty history, the challenge on one received message, the verdict on two, and false later. Their computation theorems require only polynomial-time `Com` beyond the established component routines. | None. | — |
| 51 | note | `ThreeColoring/Parties.lean` · `proverCoinsOf` (L296); `proverRepStr` (L301); `proverRepStr_poly` (L312) | The repeated prover reconstructs the correct one-round layout. | `proverCoinsOf` is `3N + N ℓ(N)`. `proverRepStr` uses half the received-history count as iteration index, cuts that coin block, and passes either no challenge or the last received message according to parity; after `n m` iterations it sends empty. `proverRepStr_poly` asserts polynomial-time evaluation of exactly that function. | None. | — |
| 52 | note | `ThreeColoring/Parties.lean` · `eRep` (L338); `eRep_poly` (L343); `checkRep` (L364); `checkRep_poly` (L369) | The repeated verifier reads independent slices and the intended message pair. | `eRep` samples the index from the iteration's fixed-length coin block. `checkRep` checks history positions `2t` and `2t+1` using that challenge. Both indexed computation theorems use unary `t`, and `checkRep_poly` requires efficient `Com`. | None. | — |
| 53 | note | `ThreeColoring/Parties.lean` · `verdictRepStr` (L382); `verdictRepStr_poly` (L388); `verifierRepStr` (L401); `verifierRepStr_poly` (L408) | The repeated verdict and activation conditions match the protocol. | `verdictRepStr` accepts a canonical edgeless graph or, with `n ≥ 2`, requires the bounded search to find no failed iteration. `verifierRepStr` emits active challenges on odd history counts, the final verdict at count `2N²`, and empty padding otherwise. Their computation theorems are conditional on polynomial-time `Com` and do not claim a separate soundness result. | None. | — |
| 54 | note | `ThreeColoring/Parties.lean` · `nOf_ilayout` (L431); `mOf_ilayout` (L437); `LOf_ilayout` (L442); `eOf_ilayout` (L447); `eRep_ilayout` (L454) | Each layout equality recovers exactly its declared count or challenge. | `nOf_ilayout`, `mOf_ilayout`, and `LOf_ilayout` recover vertex count, ordered-edge count, and randomness length. `eOf_ilayout` identifies the one-round sample with `sampleEdgeIdx`; `eRep_ilayout` identifies its repeated version with the same sampler on the selected coin slice. | None. | — |
| 55 | note | `ThreeColoring/Parties.lean` · `tblOf_ilayout` (L465); `colBits_ilayout` (L472); `blk_ilayout` (L479); `comAt_ilayout` (L487); `commitStr_ilayout` (L502) | Each prover layout identity matches the typed commitment construction. | `tblOf_ilayout` identifies the sampled permutation table; `colBits_ilayout` applies it to the witness colour. `blk_ilayout` recovers the vertex randomness and `comAt_ilayout` the padded-colour commitment. `commitStr_ilayout` assembles precisely the `multiCom` vector. The vertex-index claims have the needed in-range hypotheses. | None. | — |
| 56 | note | `ThreeColoring/Parties.lean` · `openStr_ilayout` (L516) | The opening equality has the necessary positive-edge hypothesis. | `openStr_ilayout` reads the first challenge, selects its index modulo the edge count, and constructs the two colour/randomness openings for that edge. Its positivity assumption prevents treating the numeric fallback for a missing edge as a real graph edge. | None. | — |
| 57 | note | `ThreeColoring/Protocol.lean` · `msgAt` (L103); `msgAt_encodeMsgs` (L106); `colCommit` (L120); `colOpen` (L126); `colVerify` (L137); `colVerify_honest` (L155) | The commitment/opening syntax and honest-opening theorem match the protocol. | `msgAt` takes the first projection after the requested number of second projections; its encoding theorem reads an in-range list entry. `colCommit` commits to every padded colour. `colOpen` packages the two colours and their randomness. `colVerify` rejects missing edges, checks both randomness lengths and commitment equations, and requires different decoded colours. `colVerify_honest` follows for any proper colouring, any colour permutation and randomness, and an actual selected edge; no hiding or binding hypothesis is necessary for completeness. | None. | — |
| 58 | note | `ThreeColoring/Protocol.lean` · `committedColor` (L174); `ofFn_getD_of_length` (L182, private); `committedColor_eq_some` (L193); `exists_bad_edge` (L217) | Partial committed colourings and their bad-edge lemma have the right semantics. | `committedColor` chooses some colour with an opening if one exists, and none otherwise; uniqueness requires the commitment hypothesis and `n ≥ 2` in `committedColor_eq_some`. The private list/`ofFn` identity converts a length-checked opening into typed randomness. `exists_bad_edge` says every partial assignment on a noncolourable graph has an edge with an undefined endpoint or equal colours. It does not assume every submitted commitment is valid. | None. | — |
| 59 | note | `ThreeColoring/Protocol.lean` · `challengesBefore` (L236); `challengesUpTo` (L241); `snocEquivW` (L246, private); `challengesBefore_snoc_castSucc` (L258, private); `challengesBefore_snoc_last` (L269, private) | The history projections and private splitting identities correctly express adaptivity. | `challengesBefore` takes the strict prefix before the indexed challenge; `challengesUpTo` includes that challenge. `snocEquivW` separates the final challenge from earlier challenges and independent auxiliary data. Its two prefix identities recover the earlier prefix and the entire previous tuple, respectively. | None. | — |
| 60 | note | `ThreeColoring/Protocol.lean` · `uprob_adaptive_escape` (L290); `uprob_col_cheat_le` (L354) | Both adaptive soundness statements agree with their docstrings. | `uprob_adaptive_escape` bounds avoidance of nonempty bad sets that depend only on previous challenges and auxiliary data. `uprob_col_cheat_le` instantiates those sets with binding-determined partial colourings and permits the opening to depend on the current challenge. Both are upper bounds and remain true when the auxiliary finite type is empty, since then the left probability is zero; no missing nonempty assumption is needed here. | None. | — |
| 61 | note | `ThreeColoring/Protocol.lean` · `colWellFormed` (L391); `colWellFormed_encGraph` (L394); `colProver` (L408); `colVerifier` (L433); `colProtocol` (L448) | Well-formedness and the one-round strategy definitions implement the stated three-message interaction. | `colWellFormed` compares the word to its decoded/re-encoded matrix, equivalently testing square length; encoded graphs pass. `colProver` samples and commits on empty received history, then answers its first received challenge using the same coin tape. `colVerifier` samples a challenge on one received message and evaluates the opening on two, with the documented special cases. `colProtocol` starts with the prover and exchanges exactly three messages. The two parties' coin polynomials are upper bounds in common-input length. | None. | — |
| 62 | note | `ThreeColoring/Protocol.lean` · `colCoinSlice` (L458); `colIterations` (L463); `colProverRep` (L468); `colVerifierRep` (L483); `colProtocolRep` (L500) | The repeated protocol has `n m` active iterations and enough padded rounds and coins. | `colCoinSlice` is a fixed-width block; `colIterations` multiplies decoded vertex and ordered-edge counts. `colProverRep` delegates alternate commitment/opening activations to the one-round prover using that block. `colVerifierRep` sends the matching sampled challenge, checks all active pairs at final history length `2N²`, and otherwise sends padding. `colProtocolRep` sets `4N²` alternating moves. For `N = 0`, the final-history test is already at zero and accepts the empty graph. | None. | — |
| 63 | note | `ThreeColoring/Protocol.lean` · `colProver_efficient` (L523); `colVerifier_efficient` (L538); `colProverRep_efficient` (L545); `colVerifierRep_efficient` (L553) | All four efficiency theorems match the declared D8 notion. | The single and repeated prover and verifier each have a uniform polynomial-time next-message implementation whenever `Com` is polynomial time. The statements do not assert polynomial work in common-input length on arbitrarily long received words. The module and theorem prose now call this efficient D8 behaviour, as the repair requires. | None. | — |
| 64 | note | `ThreeColoring/Protocol.lean` · `length_multiCom_le` (L562); `colProver_length_le` (L580); `colProtocol_proverBounded` (L605) | The new prover-message bounds are nonvacuous and sufficient for the repaired interface. | `length_multiCom_le` applies a polynomial output bound to each encoded commitment and sums the self-delimiting lengths. `colProver_length_le` bounds both a vector of commitments and a two-vertex opening for every witness word, tape and history. `colProtocol_proverBounded` gives the same polynomial for one round and repetition, for any relation. Hence it does not exploit emptiness of `R3COL` or assume bounded malicious challenges. | None. | — |
| 65 | note | `ThreeColoring/Protocol.lean` · `colVerifier_next_two_of` (L624, private); `colVerifier_next_one_of` (L635, private); `colProver_next_nil_of` (L642, private); `colProver_next_cons_of` (L653, private); `colProtocol_outV` (L667, private); `colProtocol_outV_honest` (L679, private) | The private execution-reading statements are consistent with the public strategies. | The two verifier identities read its challenge and verdict on a supplied decoded graph. The prover identities read its initial commitment and its response to a first challenge, with a positive-edge premise for the latter. `colProtocol_outV` expands exactly the three-message execution. `colProtocol_outV_honest` states acceptance on every pair of tapes for a proper colouring, not just averaged acceptance. | None. | — |
| 66 | note | `ThreeColoring/Protocol.lean` · `uprob_check_uniform_le` (L704, private); `colProtocol_sound` (L721, private) | The private single-round soundness claims have the correct ranges and errors. | `uprob_check_uniform_le` bounds the probability of passing a uniform-edge check on a noncolourable graph with at least two vertices. `colProtocol_sound` adds the fair-bit edge-sampling error, substitutes `m ≤ N`, and bounds literal rejection probability for every cheating prover. Its negative-instance premise excludes the zero-length yes-instance. | None. | — |
| 67 | note | `ThreeColoring/Protocol.lean` · `col_efficientProverProofErr` (L872) | The proved one-round efficient-proof statement has exactly the advertised, non-negligible error. | `col_efficientProverProofErr` combines polynomial-time parties, bounded honest messages, completeness for every proper-colouring witness, and error `1−1/N+2^(−N)`. It does not claim negligible soundness. For positive `N`, the error is below 1 because `N < 2^N`; the zero-length negative-instance case never occurs. | None. | — |
| 68 | note | `ThreeColoring/Protocol.lean` · `colRep_interactiveProof` (L919) | The repeated interactive-proof corollary states exactly the superclass of the admitted efficient-proof theorem. | `colRep_interactiveProof` adds no assumptions or strengthening and retains the repeated protocol. Its `sorryAx` dependence is correctly visible in the supplied axiom list. | None. | — |
| 69 | note | `ThreeColoring/ProtocolProofs.lean` · `msgAt` (L56); `colCommit` (L59); `colOpen` (L64); `colVerify` (L70); `colWellFormed` (L84); `colProver` (L87); `colVerifier` (L105); `colProtocol` (L119); `colCoinSlice` (L126); `colIterations` (L129); `colProverRep` (L132); `colVerifierRep` (L143); `colProtocolRep` (L158) | All thirteen protocol shadow definitions have the same mathematical meanings as their public counterparts. | The shadow `msgAt`, commitment, opening, check, and canonicality test perform the projections and checks described above. Its one-round prover, verifier, and protocol use the same coins, dispatch, and three moves. Its coin slice, iteration count, repeated prover, repeated verifier, and repeated protocol use the same blocks, parity tests, `n m` active iterations and `4N²` moves. Comparing their bodies found no semantic divergence; the documentation explicitly identifies them as shadows. | None. | — |
| 70 | note | `ThreeColoring/ProtocolProofs.lean` · `colProver_next_eq` (L167); `colVerify_eq_checkStr` (L189); `colVerifier_next_eq` (L204); `colProverRep_next_eq` (L252); `colVerifierRep_next_eq` (L279) | Every strategy-to-string-function bridge has the claimed equality and hypotheses. | The four `*_next_eq` theorems identify the one-round/repeated next-message functions with the corresponding `Parties` string evaluator on the full interactive layout. `colVerify_eq_checkStr` identifies the typed check with the numeric check only when the decoded graph has an edge, exactly where the numeric edge selection is valid. | None. | — |
| 71 | note | `ThreeColoring/ProtocolProofs.lean` · `colProver_efficient` (L320); `colVerifier_efficient` (L325); `colProverRep_efficient` (L330); `colVerifierRep_efficient` (L335); `two_le_of_edge` (L342) | The shadow efficiency results and the minimum-vertex fact match their docstrings. | Each of the four shadow parties is efficient when `Com` is polynomial time. `two_le_of_edge` uses both a proper colouring and an existing edge: its endpoints must be distinct, so there are at least two vertices. | None. | — |
| 72 | note | `ThreeColoring/ProtocolProofs.lean` · `pushesUniform_castLE` (L352); `ofFn_getD_lt` (L369); `sampleEdgeIdx_ofFn_castLE` (L374); `finOneEquiv` (L390) | The coin-prefix and one-round-index helpers have the required finite-space semantics. | `pushesUniform_castLE` says restriction of a uniform bit vector is uniform; `ofFn_getD_lt` reads an in-range bit. `sampleEdgeIdx_ofFn_castLE` proves the sampler ignores tape positions after its `T size(m)` trials, with that prefix fitting in the tape. `finOneEquiv` identifies one edge index with a one-element challenge tuple and unit auxiliary data. No non-dyadic sampler is asserted to be a bijection. | None. | — |
| 73 | note | `ThreeColoring/Simulator.lean` · `ColorPair` (L83); `card_colorPair` (L86); `perm3_ext_of_ne` (L89); `colorPairEquiv` (L96); `colorPairEquiv_apply` (L104) | The colour-pair type, cardinality, and permutation correspondence are correct. | `ColorPair` is the subtype of ordered unequal colours and has six elements. `perm3_ext_of_ne` determines a permutation from its values on two distinct colours. `colorPairEquiv` sends a permutation to those two images, and its application theorem states that formula. These are finite ideal-space facts, independent of any fair-bit implementation. | None. | — |
| 74 | note | `ThreeColoring/Simulator.lean` · `simColors` (L111); `simColorsW` (L116); `simColorsW_eq` (L121); `ColView` (L126) | The two partial-colouring definitions and their equality have the intended conditional meaning. | `simColors` assigns the first selected colour at the first endpoint, the second at a distinct second endpoint, and zero elsewhere. `simColorsW` uses the corresponding permuted witness colours instead. If endpoints coincide, the first branch wins; the proper-colouring applications exclude that case. `simColorsW_eq` identifies the assignments when the witness endpoint colours differ. `ColView` is the verifier tape, commitment word, and opening word, with common and auxiliary inputs fixed externally. | None. | — |
| 75 | note | `ThreeColoring/Simulator.lean` · `colRealView` (L135); `colSimAttempt` (L146); `colSimAttemptW` (L157); `colSimAttemptH` (L170) | The real view and the three ideal attempt functions match Algorithm 128.7 and its proof hybrids. | `colRealView` commits to a fully permuted witness and opens the edge chosen by the verifier, or sends empty when none exists. `colSimAttempt` commits to a random distinct pair on the guessed edge and zeros elsewhere; `colSimAttemptW` obtains that pair by permuting witness colours. `colSimAttemptH` instead commits to the full permuted witness. Each attempt succeeds precisely when the decoded verifier challenge equals its guessed index, then outputs the matching view. | None. | — |
| 76 | note | `ThreeColoring/Simulator.lean` · `simCoinsEquiv` (L182); `uprob_colSimAttemptW_eq` (L193); `firstSome` (L203); `firstSome_eq_none_iff` (L207); `colSimTrunc` (L216); `colSimTruncW` (L222); `colSimTruncH` (L228); `uprob_colSimTruncW_eq` (L235) | The S/S′ law identities and truncation definitions have the stated scope. | `simCoinsEquiv` replaces the permutation by its endpoint-colour pair separately for each guessed edge, using proper colouring. `uprob_colSimAttemptW_eq` transfers the one-attempt law through that bijection. `firstSome` selects the earliest successful optional result, and is none exactly when every entry fails. The three `colSimTrunc*` definitions apply this selector to independent attempt tables; `uprob_colSimTruncW_eq` transfers the whole truncated law. Zero attempts give failure on both sides. | None. | — |
| 77 | note | `ThreeColoring/Simulator.lean` · `uprob_colSimAttemptH_none` (L250); `uprob_colSimAttemptH_some` (L285); `uprob_colSimTruncH_none` (L324); `statClose_colSimTruncH` (L344) | The full-colouring hybrid failure and conditional-law statements are correctly quantified. | `uprob_colSimAttemptH_none` needs positive edge count and nonempty verifier coin space for the complementary failure probability. `uprob_colSimAttemptH_some` gives joint success-and-test mass as `1/m` times the honest-view test mass; when its coin type is empty both masses are zero. The truncation failure theorem uses independent draws to raise the failure probability to the attempt count. `statClose_colSimTruncH` bounds every optional-view test by that failure probability. None assumes hiding or that the witness is proper, because full-colouring sampling itself is the comparison law. | None. | — |
| 78 | note | `ThreeColoring/Simulator.lean` · `colSimHyb` (L364); `colSimHyb_zero` (L371); `colSimHyb_self` (L377); `colSimAttemptPlanted` (L387); `colSimRed` (L404) | The attempt hybrids and planted reduction agree with their mathematical descriptions. | `colSimHyb` uses full-colouring attempts before its cutoff and partial-colouring attempts afterwards; cutoff zero and cutoff equal to the attempt count give the two endpoints. `colSimAttemptPlanted` constructs the two selected endpoint commitments with known randomness and reads all other commitments from the challenge vector. `colSimRed` places this attempt at the chosen hybrid index and runs the supplied distinguisher on the first success. It is defined over arbitrary finite ideal coins, not declared as an efficient machine. | None. | — |
| 79 | note | `ThreeColoring/Simulator.lean` · `simColorsW_of_mem` (L416, private); `colSimAttemptPlanted_W` (L435, private); `colSimAttemptPlanted_H` (L486, private) | The three private planted-attempt identities have the stated meaning. | `simColorsW_of_mem` reads a permuted witness colour at either selected endpoint. `colSimAttemptPlanted_W` and `_H` identify a planted challenge with the corresponding ideal attempt after replacing randomness off the two endpoints. The known endpoint randomness is retained, which is essential for producing valid openings. | None. | — |
| 80 | note | `ThreeColoring/Simulator.lean` · `exists_colSimRed_ge` (L551) | The concrete hybrid reduction theorem matches its docstring; the machine bridge is a separate obligation. | `exists_colSimRed_ge` assumes positive edge and attempt counts and finds a hybrid index, edge, and permutation whose commitment-vector distinguishing advantage is at least the total truncated-hybrid advantage divided by the attempt count. It does not lose another factor equal to the number of edges or permutations. It also does not say this ideal reduction is a fair-bit PPT algorithm; see row 2. | None. | — |
| 81 | note | `ThreeColoring/Simulator.lean` · `colSimBlock` (L590); `colSimCoins` (L595); `pair6Equiv` (L599); `sampleColorPair` (L603); `colSimAttemptStr` (L611) | The string simulator's blocks and attempt semantics match the ideal construction up to rejection sampling. | `colSimBlock` budgets edge-sampler bits, colour-pair bits, commitment randomness and verifier coins; `colSimCoins` allocates `N²` blocks. `pair6Equiv` enumerates the six unequal pairs; `sampleColorPair` rejects out-of-range samples and defaults to `(0,1)`. `colSimAttemptStr` slices these fields, runs the verifier on the commitment, and returns the encoded view on a matching challenge. Its no-edge branch returns zero-colour commitments and an empty opening without needing a verifier challenge. | None. | — |
| 82 | note | `ThreeColoring/Simulator.lean` · `colSim` (L638); `exists_colSimulator` (L666) | The simulator and its machine-existence statement agree; the attribution issue is row 5. | `colSim` takes the first successful attempt among `n m` disjoint blocks, or an empty failure word; on no-edge inputs it uses attempt zero. `exists_colSimulator` supplies a uniform machine with exactly the declared coin polynomial and equality to this string function on every input and simulator tape. It is an efficiency/correct-evaluation theorem, not yet a distributional ZK theorem. | None. | — |
| 83 | note | `ThreeColoring/Simulator.lean` · `Negligible.comp_sqrt` (L682) | The square-root substitution theorem is true as stated; its printed threshold needs row 3. | `Negligible.comp_sqrt` says a negligible function at the vertex parameter remains negligible when evaluated at floor square root of input length. The reason is that polynomial powers of input length are bounded by slightly higher polynomial powers of its square root for sufficiently large inputs; no monotonicity of the negligible function is required. | None. | — |
| 84 | note | `ThreeColoring/Simulator.lean` · `col_hvzk` (L770); `col_zeroKnowledgeProof` (L782) | The two concluding corollaries state only the consequences actually available. | `col_hvzk` specializes general one-round ZK to the efficient honest verifier. `col_zeroKnowledgeProof` conjoins one-round efficient proof with explicit error, one-round ZK, and repeated efficient proof with negligible soundness. It does not conjoin ZK and negligible soundness for the same repeated protocol. Both still depend on admissions, as attested, and the latter explicitly records DQ5. | None. | — |
| 85 | note | `ThreeColoring/SimulatorLemmas.lean` · `uprob_ne_idx` (L62); `uprob_eq_idx_and` (L79); `AttemptCoins` (L99); `attemptCoinsEquiv` (L103); `findSome?_finRange_cons_of_some` (L114); `findSome?_finRange_cons_of_none` (L124) | The independent-index probabilities, attempt tuple, and first-success equations are correct. | `uprob_ne_idx` requires nonempty independent data and gives miss probability `1−1/m`; `uprob_eq_idx_and` gives hit-and-test mass `(1/m) Pr[test]`, including empty-data mass zero. `AttemptCoins` groups an edge, colour permutation, randomness and verifier tape; `attemptCoinsEquiv` moves the edge to the final coordinate without changing information. The two `findSome?` lemmas respectively return a successful head and skip a failed head. | None. | — |
| 86 | note | `ThreeColoring/SimulatorLemmas.lean` · `uprob_and_add_uprob_not_and` (L133); `uprob_prod_and` (L147); `mergeAt` (L162); `mergeAt_fst` (L167); `mergeAt_snd` (L172); `mergeAt_mergeAt_left` (L177); `mergeAt_mergeAt_right` (L184); `mergeAt_self` (L191); `msgAt_multiCom` (L199) | The event-splitting, independent-product, and merged-randomness statements match the docstrings. | The first probability identity partitions by an event, and the second factors events on separate coordinates. `mergeAt` takes the first randomness table at either selected endpoint and the second elsewhere. Its endpoint, repeated-merge and self-merge equations express exactly that selection, also when the endpoints coincide. `msgAt_multiCom` reads the corresponding challenge commitment from the encoded vector. | None. | — |
| 87 | note | `ThreeColoring/SimulatorLemmas.lean` · `plantEP` (L211); `swapEP` (L215); `uprob_plantEP` (L232); `swapR` (L254); `uprob_mergeAt` (L278) | Both planting constructions preserve the uniform finite law claimed by their lemmas. | `plantEP` replaces only the edge/permutation component. `swapEP` exchanges that component with an external one at one attempt; `uprob_plantEP` marginalizes this bijection, requiring positive edge count. `swapR` exchanges the external and attempt randomness off the endpoint set; `uprob_mergeAt` uses that exchange to preserve the law of the planted tuple. These are finite-space bijections and do not assert conversion from fair-bit tapes to permutations. | None. | — |
| 88 | note | `ThreeColoring/SimulatorLemmas.lean` · `truncAttempts` (L316); `uprob_truncAttempts_succ` (L329); `abs_uprob_truncAttempts_sub_le` (L372); `statClose_truncAttempts` (L405) | The generic truncated-attempt recurrence and distance lemmas agree with their hypotheses. | `truncAttempts` selects the first successful attempt from an independent table. `uprob_truncAttempts_succ` assumes failure probability `θ` and the stated joint success-law identity, then gives the one-step mixture recurrence. `abs_uprob_truncAttempts_sub_le` adds `θ ≥ 0` and bounds each test discrepancy by `θ^K`; `statClose_truncAttempts` packages that bound. Nonempty attempt space is explicit. The hypotheses are not replaced by an unjustified unconditional-success claim. | None. | — |
| 89 | note | `ThreeColoring/SimulatorLemmas.lean` · `hybStd` (L423); `hybGen` (L429); `hybGen_update` (L436); `hybGen_W` (L448); `hybGen_H` (L457) | The generic hybrid definitions and replacement equations faithfully isolate one attempt. | `hybStd` uses H before the cutoff and W afterwards; `hybGen` installs an arbitrary attempt at the cutoff and evaluates the first success with a distinguisher. `hybGen_update` changes that attempt's coins and function consistently when their values agree. `hybGen_W` and `_H` recover the adjacent standard hybrids. | None. | — |
| 90 | note | `ThreeColoring/SimulatorLemmas.lean` · `hybAcc` (L479); `uprob_hybGen_eq_uexp` (L487); `acceptProb_hybGen_planted` (L501); `exists_hybRed_ge` (L529) | The averaging and planted-challenge reduction statements have the expected quantitative loss. | `hybAcc` is the acceptance probability with the selected edge/permutation fixed. `uprob_hybGen_eq_uexp` averages these fixed values back to the original acceptance probability. `acceptProb_hybGen_planted` uses the supplied merged-randomness identity to identify the planted challenge law. `exists_hybRed_ge` then chooses an adjacent hybrid and a fixed edge/permutation with advantage at least the endpoint advantage divided by the positive number of attempts. Arbitrary finite distinguishers are allowed; machine efficiency is not concluded. | None. | — |
| 91 | note | `ThreeColoring/SimulatorNumeric.lean` · `ColorPair` (L66); `card_colorPair` (L69); `simColors` (L72); `blockPoly` (L78); `simCoins` (L82); `pair6Equiv` (L86); `sampleColorPair` (L90); `attemptStr` (L95); `sim` (L117) | The nine simulator shadows agree with their corresponding main definitions. | `ColorPair` is the unequal-pair subtype, with cardinality six; `simColors` assigns its two entries by endpoint priority and zeros elsewhere. `blockPoly` and `simCoins` are the same one-block and total budgets. `pair6Equiv` and `sampleColorPair` use the same enumeration/default. `attemptStr` and `sim` have the same edge/no-edge branches, verifier invocation, first-success search, and failure word as the public string simulator. No differing distribution is introduced by these shadows. | None. | — |
| 92 | note | `ThreeColoring/SimulatorNumeric.lean` · `bitsToNat_getD_eq_blockVal` (L128); `findSome?_range_eq` (L148); `sampleNum` (L183); `sampleIdx_eq` (L193); `sampleEdgeIdx_eq` (L217) | The numeric rejection-sampler model and search equations are accurate. | `bitsToNat_getD_eq_blockVal` identifies a window's binary value; `findSome?_range_eq` identifies first-success search with `firstIdx`. `sampleNum` is the accepted window value, with `m` as out-of-range marker if no trial succeeds. `sampleIdx_eq` reconstructs the optional typed sample using a test against `m`; `sampleEdgeIdx_eq` substitutes the edge default zero. This includes `m = 0` and zero trials without an invalid `Fin 0` value. | None. | — |
| 93 | note | `ThreeColoring/SimulatorNumeric.lean` · `colorA` (L226); `colorB` (L230); `sampleColorPair_fst` (L233); `sampleColorPair_snd` (L240) | The two colour projections match the sampled unequal pair. | `colorA` and `colorB` read the two entries of the enumerated pair below six and default to 0 and 1 respectively outside the range. `sampleColorPair_fst` and `_snd` identify the actual sampled pair with these numeric functions. No claim that the six outcomes have exactly equal fair-bit probabilities is made. | None. | — |
| 94 | note | `ThreeColoring/SimulatorNumeric.lean` · `getElem_product` (L254); `finRange_product_eq` (L294) | The list-product and row-major enumeration identities are correctly bounded. | `getElem_product` identifies an in-range product-list position with quotient/remainder positions, retaining their validity hypotheses. `finRange_product_eq` enumerates the square of vertex indices by the product-index inverse. The zero-size case is an empty list, not division into an inhabited zero-size type. | None. | — |
| 95 | note | `ThreeColoring/SimulatorNumeric.lean` · `countBits` (L310); `edgeList_eq_map` (L315); `map_val_filter_finRange` (L330); `edgeCount_eq_countBits` (L336); `countBits_lt_of_lt` (L342); `getElem_filter_range_spec` (L358) | Counting and filtered-index specifications agree with the decoded graph. | `countBits` counts true positions in a bounded range, using false default. `edgeList_eq_map` filters matrix positions and maps them to vertex pairs; `map_val_filter_finRange` removes the typed-index wrapper. `edgeCount_eq_countBits` identifies the edge count. `countBits_lt_of_lt` gives strict increase across a specified true bit, and `getElem_filter_range_spec` says an in-range filtered entry is set, in range, and has the correct number of predecessors. | None. | — |
| 96 | note | `ThreeColoring/SimulatorNumeric.lean` · `edgePos` (L402); `getElem_filter_range_eq_edgePos` (L407); `edgeOf_val_eq` (L434) | The numeric edge selector and endpoint equations have the stated success hypotheses. | `edgePos` finds the first set position below `n²` having the requested rank and defaults to `n²`. `getElem_filter_range_eq_edgePos` identifies it with a valid filtered entry. `edgeOf_val_eq` reads the corresponding endpoints by quotient and remainder, with a `Fin edgeCount` index guaranteeing an actual edge. | None. | — |
| 97 | note | `ThreeColoring/SimulatorNumeric.lean` · `encodeMsgs_eq_flatMap` (L471); `encodeMsgs_ofFn_eq_flatMap` (L481); `ofFn_getD_eq_padL` (L492) | The encoding and randomness-window equalities are correct. | `encodeMsgs_eq_flatMap` concatenates self-delimiting message chunks. `encodeMsgs_ofFn_eq_flatMap` does the same for a typed list and a matching natural-index extension. `ofFn_getD_eq_padL` identifies typed randomness read from a tape offset with zero-padding of the dropped word. | None. | — |
| 98 | note | `ThreeColoring/SimulatorNumeric.lean` · `nV` (L500); `mE` (L504); `eIdx` (L507); `vIdx` (L510); `kPos` (L514); `baseR` (L517); `rrStr` (L520); `colorNum` (L525); `chunk` (L530); `comStr` (L535) | The numeric simulator ingredients implement exactly the declared positions and fields. | `nV` is the square-root vertex count; `mE` counts matrix ones; `eIdx` is the sampled edge index; `vIdx` is the colour-pair sample read after the edge budget; `kPos` selects that edge's matrix position. `baseR` starts the commitment-randomness segment. `rrStr` reads one vertex's padded randomness; `colorNum` assigns the sampled colours to the quotient/remainder endpoints with first-endpoint priority. `chunk` self-delimits a padded-colour commitment, and `comStr` concatenates the vertex chunks. Out-of-domain inputs remain total but are not asserted to name actual edges. | None. | — |
| 99 | note | `ThreeColoring/SimulatorNumeric.lean` · `rVStr` (L540); `opnStr` (L544); `attemptNum` (L552); `colCommit_eq_comStr` (L562) | The remaining numeric outputs match the typed attempt components. | `rVStr` is the suffix after the allocated commitment randomness. `opnStr` encodes the two endpoint colours/randomness strings. `attemptNum` returns the zero-colour no-edge view, a successful guessed-edge view, or none after a mismatching challenge. `colCommit_eq_comStr` equates the typed vector with its numeric concatenation for agreeing colour functions. | None. | — |
| 100 | note | `ThreeColoring/SimulatorNumeric.lean` · `attemptStr_eq_attemptNum` (L583) | The complete numeric/typed attempt bridge is correctly stated. | `attemptStr_eq_attemptNum` is equality on every input word, auxiliary word and block, not merely well-formed graphs. The zero-edge branch and the in-range sampled-edge branch are both represented; all length-dependent indices are derived from the same decoded common input. | None. | — |
| 101 | note | `ThreeColoring/SimulatorMachine.lean` · `ptc_congr` (L58); `countBits_succ` (L65); `countBits_le` (L72); `countBits_poly` (L83) | The equality transfer and counting implementation claims are sound. | `ptc_congr` transfers polynomial-time computation across pointwise equality. `countBits_succ` adds the next indicator and `countBits_le` bounds the total by the scanned positions. `countBits_poly` assumes a polynomial-time word and unary polynomial-time scan length, so it produces a polynomial-size unary count. | None. | — |
| 102 | note | `ThreeColoring/SimulatorMachine.lean` · `table_poly` (L133); `sampleNum_poly` (L147); `flatMap_range_ite` (L160); `emitLoop_poly` (L180) | Finite lookup, sampling, and emission have the restrictions needed for unary polynomial time. | `table_poly` fixes a finite bound and looks up an arbitrary table at a clamped index; the bound is not an unbounded input table. `sampleNum_poly` requires a unary polynomial upper bound for `2^K`. `flatMap_range_ite` retains the shorter prefix of the chunk range. `emitLoop_poly` assumes the chunk evaluator and count are polynomial time and the count is at most input length plus one. These hypotheses prevent exponential output being hidden in an index. | None. | — |
| 103 | note | `ThreeColoring/SimulatorMachine.lean` · `simX` (L210); `simZ` (L213); `simR` (L216); `simX_poly` (L219); `simZ_poly` (L223); `simR_poly` (L227); `length_pairSndD_le` (L230); `length_simX_le` (L234) | The simulator-layout projections, computation lemmas, and length bounds agree. | `simX` and `simZ` split the simulator argument into common and auxiliary words; `simR` reads its coin word. Their polynomial-time lemmas assert exactly these projections. `length_pairSndD_le` and `length_simX_le` bound the projected lengths by their containing words. | None. | — |
| 104 | note | `ThreeColoring/SimulatorMachine.lean` · `blk_poly` (L246); `nV_poly` (L261); `mE_poly` (L266); `baseR_poly` (L271); `eIdx_poly` (L278); `vIdx_poly` (L292) | The block, graph-count, offset, and sample computation statements match the numeric definitions. | `blk_poly` extracts a requested block at a unary polynomial-time index. `nV_poly`, `mE_poly`, and `baseR_poly` compute the vertex count, edge count, and randomness offset in unary. `eIdx_poly` uses the bound on `2^(size m)`; `vIdx_poly` uses three-bit windows. Each retains polynomial-time component hypotheses, with no reliance on hiding or on the advice being short by accident. | None. | — |
| 105 | note | `ThreeColoring/SimulatorMachine.lean` · `kPos_poly` (L306); `p1_poly` (L324); `p2_poly` (L331); `colA_poly` (L339); `colB_poly` (L350); `colorStr_poly` (L362) | Edge endpoints and sampled-colour evaluation are polynomial time under the stated inputs. | `kPos_poly` searches the bounded matrix positions; `p1_poly` and `p2_poly` take quotient and remainder by the decoded count. `colA_poly` and `colB_poly` select from the fixed six-entry colour table. `colorStr_poly` compares the unary vertex index with the two endpoints and returns the corresponding encoded colour. The functions are total at zero vertices; correctness as an edge opening is asserted elsewhere with appropriate hypotheses. | None. | — |
| 106 | note | `ThreeColoring/SimulatorMachine.lean` · `rrStr_poly` (L376); `chunk_poly` (L392); `comStr_poly` (L405); `comStr0_poly` (L419); `rVStr_poly` (L430) | The randomness and commitment-string computation claims retain all necessary size assumptions. | `rrStr_poly` computes the padded vertex randomness. `chunk_poly` assumes the encoded requested colour is polynomial time before applying efficient `Com`. `comStr_poly` and `comStr0_poly` emit the simulated and constant-zero commitment vectors, respectively, with common-input length bounded by the evaluator's input length. `rVStr_poly` extracts the verifier tape suffix. | None. | — |
| 107 | note | `ThreeColoring/SimulatorMachine.lean` · `reply_poly` (L443); `opnStr_poly` (L456); `view_poly` (L463) | The verifier call, opening construction, and encoded view have their documented polynomial-time interfaces. | `reply_poly` invokes the uniform machine supplied by `V′.Efficient` on the computed common/auxiliary input, tape and one-message history. `opnStr_poly` builds the two endpoint openings. `view_poly` encodes two received messages together with common input, auxiliary input and verifier tape. Neither proof claim presumes the verifier responds honestly. | None. | — |
| 108 | note | `ThreeColoring/SimulatorMachine.lean` · `attemptNum_poly` (L478); `attemptAt` (L522); `attemptAt_poly` (L529) | The single-attempt implementation statements are faithful and do not smuggle in a success assumption. | `attemptNum_poly` separately supplies polynomial-time success testing and defaulted output evaluation on arbitrary supplied components. `attemptAt` applies that attempt to one block of the parsed simulator layout. `attemptAt_poly` evaluates its success bit and defaulted view at a unary attempt index. Failure remains an allowed output. | None. | — |
| 109 | note | `ThreeColoring/SimulatorMachine.lean` · `sim_eq` (L548); `sim_poly` (L583); `exists_simulator` (L610) | The loop equation and final uniform-machine theorem match the declared strict simulator. | `sim_eq` expresses the simulator by the first accepted bounded attempt, with a separate no-edge attempt. `sim_poly` proves polynomial-time evaluation of that function of the layout. `exists_simulator` packages it as a uniform `NUPPT` with the fixed `simCoins` polynomial and equality on every simulator tape. These results prove efficiency of the chosen simulator, independently of the still-admitted indistinguishability argument. | None. | — |
| 110 | note | Coverage and checks | The grouped entries above cover every declaration in the nine implementation files; the facade contains imports and documentation only. | Coverage reconciliation: 149 definitions/abbreviations and 274 theorem declarations, including 16 private theorems and all 258 public ones; the single decidability instance is exempt from individual docstring review. All were reviewed at the definition/statement/prose level, not by re-auditing tactic proofs. Independent finite checks enumerated all 531 Boolean-relation graphs on 0–3 vertices, their proper three-colourings and colour permutations; all six ordered-distinct-colour image sets; and all 256 partial colourings of the loopless complete four-vertex graph. These checks corroborate the boundary and bad-edge reasoning; they are not a substitute for Lean elaboration. | None. | — |

Notation used in the audit: `n` = number of vertices; `m = edgeCount G` = number of ordered edges; `N` = encoded instance length (equal to `n²` on valid graphs); `K = n m` = active attempts/iterations; `B` = the proposed commitment-hiding reduction; `ε_B` = its negligible multi-value hiding bound; `Pr` = probability over the specified uniform finite coins. Other symbols and names are those of the audited declarations.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03g-review.md =====

# Gate 03g: review of the auditor's findings (3-colouring zero knowledge)

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03g-findings.md` (SHA-256
  `09f34930…f7f1f2`, filed in `e6ffd681`). It has 110 rows: 6 findings (2 majors, 4 minors) and 104
  notes. The notes cover the admission verdicts, adversarial tests and declaration coverage.
- **Pack:** `03g-pack.md` (SHA-256 `945f565e…297066`), with the common brief `03a-pack.md`.
- **Code:** worktree `wt-g03c-fix` at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (checked with
  `git rev-parse`). Line numbers are at that commit unless marked "HEAD".
- **Since the pin:** the branch head is `559c3624`. #203 changed one proof line in this pack's files,
  `ThreeColoring/Machines.lean:126`: `polyTimeComputable_stateFind` became
  `EncodingMachines.polyTimeComputable_stateFind`, so lines after 126 move down by one.
  - It affects no finding. Only the line numbers of the auditor's Machines.lean notes (rows 33–45)
    are one too low at HEAD.
  - `Simulator.lean` and `Language.lean` are identical at the pin and at HEAD.
  - #203 also adds `NUPPT.exists_compParam` (Closure.lean). The fixes below may use it, but do not
    need it.
  - The records changed after the pin (`e79397ea`: DESIGN §5 items 8 and 11, §7 item 51;
    `559c3624`: D3). Row 6's complaints still hold at HEAD (see #6).
- **Source:** `pass-shelat-2010-ch4.raw.md`. I also looked at PDF pp. 140–141 (book pp. 128–129),
  rendered from `Pass–Shelat.pdf`, to check Algorithm 128.7 steps 4–5 and the S′/S″ wording.
- **Downstream:** `wt-prong-{a,b,c,d,d2}` and `wt-s2b` were grepped for `col_zk`, `colProtocol`,
  `R3COL` and `ThreeColoring`. Only facade imports were found. Prong C's `ZK.seqRep`
  (`SequentialZK.lean:376`) is the planned consumer: the gate-06 corollary in the decision log,
  2026-11-05.
- **Arithmetic:** `scratchpad/g03rev2/tools/arith.py`, run with `python3 -I`. It enumerated every
  3-colourable symmetric loopless graph on 0–5 vertices, the complete tripartite family, the
  `comp_sqrt` thresholds for c ≤ 5 and n₀ ≤ 5, `Nat.size` at powers of two, and the sampler failure
  rates.
- **Not done:** no Lean was built or run. The Lean-level fix sketches below are unchecked.

## Summary

- **Verdicts:** 6 true and 0 false; 0 partly true. Two of the true findings are understated:
  - #2 is worse than stated. The sketch's machine cannot match the ideal reduction even in law (see #2).
  - #5's misattribution also appears at three more sites.
- **The key question: is `col_zk` provable as stated in its declared D8 scope? Yes.** I found no
  counterexample, and I can give a complete corrected argument (§#1–#2). Both majors are defects of
  the **proof sketch only**. No statement, interface or signature changes.
  - The other two admissions, `R3COL_witnessRelation` and `colRep_efficientProverProof`, are true
    as stated. I agree with the auditor's verdict (a) for both.
  - On `col_zk` the auditor gives (b): "weaker than the source's literal all-z wording". The
    literal reading is **false** for this protocol, so no stronger true statement exists. I record
    `col_zk` as **(a) in its declared D8 scope**. The (b) only means "weaker than an unprovable
    literal reading", and it should not be read as debt. Note 9 below has the triangle
    counterexample.
- **Severity:** I agree with all six (2 majors, 4 minors).
  - #1 and #2 stay majors. Policy §3 says "the sketch *is* the plan" for a sorry-stub, and this
    pack gates the fills. The sketch of the chapter's hardest theorem contains a false inequality
    (#1) and an impossible identification (#2). Pack question 3 asks exactly whether the bound
    reduces to hiding "as the sketch claims", and the answer is no. Precedent: 03a r2 R2-2 and
    03f1 #1 were docstring and sketch claims rated major.
  - Both majors have one-paragraph fixes, using lemmas the library already has.
- **Fixes, in order of importance:**
  1. Rewrite `col_zk`'s proof sketch (`Simulator.lean:727–763`). Use the text in §#2.3 (it covers
     #1, #2, the m = 0 and N = 0 cases, and M1). The leading term becomes `N² · ε_B(⌊√N⌋)`. The
     hiding reduction fixes the ideal attempt table by `CommitmentLemmas.exists_fixCoins`, so the
     machine `B` is deterministic in the challenge, apart from `D`'s coins: one call of `V'`, one
     call of `D`.
  2. Fix the truncation attribution: `colSim` (#5), and also `Simulator.lean:34–36`, `:722`, and
     `inventory-ch4.md:30–31`.
  3. Fix the records (#6): DESIGN D8, §5 item 11, an as-built note under §2.15, and inventory
     Thm-124.1 (A), Claim-124.d and Def-124.a.
  4. Fix the docstrings of `Negligible.comp_sqrt` (#3) and `sampleEdgeIdx` (#4).
  5. Quote the S′/S″ typo faithfully (M2).
  6. For the fill brief: give the sorry ladder in M3.
- **Rulings needed: none.** No fix changes a statement or an interface, and none accepts new debt.
  - The bounded-auxiliary-input scope of `ZK` was already ruled and recorded: D8, Q-1, the
    `Defs.lean` module docstring, and DESIGN §7 item 51.
  - The choice between the two bridges for #2 is a proof strategy, so it is the maintainer's call.
    I recommend the fixed-coin bridge.
- **Ripple:** none to statements.
  - `Checks.lean` keeps its prints. `col_zk` prints `sorryAx` until the fill lands.
  - `NP.lean`'s form (A) and its tied and untied variants (pack 03e) are unchanged.
  - Prong C's planned `ZK.seqRep` corollary is unchanged.
  - The 03g fill brief must carry the corrected sketch and the ladder of M3.

## Overview

| # | Auditor | Verdict | Severity | Fix kind | Packs / prongs touched | Ruling? |
|---|---|---|---|---|---|---|
| 1 | major | true | **major** (agree) | sketch rewrite (`Simulator.lean:739–759`) | 03g only; fill brief | no |
| 2 | major | true, **understated** | **major** (agree) | sketch rewrite (`Simulator.lean:727–738, 756–759`) | 03g only; fill brief | no |
| 3 | minor | true | minor | docstring (`Simulator.lean:679–681`) | none | no |
| 4 | minor | true | minor | docstring (`Language.lean:303–305`) | none | no |
| 5 | minor | true, **understated** (3 more sites) | minor | docstrings + inventory | 03g; inventory ch. 4 | no |
| 6 | minor | true (still true at HEAD) | minor | records | 03e's §2.15 record; 03k reads D8 | no |
| M1 | — | missed | (folded into #1) | sketch | 03g | no |
| M2 | — | missed | minor | docstring + DESIGN §7 item 46 | 03g | no |
| M3 | — | missed | note | fill brief (sorry ladder) | 03g fill | no |
| M4 | — | missed | note | optional move | 03g / clean-up | no |

---

## #1 (major): the attempt-count loss in `col_zk`'s sketch

### Verdict: **true**

- The sketch (`Simulator.lean:756–759`) concludes step (4) with
  "`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`". On a yes-instance `|x| = n²`, so this asserts `n·m ≤ n²`,
  i.e. `m ≤ n`. But `m = edgeCount G` counts **ordered** adjacencies (run-3 P11-3).
- The auditor's triangle checks: `n = 3`, `m = 6`, `N = 9`, `K = n m = 18`.
- So does `K_{t,t,t}`: `n = 3t`, `m = 6t²`, `N = 9t²`, `K = 18t³`, `K/N = 2t` (computed for
  t = 1…4). The ratio is unbounded, so no constant repairs the bound.
- The failure is the rule, not an edge case. Among 3-colourable graphs, `nm > N` holds for 4 of 8
  graphs on 3 vertices, 41 of 63 on 4, and 902 of 958 on 5 (enumeration).
- The sketch is also internally inconsistent: for the sampler term it already uses `N²`
  (`2 N² (1/4)^N + N² (1/2)^N`, :739), which is the right majorant.
- The loss is genuinely `K`. `exists_colSimRed_ge` (:551) divides by the attempt count, and
  `exists_hybRed_ge` cannot avoid that factor.
- **The statement is unaffected.** `ZK` has `∃ ε`, so only the named `ε` changes.

### Recomputed bound

`K = n m ≤ n · n² = n³ ≤ n⁴ = N²` for `n ≥ 1` (and `K = 0` at `n = 0`). This was checked on every
enumerated graph. Two further points matter for the fill:

- **ε_B is nonnegative.** The step `K ε_B(n) ≤ N² ε_B(n)` needs `ε_B(n) ≥ 0` at every `n`.
  - `hC.multiHiding var B` bounds a `distAdv` (an absolute value) for all `n`-vectors, and vectors
    exist at every `n`. So `0 ≤ ε_B n` follows from the conclusion at `v = v'`.
  - The sketch should say so.
- **Under a "worst instance" choice, the factor must be the uniform majorant `n³`.**
  - If `B` hard-wires the instance that maximizes the hybrid advantage, a different instance `x'`
    at the same vertex count is bounded through the hard-wired instance's `K`, not its own.
  - So the multiplier must be the uniform `n³` (or `N²`), not "the instance's `n m`". With the
    choice of §#2.3, which maximizes the reduction's gap, either works.

The corrected error function is:

```
ε N := N² · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N : ℝ)) + N² · ((1/2)^N + (1/4)^N) + (1/4)^N
```

Its terms are:
- step (4) and the `m = 0` case: `≤ K ε_B(n) ≤ N² ε_B(√N)` for `n ≥ 1`;
- step (5): `(1 − 1/m)^K ≤ e^{−n}`;
- step (2): `K(2^{−N} + 4^{−N}) ≤ N²(…)`. The edge sampler accepts with probability at least 1/2
  (minimum 1/2 at powers of two); the colour-pair sampler fails with probability 2/8 = 1/4;
- step (1): `4^{−N}`, the same rate for `samplePerm3`.

The sketch's `2 N² (1/4)^N` was slack; one `N²(1/4)^N` suffices.

- **Negligible** by `Negligible.mul_pow (Negligible.comp_sqrt hε_B) 2`,
  `negligible_exp_neg_sqrt_div` (C = 1), `Negligible.mul_pow negligible_two_pow_neg 2`,
  `(1/4)^N ≤ (1/2)^N` with `Negligible.mono`, and `Negligible.add`.
- **At N = 0** the exponential term is 1, which bounds every advantage. This matters (M1).

A tighter alternative is `N · Nat.sqrt N · ε_B(Nat.sqrt N)`, i.e. `n³ ε_B(n)`. It is optional.

### Severity: **major** (agree)

The step is load-bearing in the plan of a sorried theorem, it is false for most inputs, and the
pack's question 3 asks exactly this. Fixing it takes one line, but as it stands it misleads.

### Fix

`Simulator.lean:739` and `:759`: replace the leading `N · ε_B (Nat.sqrt N)` by
`N² · ε_B (Nat.sqrt N)`, and the chain "`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`" by
"`≤ n m ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` (`n ≥ 1`, `0 ≤ ε_B`)". The full replacement
paragraph is in §#2.3.

### Ripple

None outside the sketch.
- The pack's question 3 quotes the old bound. The closing pack should quote the new one.
- The inventory's Prop-128.8 and Claim-129.d already state the correct `(n·m) · ε_Com`
  (`inventory-ch4.md:693, :729`). Nothing else repeats `|x| ε_B(√|x|)`: grep over briefs, TCSlib
  and audits.

---

## #2 (major): the bridge from the ideal reduction to a machine

### Verdict: **true, and understated**

- **What the auditor says, which checks.**
  - `colSimRed`'s coin type (`Simulator.lean:404–413`) is
    `(Fin K → ((Fin m × Perm (Fin 3)) × (Fin n → Fin ℓ(n) → Bool)) × ρ) × ρ'`.
  - Its cardinality `(6 m 2^{nℓ(n)} |ρ|)^K |ρ'|` is divisible by 3 for `K ≥ 1`, while a fair-bit
    tape has `2^b` elements.
  - So no `Equiv` exists, and `acceptProb_comp_equiv` cannot give
    "`colSimRed … = B.distinguisherL n` up to the coin bijection" (:758).
- **What is worse.** The identification is impossible even as an equality of acceptance
  probabilities, not just as a coin bijection.
  - A fair-coin machine's acceptance probability is dyadic.
  - The ideal reduction's probabilities are generally not. A `D'` that accepts when the colour opened
    at the first endpoint of a later `S′` attempt is 0 gives terms of `Pr_π[π(a) = 0] = 1/3`, mixed
    with weights in `1/m`.
  - So no "same law" argument of any form can bridge. The bridge must be an **inequality** (fix the
    coins) or an **approximation** (re-sample the coins, with an error term).
- **The sketch's machine is the lossy variant without its error term.**
  - The sketch builds `B` with "coins … the other attempts' blocks and `D`'s coins
    (`NUPPT.exists_split`)", runs the attempts with `polyTimeComputable_iterateFind`, and samples
    them from fair bits (:733–735).
  - That machine's acceptance differs from `colSimRed`'s by up to `(K − 1)·(edge-sampler error +
    permutation-sampler error)` on each challenge distribution. After multiplication by `K` this
    becomes a `~K²δ` term, and the ε of :739 has no such term.
  - The simulator's own sampler error (step 2) is a different term, as the auditor says.
- **The admitted statement is unaffected.** The repair below is lossless and uses only existing
  lemmas and closure facts. No new cryptographic hypothesis is needed.

### 2.1 Recommended repair: fix the ideal coins (lossless; the library's own idiom)

1. **Average out the attempt table.** Apply `CommitmentLemmas.exists_fixCoins`
   (`CommitmentLemmas.lean:108`), with `κ :=` the attempt table and `ρ :=` `D`'s coins, to
   `colSimRed … k e₀ π₀ D'`.
   - Some table `w₀` satisfies `distAdv X Y colSimRed ≤ distAdv X Y (colSimRed with w₀ fixed)`.
   - `Commitment.multiHiding` itself is proved this way (its sketch, `Commitment.lean:385–388`).
2. **With `w₀` fixed, only attempt `k` reads the challenge.**
   - Attempts `t < k` (`colSimAttemptH`) and `t > k` (`colSimAttemptW`) depend only on `w₀ t`.
   - So the fixed reduction is `cv ↦ D'(pre <|> colSimAttemptPlanted … cv (w₀ k) <|> post, ·)`,
     where `pre` and `post` are the first successes among attempts `< k` and `> k`. Both are
     constants.
   - The machine needs no loop over attempts and no `K`-entry table: one call of `V'` on the spliced
     commitment vector and one call of `D`.
   - The auditor's version (hard-wire the whole table, `≤ n³` entries) is also correct, but it is
     needlessly heavy.
3. **Choose the worst data, at each `n`.** The data are: a graph on `n` vertices, a proper `c`,
   `z` with `|z| ≤ Lz(n²)`, `k`, `e₀`, `π₀` and `w₀` (or the `m = 0` data below). Choose those that
   maximize the fixed reduction's gap on its own vectors `X`, `Y`.
   - **The set is finite only because `|z|` is bounded.** This is where `Lz` is used (the `Defs.lean`
     module docstring), and the sketch should say so.
4. **Build `B` at parameter `n`.**
   - Advice: `x`, `z`, a case flag, `ρ_k`, `e₀`, the two endpoint commitments with their openings,
     `pre`, `post`, and `D.advice (n²)`.
     - The length is polynomial in `n`. Every view is polynomially bounded:
       `hC.easy.output_length_le`, `colProtocol_proverBounded`, `|z| ≤ Lz(n²)`.
     - The advice polynomial printed at :731 omits the pairing overhead and every component after
       the instance, so it must be redone.
   - Coins: `D`'s at parameter `n²`, by `NUPPT.exists_reparam_advice` with `φ n = n²`,
     `p = mul var var`; then `B.coinLen n = D.coinLen (n²)` exactly.
   - Computation: `B` splices `cv` with `msgAt`. It evaluates `V'.next x z ρ_k [com]` through the
     uniform machine of `Strategy.Efficient` (`A.polyTimeComputable_output` on the
     `⟨⟨x, z⟩, encodeMsgs [com]⟩` layout), compares `edgeIdxOfMsg m` with `e₀`, and runs `D`.
   - It is packaged by `NUPPT.ofPolyTime` and `exists_withAdvice`, or by `exists_compParam` at HEAD.
5. **Transport the coins.** `B`'s acceptance on `multiCom` samples equals the fixed reduction's.
   - Use `acceptProb_distinguisherL_of_runAtL` (`CommitmentLemmas.lean:143`) in a two-parameter
     form (`B` at `n`, `D` at `n²`, `B.coinLen n = D.coinLen (n²)`).
   - That is a small new glue lemma, or `EnsembleLemmas.acceptProb_coins_equiv` along `finCongr`.
     The coin types here are bits on both sides, so this equivalence exists.
6. `hC.multiHiding var B` gives `ε_B`. The hybrid term is at most `K ε_B(n)`, as in #1.

### 2.2 Alternative: re-sample inside `B` (lossy)

`B` samples the other attempts with fair-bit rejection samplers (`T` trials each). Then
`|gap_B − gap_ideal| ≤ 2(K − 1)(2^{−T} + 4^{−T})`, and step (4) gains `2K(K−1)(2^{−T} + 4^{−T})`.
This is negligible for `T = n²`. It is correct, but it needs the `iterateFind` loop and an extra
term. I do not recommend it.

### 2.3 The corrected sketch (replacement for `Simulator.lean:727–763`)

> **Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
> and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
> the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
> on the encoded optional view (`⊥ ↦ []`).
>
> (1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
> uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
> randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
> `decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
> `some ∘ colRealView`.
>
> If `m > 0`:
> (2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
> `(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
> `statClose_sampleColorPair`, `StatClose.prod` over the blocks).
> (3) `uprob_colSimTruncW_eq`.
> (4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
> `distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
> `CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
> With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
> `cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
> (5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
> `distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.
>
> If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
> `0`). For each fixed `π`, `D`'s advantage is the hiding gap of `cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`,
> with `r_V` fixed by `exists_fixCoins`. Average over `π`.
> If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
> from the real tape when `V'.coinLen 0 > 0`.
>
> The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
> because `|z| ≤ Lz(n²)`), take those whose fixed reduction (either case) has the largest gap on
> its own vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and
> openings, `pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially
> bounded by `hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform
> machine once (`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins
> (`NUPPT.exists_reparam_advice`, `φ n = n²`). Its acceptance probabilities on `multiCom` samples
> are the fixed reduction's (coin transport along `finCongr`).
> `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a `distAdv` at every `n`), so the
> hiding terms are at most `K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.
>
> Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
> negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div` (`C = 1`),
> `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is `1`. Use the
> triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
> (`length_encGraph`, `Nat.sqrt_eq`).

### Severity: **major** (agree)

As written, the sketch specifies a machine whose analysis cannot be completed, and the error
budget is missing a term. The repair is standard, but the fill would otherwise have to discover it.

### Ripple

- None to statements.
- The fill needs two or three new lemmas (M3). `ColSimLemmas` and `CommitmentLemmas` keep their
  statements.
- If a two-parameter coin-transport lemma is added, ledger it next to
  `acceptProb_distinguisherL_of_runAtL` (duplication ledger), and do not keep a private copy.

---

## #3 (minor): `Negligible.comp_sqrt`'s printed threshold

### Verdict: **true**

- The sketch (`Simulator.lean:679–681`) takes `N ≥ max((n₀+1)², 4^c·4)`, then needs
  `⌊√N⌋ ≥ 4^c`.
- From `N ≥ 4^{c+1}` one only gets `√N ≥ 2^{c+1}`, which is `≥ 4^c` only for `c ≤ 1`.
- The auditor's `c = 3`, `n₀ = 1` (`N = 256`, `√N = 16 < 64`) checks. The enumeration shows the
  first failure at `c = 2` (`N = 64`, `√N = 8 < 16`).
- The code (:686–687) uses `K := max (max n₀ (4^c)) 1` and threshold `K * K`, which is correct
  (checked on samples).

### Severity: minor (agree)

The sketch of a proved lemma disagrees with its proof; this is the 03b #4 precedent.

### Fix

`Simulator.lean:679–681`:

> "Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
> `n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
> `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
> `|μ n| < 1/n^{2c+1} ≤ 1/N^c`."

### Ripple

None.

---

## #4 (minor): `sampleEdgeIdx`'s bit-width bound

### Verdict: **true**

- `Language.lean:303–305` says "(so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`)" with
  `k = Nat.size m`.
- For `m = 2^j`, `2^{size m} = 2m` (`m = 1, 2, 4, 8` checked), so the strict bound fails.
- For `m = 0`, it reads `0 ≤ 1 < 0`.
- The correct bound, `m < 2^k ≤ 2m` for `m ≥ 1`, holds for `m ≤ 5000`. It is what
  `statClose_sampleEdgeIdx` proves and uses (`h2 : 2 ^ Nat.size m ≤ 2 * m`, :397–401).

### Severity: minor (agree)

### Fix

`Language.lean:304`: "(for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds with probability
`≥ 1/2`; for `m = 0` the sampler returns the default)".

### Ripple

None.

---

## #5 (minor): truncation attributed as a deviation from Algorithm 128.7

### Verdict: **true, and understated**

- PDF p. 140 (book p. 128), Algorithm 128.7:
  - step 4: "Otherwise, restart the process from the first step, but at most n|E| times";
  - step 5: "If, after n|E| repetitions the simulation has not been successful, output fail."
- The same misattribution as `colSim`'s docstring (`Simulator.lean:636–637`) appears at:
  - `Simulator.lean:34–36` (module docstring): "the simulator is strict PPT, truncated at `n|E|`
    attempts … which costs the statistical term";
  - `Simulator.lean:722`, `col_zk`'s deviation: "strict PPT simulator truncated at `n|E|`
    attempts";
  - `inventory-ch4.md:30–31` (HEAD): "The two rewinding simulators (123.4, 128.7) are truncated at
    `n` resp. `n·|E|` attempts".
- GI's Algorithm 123.4 does restart until success (PDF raw text lines 603–604, "expected
  polynomial time"), so there the truncation **is** a deviation. Keep it.
- For 3COL, the `(1−1/|E|)^{n|E|}` cost is the text's own `O(e^{−n})` term.
- The real deviations are the rejection-sampled `e'`, colour pair and `π` (D10), and `ZK`'s strict
  simulators, which are a property of the definition (Def 121.2 allows expected time).

### Severity: minor (agree)

This is an attribution defect.

### Fix

- **`Simulator.lean:636–637`**: "As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|`
  attempts, then `fail` (`⊥ = []`). **Deviation (D10):** `e'` and the colour pair are
  rejection-sampled from the tape (defaults `0` and `(0, 1)`)."
- **`:34–36`**: "the simulator makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as the
  text does (Algorithm 128.7, steps 4–5); the failure costs the text's own term
  `(1 − 1/|E|)^{n|E|} ≤ e^{−n}`."
- **`:722`**: delete "truncated at `n|E|` attempts". Keep "strict PPT simulator", attributed to D8's
  definition of `ZK`.
- **`inventory-ch4.md:30–31`**: "The GI simulator (123.4) is truncated at `n` attempts (D8); the
  3COL simulator (128.7) already stops after `n·|E|` attempts in the text."

### Ripple

- 03k is unaffected: GI's truncation stays declared.
- The inventory's Alg-128.7 row (:205) is already right.

---

## #6 (minor): records out of sync

### Verdict: **true, and still true at HEAD**

- **D8** (DESIGN.md:136–140 HEAD): "GI and 3COL are proved statistically (truncated simulators,
  rejection-sampled permutations) … statistical instead of perfect ZK". `col_zk` is computational
  `ZK` from `Commitment.multiHiding`.
- **§5 item 11** (:1055 HEAD) still opens "GI/3COL: statistical ZK". `e79397ea` added the
  PerfectZK text but kept this.
- **§2.15** (:879–892 HEAD) prints `InteractiveProof.complete` without the message bound and
  `EfficientProverProof` without `boundedP`. The code has both (`InteractiveProofs.lean:126–128`,
  and the `boundedP` field).
  - §5 item 8 was synced after the pin; §2.15 was not.
- **Inventory:**
  - Thm-124.1 (A) (`inventory-ch4.md:535–539`) says "the composed protocol … is a ZK proof with
    efficient prover", with no `hLR`. `zk_proof_of_levinReduction` (`NP.lean:584–592`) gives two
    protocols (the repeated one, a proof; the single one, ZK) and needs `hLR`.
  - Claim-124.d (:563ff) omits `hLR` for the completeness transfer.
  - Def-124.a (:548–551) omits `length_eq` and `le_eval` (`NP.lean:145–147`).

### Severity: minor (agree)

These are records only. The Lean statements are right.

### Fix

- **D8:** "GI is proved statistically (`gi_statZK`: truncated simulator, rejection-sampled
  permutations); 3COL is computational ZK from the commitment's hiding (`col_zk`), its simulator
  stopping after `n|E|` attempts as in the text".
- **§5 item 11:** "GI: statistical ZK (…); 3COL: computational ZK (`col_zk`, via
  `Commitment.multiHiding`; rejection-sampled edges, colour pairs and colour permutations)".
- **§2.15:** do not edit the frozen block. Append an "As-built note (gate 03g, #6)", as §2.4 and §2.6
  do, giving the G3-3 signatures of `complete` and `boundedP`.
- **Inventory:**
  - Thm-124.1 (A): add `hLR`, and say "the pulled-back repeated protocol is an interactive proof
    with efficient prover and the pulled-back single iteration is ZK (DQ5)".
  - Claim-124.d: add `hLR`.
  - Def-124.a: add `length_eq` and `le_eval`.

### Ripple

- §2.15 is 03e's interface record. Note the as-built line in 03e's closing record.
- D8's GI sentence is unchanged, so 03k is unaffected.

---

## The notes (rows 7–110): checked, with one disagreement

- **Row 7, `R3COL_witnessRelation`: (a), agree.** Only `decidable` is sorried (`Protocol.lean:838`).
  The re-encoding decider is polynomial in `|⟨x, y⟩|`, including long `y`, since it reads only `2n`
  bits.
- **Row 8, `colRep_efficientProverProof`: (a), agree.**
  - I re-traced the layout (`Protocol.lean:458–504`): four moves per iteration; challenges on odd
    history counts from block `t` of `(|x|+1)²` bits; the verdict at `2|x|²`.
  - The sketch's soundness error checks: `ε N = exp(−√N) + N²(1/2)^N + 2^{−N}`.
    `(1−1/m)^{nm} ≤ e^{−n}`, and `K·2^{−N} ≤ N²2^{−N}` with `T = N` trials per block.
  - The extra `2^{−N}` makes the strict inequality hold, including the always-reject cases.
- **Row 9, `col_zk`: verdict (b) is technically right, but should read (a) in the declared
  scope.** The literal source reading (all `z`, `D` polynomial in its input) is false here.
  - Take the triangle and `|z| ≥ 2^{ℓ(n)}·poly`. `D` brute-forces every commitment in the view,
    which binding makes uniquely openable, and accepts iff all three committed colours are distinct.
  - The real view gives probability 1. The simulated view gives `Pr[{a, b} = {1, 2}] = 1/3`.
  - The `Lz` bound is therefore necessary (`Defs.lean` module docstring at the pin; DESIGN §7 item 51
    at HEAD). The source's `V*` is "p.p.t." (Def 121.2), i.e. uniform, as `V'.Efficient` is.
- **Rows 10–12** (adversarial instances): agree.
  - The total challenge decoding is checked (`Language.lean:321`).
  - The `N = 0` tape mismatch is real: `colSimCoins` is 0 at `N = 0`, so
    `colCoinSlice B 0 [] = []` and `r_V = []`. It is covered only by the `exp(0) = 1` term (M1).
  - The attempt count is advice-independent (`colIterations` depends on `x` alone; `K ≤ N²`).
- **Rows 13–14** (`hLR`, headline dependencies): agree.
  - `NP.lean:584–592` consumes `colRep_efficientProverProof`, `col_zk` and
    `col_efficientProverProofErr`.
  - `R3COL_witnessRelation` reaches no form (A) body; its only other use is `Checks.lean:312`.
- **Row 15** (evidence): reconciled.
  - `replay.log`: 115 lines with `rc=0`.
  - `axioms.log`: 6 `sorryAx` lines (258 prints).
  - `admissions.txt`: 3 entries, at `Protocol.lean:838`, `:914` and `Simulator.lean:764`.
- **Rows 16–110:** I spot-checked rows 63, 67, 76–82, 84, 88 and 90 against the code and found no
  disagreement. I did not re-derive the coverage count (row 110).

---

## Missed by the auditor

- **M1 (folded into #1): the `m = 0` sentence is false at `n = 0`.**
  - `Simulator.lean:744–746` claims the advantage is at most `ε_B n` whenever `m = 0`.
  - At `x = []` (`R3COL [] []` holds), the simulator's tape is empty, so its `r_V = []`, while the
    real `r_V` has `V'.coinLen 0` bits. `D` can then tell them apart with advantage 1.
  - The auditor notes the mismatch (row 11) but not that the sketch's sentence is false.
  - §#2.3 restricts the case to `n ≥ 1` and bounds `n = 0` by 1.
- **M2 (minor): a silent source correction in a quotation.**
  - `uprob_colSimTruncH_none` (`Simulator.lean:320–321`) quotes the text as "`S''` fails with
    probability `(1 - 1/|E|)^{n|E|}`".
  - The PDF (p. 141, book p. 129) prints "S′ fails with probability …", and before it "If we assume
    that S′ never outputs fail". Both are typos for S″.
  - **Fix:** quote "`S'` [sic: `S''`] fails …", and add the two typos to DESIGN §7 item 46
    (:1279 HEAD).
- **M3 (note; for the fill brief): the single `sorry` has no ladder.**
  - Policy §3 says each `sorry` of a skeleton should correspond to a named step. `col_zk` is one
    `sorry` for the chapter's hardest theorem, and its sketch names steps that have no lemma: "the
    colour-pair analogue of `statClose_samplePerm3`", and the machine `B`.
  - The 03g fill brief should fix the ladder:
    1. `statClose_sampleColorPair` (within `(1/4)^T` of uniform on `ColorPair`);
    2. step (1), the real view to `some ∘ colRealView`;
    3. step (2), `colSim` to `colSimTrunc`;
    4. `exists_colSimRed_fixCoins` (§2.1, items 1–2);
    5. the reduction machine `exists_colHidingRed` (§2.1, items 3–5);
    6. the `m = 0` reduction;
    7. the assembly.
  - It should also carry the 20 lint findings, which by the 2026-11-05 decision are swept with these
    fills.
- **M4 (note): placement.** `Negligible.comp_sqrt` is a general negligibility fact (Inf-4.4).
  `inventory-ch4.md` puts Inf-4.4 in `Defs.lean`, next to `negligible_exp_neg_sqrt_div`. Moving it
  there in clean-up part 2 is optional. It has no duplicate in the library (grep).

## Proposed closing condition

Gate 03g closes at **0 blockers and 0 majors** when:

1. **The `col_zk` sketch is rewritten.** `Simulator.lean:727–763` is replaced by the text of §#2.3,
   with:
   - the leading term `N² ε_B(⌊√N⌋)`;
   - the fixed-coin bridge;
   - the `m = 0`/`n ≥ 1` and `N = 0` cases;
   - the corrected advice bound;
   - the use of `Lz` stated.
2. **The minors are fixed:**
   - #3 (`Simulator.lean:679–681`) and #4 (`Language.lean:304`);
   - #5 at all four sites;
   - #6's records (D8, §5 item 11, an as-built note under §2.15, inventory Thm-124.1 (A),
     Claim-124.d, Def-124.a);
   - M2 (`Simulator.lean:321` and DESIGN §7 item 46).
3. **Checks pass and a delta audit is run.**
   - The repair touches only docstrings, so a re-check of `Language.lean`, `Simulator.lean` and their
     downstream closure suffices.
   - The admissions stay at 3 and `axioms.log` stays at 6 `sorryAx`.
   - A delta round-2 audit reads the new sketch and the changed docstrings. It is needed because both
     majors are about the sketch, and the sketch gates the fill.
4. **The fill brief for the three admissions carries the corrected sketch and the ladder of M3.**

No user ruling is needed.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03g-r1.md =====

# Gate 03g (3-colouring zero knowledge): round 1 resolutions

- **Round:** findings `findings/gate03g-findings.md`, SHA-256 `09f349307f40468c95945b2beb41a648e6d95e5bb32c126ffdc36115a5f7f1f2`; pin `0c348ff9`. **0 blockers, 2 majors, 4 minors**; the three admissions a, a, b. Review `review/gate03g-review.md`: all six true (#2 and #5 understated); `col_zk` provable as stated in D8's scope (the reviewer records its verdict as (a) in that scope). No ruling.
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| #1, #2, M1 | major | **Fixed** (#206, item E). `col_zk`'s sketch is replaced by the review's §2.3: the leading term `N²·ε_B(⌊√N⌋)`; the bridge from ideal coins to a machine that fixes the attempt table with `CommitmentLemmas.exists_fixCoins`, so the hiding machine makes one verifier call and one call to `D`; the `m = 0` / `n ≥ 1` and `n = 0` cases; the advice bound; the use of `Lz`. `statClose_sampleColorPair` is named as a lemma still to add. Docstring only. |
| #3 | minor | **Fixed.** `Negligible.comp_sqrt`'s sketch threshold (`K = max(n₀, 4^c, 1)`, `N ≥ K²`). |
| #4 | minor | **Fixed.** `sampleEdgeIdx`'s docstring: `m < 2^k ≤ 2m` for `m > 0`. |
| #5 | minor | **Fixed.** The four truncation sites now say that Algorithm 128.7 itself stops after `n|E|` attempts (`Simulator.lean`'s module docstring, `colSim`, `col_zk`'s deviation; the inventory in the records). GI's truncation stays a declared deviation. |
| #6 | minor | **Fixed (records).** DESIGN D8 erratum and §5 item 11 (3COL is computational); an as-built note under §2.15 (G3-3's `complete` and `boundedP`); inventory Thm-124.1 (A), Claim-124.d, Def-124.a. |
| M2 | (review) | **Fixed.** `Simulator.lean` quotes "`S'` [sic: `S''`]"; DESIGN §7 item 46 records the source typo. |
| M3 | (review) | **Scheduled:** the seven-step ladder for `col_zk` is in the 3-colouring fill notes (`fills/3col/brief-notes.md`). |
| M4 | (review) | **Recorded** (optional): `Negligible.comp_sqrt` could move to `Defs.lean`; not done. |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/repair.diff.txt =====

diff --git a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
index 66f802b8..c51a6ff4 100644
--- a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
@@ -38,6 +38,11 @@ inside one finite machine.
   the host: from the host seam at the module's entry state, with any output prefix, the host
   reaches the seam at the module's return state with the module's result word, forwarding exactly
   the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
+* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
+  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
+  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
+  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
+  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).
 
 ## Origin
 
@@ -62,6 +67,8 @@ machines, the control states and their table, the return map and the start state
   clean install and a clean emit module with a polynomial budget on the argument length.
 * `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
   that no control state is visited; `guard_add` — chaining guarded segments.
+* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
+  envelopes of a clean module and of a host call.
 * `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
   liveness of the prefix of a live run.
 * `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
@@ -213,6 +220,44 @@ theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B :
           state := none, output := emit arg} :=
   Iff.rfl
 
+/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
+then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
+seam at its start state holding `arg` (before, at and after its first halt), every work head is
+within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
+and the run is constant from `t` on. The contract gives nothing sharper: it fixes the terminal
+seam, not the intermediate head positions, and a clean module may move a head out and back
+before it halts at the seam (gate 03l round 2, finding 1).
+
+**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
+within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
+is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
+`MultiTapeTM.runFrom_of_halt`). -/
+theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
+    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
+    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
+      (B arg.length : ℤ) := by
+  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
+  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
+      none := by
+    rw [hend]
+  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
+      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
+        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
+    rcases le_total v t with hvt | htv
+    · exact ⟨v, hvt, rfl⟩
+    · refine ⟨t, le_rfl, ?_⟩
+      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
+  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
+    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
+  rw [Cfg.ofWords_workTapePos] at h1 h2
+  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
+  rw [hu, abs_le]
+  constructor <;> omega
+
 /-- Turn a clean-call bridge contract into the uniform first-halting form.
 
 **Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
@@ -503,6 +548,42 @@ theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
   · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
     exact host_seam M K ret i hp x result pre out q none
 
+/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
+endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
+`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
+where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
+the duration of the call, so this bounds the heads throughout the call.
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
+`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
+tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
+physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
+origin, so the host's heads obey any head envelope of the module.
+
+**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
+at the origin, and `v ≤ t`. -/
+theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
+    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
+        j| ≤ (t : ℤ) := by
+  intro v hv j
+  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
+      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
+    intro c hc
+    obtain ⟨h1, h2⟩ :=
+      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
+    rw [hc] at h1 h2
+    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
+    rw [abs_le]
+    constructor <;> omega
+  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)
+
 /-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
 and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
 from `c` avoids `anchor` before time `a + b`. -/
@@ -545,4 +626,38 @@ theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
     host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
   exact ⟨t, hp, ht, hguard, hend⟩
 
+/-- **A clean module call inside the host, with its head envelope** (the bounded call of
+`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
+emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
+prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
+output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
+`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
+every time `v ≤ t` has every work head within `B |arg|` cells of the origin.
+
+The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
+the sharper envelope inherited from the module).
+
+**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
+`t ≤ B |arg|`, gives the envelope. -/
+theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M)
+    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
+    (h : Clean (M i) f g B) (x arg pre : List Bool) :
+    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
+      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
+          ≠ some (.inl c)) ∧
+      (hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
+        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
+      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+          v).workTapePos j| ≤ (B arg.length : ℤ) := by
+  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
+  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
+  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
+  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB
+
 end Turing.ModuleHost
diff --git a/TCSlib/Cryptography/Asymptotic/OneWay.lean b/TCSlib/Cryptography/Asymptotic/OneWay.lean
index b2445e44..7ac5de06 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWay.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWay.lean
@@ -281,8 +281,9 @@ theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 
   simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]
 
 /-- **The literal form implies the `1^n` form when the output length determines the
-parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
-audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
+parameter** (injective `outLen`, equivalently non-constant output length for these polynomial
+lengths; repair of the run-3 audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a
+`1^n`-inverter `B` is the literal
 inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
 and `B.advice n` at the output length and leaves its extra coins unread.
 
diff --git a/TCSlib/Cryptography/Candidates/Concrete.lean b/TCSlib/Cryptography/Candidates/Concrete.lean
index 59dac7c5..938af1fa 100644
--- a/TCSlib/Cryptography/Candidates/Concrete.lean
+++ b/TCSlib/Cryptography/Candidates/Concrete.lean
@@ -519,6 +519,15 @@ def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List B
     if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- Block rejection sampling unfolded: `rejectBlocksL E k B T r` is the first `some v` over
+`t ∈ [0, T)` (`List.findSome?` over `List.range T`) with `v` the number read from the first `k`
+bits of the `t`-th block of `B` bits of `r`, kept iff `E v`. -/
+theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
+    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
+      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
+      else none :=
+  rfl
+
 /-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
 bits, `listToNat_lt_two_pow`). -/
 theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 767d14fe..b7fbd309 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -49,7 +49,8 @@ collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀
 as an argument.
 
 **Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
-the `1/q` term of Theorem 107.3) the prime must have full length `2^{n−1} ≤ p`. This is
+the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
+hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
 demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
 `Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
 loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
@@ -316,9 +317,11 @@ def FullLength : Prop :=
 
 /-- The generator outputs primes of full length `n` **except on a set of coins of probability
 at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
-rejection sampler, D10). Needed, with `Negligible δ`, where the proofs divide by `q` or
+rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
 `p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
-are discarded and contribute at most `δ n`. Whether safe primes (resp. primes `≡ 3 (mod 4)`
+are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
+a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
+review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
 with a generator) of full length can be produced for every `n` except with negligible
 probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
 unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
@@ -467,6 +470,15 @@ def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
     if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
+`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
+review, M2). -/
+theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
+    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
+  funext r
+  rw [rejectBlocksL_eq]
+  rfl
+
 /-- A sampled value is below `m`. -/
 theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
     v < m := by
@@ -484,18 +496,15 @@ distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
 `expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
 `ddhExpo`).
 
-**Proof sketch.** `k ≤ n` by `Nat.size_le`, so trial `t < n` reads the first `k` bits of the
-`t`-th block of `n` bits of `List.ofFn b` (`NumberTheory.chunk`; `List.drop`/`List.take` of
-`List.ofFn`), and `sampleBelowL m k n n` is `firstHit (· < m)` of the numbers read from the
-blocks (`List.findSome?` over `List.range n` versus `List.finRange n`; `listToNat` of the `k`
-bits is `bitsToNat` of the block's prefix, `bitsToNat_eq_listToNat`). The map from the `n · n`
-coins to the `n` prefixes is a product of coordinate projections, so it pushes the uniform
-distribution to the uniform one on `Fin n → Fin k → Bool` (`StatClose.comp_pushesUniform`),
-and reading bits is the bijection `bitsEquiv k` onto `Fin (2^k)`; `statClose_firstHit` with
-`E = {x < m}` and `d = 0` gives closeness `(1 − m/2^k)^n ≤ (1/2)^n` (`Nat.lt_size_self`:
-`m/2^k ≥ 1/2`), transported along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` by
-`StatClose.comp_equiv_right` and `StatClose.map` (`Fin.val`), exactly as in
-`statClose_rejectionSample`. -/
+**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
+filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
+`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
+(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
+`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
+the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
+`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
+target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
+(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
 theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
     StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
       (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
@@ -514,7 +523,7 @@ def expSampleRaw (z : List Bool) : List Bool :=
 domain `D_i`"] given the arithmetic bundle.
 
 **Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
-leading zeros stripped (requested shared primitive, as in the RSA sampler); the trial loop is
+leading zeros stripped (`H.size`); the trial loop is
 `Complexity.polyTimeComputable_iterateFind` over the `n` blocks of `1^n` bits
 (`polyTimeComputable_pairDropPoly`), each trial comparing the first `k` bits with `m`
 (`H.le`); the payload is the accepted block, the `none` branch gives the fallback; the output
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
index 14900a0d..8c1cc2b3 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
@@ -558,24 +558,36 @@ set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f
 `expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
 `orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
 `Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
-success is `predProb (expo g_u) (halfBit (p−1)) A_i` with `A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`.
-Apply `invProb_dlInverter_ge` with `s := ⌊ε(p−1)/4⌋ ≥ 1` (as `p − 1 ≥ 2^{n−1} − 1 ≥ 8n^c` for
-large `n`), `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n · (2n^c)² = 16 n^{2c+1}`: the inverter
-succeeds on the good instances with probability `≥ (3/4)/T ≥ 3/(4(8n^c + 1))`, hence overall
-`≥ (ε/2) · 3/(4(8n^c + 1))` (`OneWay.uprob_mul_le_uexp`-style averaging over the good set). The
-machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, 1^{n}⟩`, coins
-`T·n + n·ℓ·(2n + A.coins)` (all `PolyExpr`), on `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`,
-computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`), samples `t` and the `r_{j,i}` by
-rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by
-`statClose_rejectionSample`/`StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), shifts
-`y · g^{−ts}` (`H.modExp`, `H.xgcd` for the inverse), and runs the `n` rounds of `dlLoop`
-(`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11): quadratic
-residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by `H.modExp`
-(`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
-`⟨⟨⟨1^n, ⟨i, z_i⟩⟩, A.advice n⟩, ρ_i⟩` (`polyTimeComputable_iterateEmit`, `NUPPT.polyTimeComputable_layout`),
-the comparison with `half(r_i)` (`halfStr`), the majority (`polyTimeComputable_majority`), the
-negation `p − z` and the bit assembly; finally `(bits + ts) mod (p−1)` as an `n`-bit numeral
-(`decodeFin n` reads it back, `bitsToNat_natToBits`). Thus `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`
+success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
+`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
+Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
+`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
+(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
+`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
+succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
+The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
+(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
+`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
+and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
+`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
+`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the
+good instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
+`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
+`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the
+`n` rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`,
+D11): quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
+`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
+`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
+`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the
+majority (`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
+`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
+`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
+of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of
+`A` are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
+`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
+`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
+`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n`
+`= 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
 for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
 theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
     (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
diff --git a/TCSlib/Cryptography/Candidates/ElGamal.lean b/TCSlib/Cryptography/Candidates/ElGamal.lean
index 1f1d1ab4..be4efe98 100644
--- a/TCSlib/Cryptography/Candidates/ElGamal.lean
+++ b/TCSlib/Cryptography/Candidates/ElGamal.lean
@@ -56,10 +56,11 @@ generator's coins (`ExpGroupGen.FullLengthExcept`).
 
 **Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
 `Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
-`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — the two ensembles
-then had different instance laws whenever `q` varies with the coins, and the threshold test
-`[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every
-randomized generator. The seeds are now product types (uniform coins for the generator, D6)
+`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — so the two ensembles
+could have different instance laws, and when `q` varies non-negligibly with the coins (two
+orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a
+threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons
+unrelated to DDH. The seeds are now product types (uniform coins for the generator, D6)
 with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
 (full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.
 
@@ -294,8 +295,8 @@ run-3 audit P2-2, by instance resolution).
 
 Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
 the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
-depended on the fibre sizes and differed from `ddhRandom`'s (cubes), making `DDHAssumption`
-false for every generator whose `q` varies with the coins. -/
+depended on the fibre sizes and differed from `ddhRandom`'s (cubes), which could make
+`DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20). -/
 noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
   σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
   X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
@@ -509,9 +510,9 @@ def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
 (`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
 layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
 rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
-test `H.le` (the decrement `p − 1` and the bit length `Nat.size` are requested shared
-primitives, as in the RSA generator); `h = g² mod p` and `h^x mod p` by `H.modExp`; the
-numerals are padded to width `n` (`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
+test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
+`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
+(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
 theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
     PolyTimeComputable (egGenRaw G) := by
   sorry
@@ -843,8 +844,11 @@ except on a negligible set of the generator's coins (and under the arithmetic hy
 **Deviation:** message space `G_q` and the chosen-message form of security (the text's
 `m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
 and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
-makes the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of probability
-`δ n`; the text leaves the proof as an exercise and omits the generator-versus-square term.
+is used to make the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of
+probability `δ n` (a convenience: if `E[1/q]` were not negligible, a DDH distinguisher finding
+`a` by exhaustive search when `q ≤ 2n^c` would contradict the DDH assumption, so `hbig` could be
+dropped; gate 03f1 review, M1; ruling R-03f1-1 (A) keeps it); the text leaves the proof as
+an exercise and omits the generator-versus-square term.
 
 Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
 is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
diff --git a/TCSlib/Cryptography/Candidates/Factoring.lean b/TCSlib/Cryptography/Candidates/Factoring.lean
index 42944c08..0566c08f 100644
--- a/TCSlib/Cryptography/Candidates/Factoring.lean
+++ b/TCSlib/Cryptography/Candidates/Factoring.lean
@@ -499,11 +499,17 @@ with the step dropping `n` bits, the test `hP` on the first `n` bits, the payloa
 bits, `R = 2n²`, `P = var`), whose `List.range.find?` form is `firstHit` over `chunk`
 (`samplePrime`); the fallback numeral `natToList n 2 = 0^{n-2}10` of a failed run is the
 `none` branch of `iterateFind` (a constant string of unary-polynomial length,
-`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`); the acceptance test of
-`samplePairOut` is two `H.prime` calls, a `pairEq` test and two `H.le`
-comparisons with `1^{max n 2}` (`polyTimeComputable_ite`), the accepted blocks are re-encoded
-with `max n 2` bits (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the
-default pair is a constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). The acceptance test of
+`samplePairOut` uses `hP` only (this theorem has no `ArithmeticFP` argument): the two prime
+tests are `hP`, and the inequality of the two values is tested by comparing the two `n`-bit
+words directly (a `pairEq` test: words of equal length have equal values iff they are equal);
+the two range checks `< 2^{max n 2}` are discharged from the fixed widths, not computed (each
+`samplePrimeL` output has `n` bits, so its value is `< 2^n ≤ 2^{max n 2}`,
+`listToNat_lt_two_pow`); the branch is `polyTimeComputable_ite`. The accepted words are
+re-encoded with `max n 2` bits by leading-zero padding (the `max n 2`-bit numeral of an `n`-bit
+word is the word preceded by `max n 2 − n` zeros, a constant block of unary-polynomial length:
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the default pair is a
+constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
 theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
     PolyTimeComputable samplePairRaw := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/RSA.lean b/TCSlib/Cryptography/Candidates/RSA.lean
index e548ac26..e2379a32 100644
--- a/TCSlib/Cryptography/Candidates/RSA.lean
+++ b/TCSlib/Cryptography/Candidates/RSA.lean
@@ -755,14 +755,26 @@ so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", wh
 event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`, `decodeFin_ofFn`,
 `bitsToNat_natToBits`, `val_units_pow`). Since `x ↦ x^e` pushes uniform to uniform
 (`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the inner probability equals the RSA
-inner probability at `(z, e)`. The law of `(z, e)` under the generator's coins is within
-`rsaGenErr n` of the ideal uniform law on `DistinctPrimes n × Z*_{Φ(N)}`
-(`statClose_samplePrime` with the prime fallback `natToBits n 2` of `samplePrimeL` — run-3
-audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map` through the validity
-test with `uprob_diag` and `one_div_card_primes_le` for the fallback on `p = q`,
-`statClose_rejectBlocksL` for `e` with the acceptance rate of the sampleClose sketch); `StatClose.abs_uprob_sub_le_prod` with the
-auxiliary coins `(y, r)` turns `uexp` over the generator's coins into `uexp` over `z`
-(`uexp_prod`, `uprob_prod`) up to `rsaGenErr n`. -/
+inner probability at `(z, e)`: a number `h(z, e) ∈ [0, 1]` (over `y` and `A`'s coins).
+The exponent group `Z*_{Φ(N)}` depends on `z`, so the generator's law is not compared with one
+uniform product: the comparison is a conditional expectation over `z`. Split the generator's
+coins into the two prime segments and the exponent segment (`rsaGenParams`, `uexp_prod`,
+`uprob_prod`). (i) For each fixed prime pair `z`, the exponent drawn from the exponent segment
+(`sampleUnitL` modulo `Φ(N)`, fallback `1`) is within `e^{-n}` of the uniform element of
+`Z*_{Φ(N)}` (`statClose_rejectBlocksL` with the acceptance rate of the sampleClose sketch), so
+the conditional success at `z` exceeds `g(z) := E_{e uniform}[h(z, e)]` by at most `e^{-n}`
+(`StatClose.abs_uprob_sub_le_prod`, with `(y, r)` as the auxiliary coins). (ii) The law of `z`
+under the two prime segments is within `2 · 2^{-n} + 2n/2^n` of the uniform law on
+`DistinctPrimes n` (`statClose_samplePrime` with the prime fallback `natToBits n 2` of
+`samplePrimeL` — run-3 audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map`
+through the validity test with `uprob_diag` and `one_div_card_primes_le` for the fallback on
+`p = q`); averaging the `[0, 1]`-valued `g` over that law instead of the uniform one costs at
+most that distance (`StatClose.abs_uprob_sub_le_prod` again, with `g(z)` read as a probability
+over the auxiliary coins `ω : Π z', Z*_{Φ(N')} × Z_{N'}^* × A.Coins n` at `ω z`). (iii) Adding
+the conditional exponent error, the inversion probability is at most
+`uexp g + (2 · 2^{-n} + 2n/2^n) + e^{-n} = rsaProb (rsaBreaker A) n + rsaGenErr n`, as
+`rsaProb` is the outer `uexp` over `z` of the inner probability over `(e, y, r)`. No error
+beyond `rsaGenErr n` is needed. -/
 theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
     (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/Rabin.lean b/TCSlib/Cryptography/Candidates/Rabin.lean
index d9c93a07..a0a19227 100644
--- a/TCSlib/Cryptography/Candidates/Rabin.lean
+++ b/TCSlib/Cryptography/Candidates/Rabin.lean
@@ -146,8 +146,12 @@ theorem blumFactoring_of_factoring (hD : BlumDensity) (hF : FactoringAssumption)
 
 /-! ## The symmetry lemma (Claim-62.2) -/
 
-/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`: a square root of `1` different from `±1`
-[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"]. -/
+/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`, for coprime moduli `p`, `q`
+[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"].
+It squares to `1` for all coprime moduli (`crtNegOne_sq`). For primes `p`, `q` it differs from
+`1` when `q` is odd and from `−1` when `p` is odd (`crtNegOne_ne_one`, `crtNegOne_ne_neg_one`),
+so for two odd primes it is a square root of `1` other than `±1`. Coprimality alone does not
+give this: for `p = 2`, `q = 3` it is `5 = −1` in `Z_6`. -/
 noncomputable def crtNegOne {p q : ℕ} (h : p.Coprime q) : (ZMod (p * q))ˣ :=
   (crtUnits h).symm (1, -1)
 
@@ -495,8 +499,9 @@ theorem rabinCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rabinCollection
 /-- The statistical error of the Rabin reductions at parameter `n`: two restricted prime
 samplers and the unit sampler of `rabinFactorer`, the latter counted twice because it enters
 through the factor `2` of the symmetry lemma (`e^{-n}` each: `4e^{-n}`), and the diagonal
-`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` for the `P = |Π_n| − 1 ≥ 2` odd
-primes (`one_div_card_primes_le`) and `1/B ≤ 4n/2^n` for the `B` Blum primes (`BlumDensity`).
+`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` with `P = |Π_n|` the total prime
+count, of which `P − 1 ≥ 2` are odd (`one_div_card_primes_le`), and `1/B ≤ 4n/2^n` for the `B`
+Blum primes (`BlumDensity`).
 
 Repair (run-3 audit P7-3): the diagonal term was `2n/2^n`, which neither the Chebyshev bound
 `2^n ≤ 2n|Π_n|` (odd class: `1/(|Π_n| − 1)`) nor `BlumDensity` (`1/B`) yields; both give
diff --git a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
index 423c20bc..ddae2c96 100644
--- a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
+++ b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
@@ -36,7 +36,8 @@ arguments by the text's monotonicity of `t / log t`.
 
 **Deviation:** [PS10, Theorem 31.3] claims the strict inequality `π(x) > x / (2 log x)` for
 every real `x > 1`; equality holds at `x = 2` (`π(2) = 1`), so the theorem is stated with `≤`,
-for natural arguments `m ≥ 2`. **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
+and for natural arguments `m ≥ 2`, which repairs and restricts the real claim (it fails even with
+`≤` at `x = 3/2`, where `π(x) = 0`). **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
 `x = 1, p = 2`; the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is Mathlib's
 `Nat.pow_factorization_choose_le`. **Deviation:** the density corollary needs `n ≥ 2`
 (`Π_1 = ∅`); the text's "`n`-bit numbers" silently assumes it.
@@ -157,7 +158,9 @@ theorem chebyshev_two_mul (x : ℕ) (hx : 0 < x) :
 `m / (2 log₂ m) ≤ π(m)`.
 
 **Deviation:** stated with `≤` (the text's `>` fails at `m = 2`) and for natural arguments
-`m ≥ 2` (the text's real `x > 1`; `π` is a step function, so nothing is lost).
+`m ≥ 2`. This repairs and restricts the text's claim for every real `x > 1`, which is false even
+with `≤`: at `x = 3/2`, `π(x) = 0 < x / (2 log₂ x)`. The natural-argument form is the one the
+prime-density uses need.
 
 **Proof sketch.** Even `m = 2x`: `chebyshev_two_mul`. Odd `m = 2x − 1 ≥ 3`: `2x` is composite,
 so `π(m) = π(2x) ≥ 2x / (2 log₂(2x))`, and `t ↦ t / log₂ t` is increasing for `t ≥ 3`
diff --git a/TCSlib/Cryptography/NumberTheory/Primality.lean b/TCSlib/Cryptography/NumberTheory/Primality.lean
index e9e0e712..1c496b08 100644
--- a/TCSlib/Cryptography/NumberTheory/Primality.lean
+++ b/TCSlib/Cryptography/NumberTheory/Primality.lean
@@ -41,7 +41,10 @@ The Miller–Rabin test [PS10, §2.6.5] and the prime sampler [PS10, §2.6.6]:
 test reject primes with positive probability; the test draws `α ∈ [1, N−1]` as in the
 standard presentation, matching `|L_N| = N − 1`. Even `N > 2` are rejected outright (the text
 handles only the base case `N = 2`). **Deviation:** [PS10, Theorem 49.14] says "with
-probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case needs `N` odd.
+probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case is proved for odd `N`
+only, as a convenience: for even `N > 2` the liars also lie in a proper subgroup of `Z_N^*` (the
+kernel of `x ↦ x^{N−1}`, which misses `−1` since `(−1)^{N−1} = −1`), and the test rejects even
+`N` outright.
 **Deviation:** `SamplePrime` is truncated to `T` trials (strict PPT with failure `⊥`, D10)
 and tests primality exactly (`Nat.Prime`); with Miller–Rabin in place of the exact test the
 output would only be statistically close to uniform. §2.6.6 (p. 50) misquotes the prime
@@ -386,8 +389,11 @@ private theorem liar_pow_mem {N : ℕ} (hN : 2 < N) {j' : ℕ}
 /-- **Odd composites have few liars** [PS10, Lemma 50.15, second half]: for odd composite
 `N > 2`, `|L_N| ≤ (N−1)/2`, stated as `2 |L_N| ≤ N − 1`.
 
-**Deviation:** the text says `N > 2` composite (oddness is needed) and `<` (the proof gives
-`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14).
+**Deviation:** the text says `N > 2` composite and `<`. The restriction to odd `N` is a
+convenience, not a necessity: for even `N > 2` every liar satisfies `α^{N−1} = 1` while the unit
+`−1` does not (`N − 1` is odd and `−1 ≠ 1`), so the liars again lie in a proper subgroup;
+`uprob_millerRabin_le` rejects even `N` outright and needs only the odd case. The proof gives
+`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14.
 
 **Proof sketch.** ([CLRS09, Theorems 31.38–31.39].) Every liar is a unit (`α^{N−1} = 1`,
 `mrLiar_isUnit`), so it suffices to exhibit a proper subgroup of `Z_N^*` containing every
@@ -859,10 +865,11 @@ private theorem spFind_eq (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool) :
     rfl
 
 /-- **`SamplePrime` is a PPT** [PS10, Lemma 51.17, "in time `poly(n)`"], given a
-polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan,
-AKS or Miller–Rabin): there is a uniform `NUPPT` with coin polynomial `2n² · n` whose
-activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks of
-`n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
+polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan:
+an exact deterministic primality test such as AKS; a bounded-error Miller–Rabin test does not
+compute `hP`'s function exactly): there is a uniform `NUPPT` with coin polynomial `2n² · n`
+whose activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks
+of `n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
 
 **Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` (M3): on the state
 word `⟨1^n, r⟩`, the step `spStep` drops the first `n` bits of the second component
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
index f6c4bc5f..8e81839e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
@@ -39,13 +39,15 @@ and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the erro
 a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
 stated for a protocol and a witness relation without assuming the proof property, which the
 theorems add separately.
-The bound `Lz` is necessary, not only convenient (gate 03e, note 9): the distinguisher runs in
-time polynomial in its input, the encoded view, which contains `z`; with `|z| ≥ 2^n` it could
-invert a one-way permutation on `n`-bit inputs and open the unopened commitments of the
-3-colouring protocol, so computational zero-knowledge would fail for every protocol whose
-hiding is only computational. Read literally, [PS10, Definition 121.2] (every
-`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect. For the same reason
-the distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
+The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
+note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
+encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
+binding commitments by exhaustive search. On a graph with two proper colourings outside one
+colour-permutation orbit, that tells the two real views apart with advantage 1, while the
+simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
+`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
+Protocols with exactly simulable views are not affected. For the same reason the
+distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
 
 **Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
 drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
@@ -307,6 +309,15 @@ def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
     (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
       (S.coinLen (NUPPT.inParam w).length)))
 
+/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
+`inParam w`, argument `inArg w`, empty advice and coins
+`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
+theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
+    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
+      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
+        (S.coinLen (NUPPT.inParam w).length))) :=
+  rfl
+
 /-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
 (for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
 first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
@@ -317,6 +328,41 @@ noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
     attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
   else []
 
+/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
+whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
+attempt `i` if `i < N`, and `[]` otherwise. -/
+theorem retry_eq (S : NUPPT) (w : List Bool) :
+    retry S w =
+      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
+          (NUPPT.inParam w).length then
+        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
+      else [] :=
+  rfl
+
+/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
+`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
+`retry_eq` with it and take the `i < |inParam w|` branch. -/
+theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
+    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
+    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
+  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
+    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
+  rw [retry_eq, h, if_pos hi]
+
+/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
+then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
+rewrite `retry_eq` with it and take the `else` branch. -/
+theorem retry_eq_nil {S : NUPPT} {w : List Bool}
+    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
+  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
+      (NUPPT.inParam w).length :=
+    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
+  rw [retry_eq, h', if_neg (lt_irrefl _)]
+
 /-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.
 
 **Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
index 9869c680..675fa55e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
@@ -71,9 +71,10 @@ lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the chan
 variables `gniShear`), which certifies the repaired statements.
 
 **Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
-moves per iteration (`H`, `b`, `γ`, and an empty verifier message) so that the strict
-prover/verifier alternation of `exec` is respected; the repeated protocols run `|x|`
-iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in `|x|` directly).
+moves per iteration (`H`, `b`, `γ`, and a verifier message, empty except for the final
+verdict) so that the strict prover/verifier alternation of `exec` is respected; the repeated
+protocols run `|x|` iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in
+`|x|` directly).
 
 **Deviation (well-formedness):** the verifiers reject common inputs that are not the
 encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
@@ -552,7 +553,8 @@ noncomputable def giVerifierRep : Strategy where
 
 /-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
 `|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
-an empty verifier message, D8 fixed alternation), `4|x|` messages. -/
+a verifier message, empty except for the final verdict, D8 fixed alternation), `4|x|`
+messages. -/
 noncomputable def giProtocolRep : Protocol where
   P := giProverRep
   V := giVerifierRep
@@ -924,18 +926,20 @@ theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
 `n² ≤ |x|`, so at most `|x|` bits per message, on every instance (ruling G3-3 of gate 03;
 `GI.giProver_length_le`). -/
 theorem giProtocol_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocol.ProverBounded R .var := fun x y r hist _ => GI.giProver_length_le x y r hist
+    giProtocol.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProver_length_le x y r hist
 
 /-- The `|x|`-fold form of `giProtocol_proverBounded` (`GI.giProverRep_length_le`). -/
 theorem giProtocolRep_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocolRep.ProverBounded R .var := fun x y r hist _ => GI.giProverRep_length_le x y r hist
+    giProtocolRep.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProverRep_length_le x y r hist
 
 /-- The honest graph non-isomorphism prover sends one bit per message (ruling G3-3 of gate 03;
 `GI.gniProver_length_le`), in one iteration and in the `|x|`-fold protocol. -/
 theorem gniProtocol_proverBounded (R : List Bool → List Bool → Prop) :
     gniProtocol.ProverBounded R (.const 1) ∧ gniProtocolRep.ProverBounded R (.const 1) :=
-  ⟨fun x y r hist _ => GI.gniProver_length_le x y r hist,
-    fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
+  ⟨(Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
 
 /-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
 with soundness error `1/2` and efficient prover with respect to `R_iso`
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
index a8918e97..22a93238 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
@@ -318,7 +318,8 @@ theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Ef
       rw [HardcoreBit.uprob_eq_one_of_forall hall]
       norm_num
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProver_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProver_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact gi_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
index 4aeed143..22b293d7 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
@@ -474,7 +474,8 @@ theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVeri
       have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
       linarith
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProverRep_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProverRep_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact giRep_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 23519614..b6f95458 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -37,10 +37,12 @@ last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chap
 are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
 message as the verdict.
 Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
-verifier, prover) is repeated under strict alternation by appending one dummy empty verifier
-message to each iteration, so that every iteration starts with the prover; the fourth move of
-`giProtocolRep` and of `colProtocolRep`, and the filler moves of the sequential repetition of
-[PS10, §7.2.1] in ch. 7, follow this convention.
+verifier, prover) is repeated under strict alternation by giving each iteration one additional
+verifier move, so that every iteration starts with the prover. In `giProtocolRep` and
+`colProtocolRep` that move is the empty message, except for the protocol's final move, which
+carries the verifier's verdict (the verdict convention above). The sequential repetition of
+[PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(|x|)` filler moves of both parties,
+its last filler again carrying the verdict.
 `Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
 activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
 whole random tape; the time is polynomial in the total input length rather than in `|x|`
@@ -331,6 +333,13 @@ of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate.
 def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
   ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length
 
+/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
+`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
+theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
+    π.ProverBounded R B ↔
+      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
+  Iff.rfl
+
 /-- A message bound `B` implies every pointwise larger bound `B'`. -/
 theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
     (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
diff --git a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
index 6b774497..09042140 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
@@ -33,8 +33,9 @@ read as the output string `[false]`, the negligible `ε` quantified before the i
 cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
 polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
 averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
-every pair of random tapes. The parties' efficiency (the text's "p.p.t.") is
-`Strategy.Efficient`, polynomial time in `|x| + |z| + |messages|` (D8), together with a
+every pair of random tapes. The verifier's efficiency (Definition 116.1's "p.p.t.", and the
+prover's for Definition 119.5) is `Strategy.Efficient`, polynomial time in
+`|x| + |z| + |messages|` (D8), together with a
 polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
 convention of ch. 6): in the completeness clause of `InteractiveProof` and
 `InteractiveProofErr` for the completeness witness, and as the field `boundedP`
@@ -43,10 +44,13 @@ witness. The residual deviation is that against a cheating prover the verifier's
 polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
 are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
 message is still complete (the honest messages are untouched) and sound (against `P*` it acts
-as `V` against `P*` with truncated messages, another prover strategy). So the proof systems
-hold only for languages of the text's class IP — undecidable languages such as the halting
-problem, whose computation histories are not polynomially bounded, are excluded — while
-`IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
+as `V` against `P*` with truncated messages, another prover strategy). So `InteractiveProof`
+(and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`)
+holds only for languages of the text's class IP — undecidable languages such as the halting
+problem, whose computation histories are not polynomially bounded, are excluded — the
+explicit-error forms with a large error say little (with `s = 1` the zero-message,
+always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —
+while `IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
 (run-3 audit P9-1). The capping argument is not formalized as a lemma.
 
 ## Main definitions
@@ -111,12 +115,14 @@ on the complete history of the fixed-alternation execution; `P'` ranges over str
 polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
 `uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
 polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
-witness are bounded by `B(|x|)` (the text's p.p.t. prover writes at most `t(|x|)` bits; the
-convention of ch. 6). Against a cheating prover the verifier's work is polynomial in the
-length of the messages it receives, not in `|x|`; because the honest messages are short the
-verifier can be capped to their length without losing completeness or soundness (module
-docstring), so the predicate holds only for languages of the text's class IP. The class `IP`
-is stated with the message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
+witness are bounded by `B(|x|)` (Definition 116.1's prover need not be efficient; bounding its
+messages is the chosen normal form, harmless because a verifier of time `t(|x|)` reads at most
+`t(|x|)` bits of each message; the convention of ch. 6). Against a cheating prover the
+verifier's work is polynomial in the length of the messages it receives, not in `|x|`; because
+the honest messages are short the verifier can be capped to their length without losing
+completeness or soundness (module docstring), so the predicate holds only for languages of the
+text's class IP. The class `IP` is stated with the message-prefix cap `Strategy.ReadsPrefix`
+(run-3 audit P9-1). -/
 structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
   /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
   efficientV : π.V.Efficient
@@ -232,7 +238,7 @@ theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Boo
       ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
   ⟨B, fun x hx =>
     let ⟨y, hy⟩ := hLR x hx
-    ⟨y, fun r hist => hB x y r hist hy, hc x y hy⟩⟩
+    ⟨y, fun r hist => (π.proverBounded_iff R B).1 hB x y r hist hy, hc x y hy⟩⟩
 
 /-! ### Witness relations -/
 
@@ -466,7 +472,7 @@ theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
 theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
     {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
     (npProtocol T p).ProverBounded R p :=
-  fun x y _ _ hxy => hp x y hxy
+  ((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy
 
 /-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
 `R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
diff --git a/TCSlib/Cryptography/ZeroKnowledge/NP.lean b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
index 8ad8b9c0..9e83f76c 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/NP.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
@@ -275,6 +275,7 @@ theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
     {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
     {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
     (π.pullback f w p).ProverBounded R (B.subst p) := by
+  rw [Protocol.proverBounded_iff] at hB ⊢
   intro x y r hist hxy
   rw [PolyExpr.eval_subst, ← h.length_eq x]
   exact hB (f x) (w x y) r hist (h.witness x y hxy)
@@ -674,25 +675,27 @@ scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduc
 one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
 `1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
 efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
+The Levin reduction `LevinReduction L L3COL R R3COL f w p` is part of the conclusion (ruling
+R-03e-r2-1 of gate 03e round 2), so further protocols can be pulled back along the same maps.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
     {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-      (∀ N, N ≤ p.eval N) ∧
+      LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
       EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
       ZK ((colProtocol Com ℓ).pullback f w p) R ∧
       EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
         (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨f, w, p, h⟩ := h3 L R hR
-  exact ⟨f, w, p, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
+  exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
 zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
 from the text's hypothesis, a one-way permutation, there is a commitment scheme
-(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds,
-under NP-hardness of `3COL` with Levin reductions.
+(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds
+(the Levin reduction included), under NP-hardness of `3COL` with Levin reductions.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
@@ -700,7 +703,7 @@ theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
       ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-        (∀ N, N ≤ p.eval N) ∧
+        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
         EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
         ZK ((colProtocol Com ℓ).pullback f w p) R ∧
         EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
@@ -734,7 +737,7 @@ theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → L
         EfficientProverProofErr π L R
           (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
-  obtain ⟨_, _, p, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
+  obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
   exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
index 0d3c8409..8e77b389 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
@@ -301,8 +301,9 @@ noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
   ((sampleIdx 6 3 T r).map perm3Equiv).getD 1
 
 /-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
-rejection trials of `Nat.size m` bits (so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`),
-the index `0` on failure (D10). -/
+rejection trials of `k = Nat.size m` bits (for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds
+with probability `≥ 1/2`; for `m = 0` the sampler returns the default), the index `0` on
+failure (D10). -/
 def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
   ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0
 
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
index e8cb2fe1..84e5e0a0 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
@@ -495,8 +495,9 @@ noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr
     else []
 
 /-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
-per iteration (commitments, edge, openings, empty verifier message; D8 fixed alternation),
-`4|x|²` moves in all, of which the first `4 n|E|` carry the iterations. -/
+per iteration (commitments, edge, openings, and a verifier message, empty except for the final
+verdict; D8 fixed alternation), `4|x|²` moves in all, of which the first `4 n|E|` carry the
+iterations. -/
 noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
   P := colProverRep Com ℓ
   V := colVerifierRep Com ℓ
@@ -607,7 +608,8 @@ theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExp
     ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
       (colProtocolRep Com ℓ).ProverBounded R B := by
   obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
-  refine ⟨B, fun x y r hist _ => hB x y r hist, fun x y r hist _ => ?_⟩
+  refine ⟨B, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => hB x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => ?_⟩
   show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
   simp only [colProverRep]
   split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _
@@ -878,7 +880,8 @@ theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyE
     obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
     refine ⟨B, fun x hx => ?_⟩
     obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
-    exact ⟨encColoring c, fun r hist => hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
+    exact ⟨encColoring c,
+      fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
       fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
   sound := fun x hx P' z => colProtocol_sound hC x hx P' z
   efficientP := colProver_efficient hC.easy ℓ
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
index c233cc12..955948e3 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
@@ -31,9 +31,10 @@ the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → B
 `ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
 simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.
 
-**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT,
-truncated at `n|E|` attempts and outputting `⊥ = []` on failure, which costs the statistical
-term `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
+**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT
+(D8's definition of `ZK`); it makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as
+the text does (Algorithm 128.7, steps 4–5), and the failure costs the text's own term
+`(1 − 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
 rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
 `2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
 `(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
@@ -318,9 +319,9 @@ theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
     (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))
 
 /-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
-128.8, "`S''` fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the attempts use
-disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability `1 - 1/|E|`
-(`uprob_colSimAttemptH_none`). -/
+128.8, "`S'` [sic: `S''`] fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the
+attempts use disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability
+`1 - 1/|E|` (`uprob_colSimAttemptH_none`). -/
 theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
     (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
     uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
@@ -633,8 +634,9 @@ noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyEx
 the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
 after `n|E|` failures; a single attempt if `E = ∅`.
 
-**Deviation (D8):** truncated at `n|E|` attempts (strict PPT) instead of restarting until
-success. -/
+As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|` attempts, then `fail` (`⊥ = []`).
+**Deviation (D10):** `e'` and the colour pair are rejection-sampled from the tape (defaults `0`
+and `(0, 1)`). -/
 noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
     (x z r : List Bool) : List Bool :=
   let B := (colSimBlock ℓ V').eval x.length
@@ -676,9 +678,10 @@ theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComp
 commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
 Inf-4.4).
 
-**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)` and `N ≥ max ((n₀ + 1)², 4^c · 4)`:
-`n := Nat.sqrt N ≥ n₀` (`Nat.le_sqrt`) and `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`), so
-`N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` once `n ≥ 4^c`, whence `|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
+**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
+`n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
+`N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
+`|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
 theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
     Negligible fun N => μ (Nat.sqrt N) := by
   intro c
@@ -719,48 +722,59 @@ there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| 
 advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
 `ε(|x|)`.
 
-**Deviation (D8, D10):** strict PPT simulator truncated at `n|E|` attempts, rejection-sampled
+**Deviation (D8, D10):** strict PPT simulator (D8's definition of `ZK`), rejection-sampled
 `π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
 undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
 composition, [PS10, §7.2.1], out of scope).
 
-**Proof sketch.** Fix `V'` efficient and take `S` from `exists_colSimulator hC.easy`. Fix
-`Lz` and `D`. Let `B` be the hiding reduction machine of Claim-129.d (`colSimRed` at the
-string level): at parameter `n` it carries in its advice the worst instance
-`(x_n, y_n, z_n)` with `|x_n| = n²`, `|y_n| = 2n`, `|z_n| ≤ Lz(n²)` (`NUPPT.exists_withAdvice`
-with the polynomial bound `add (add (mul var var) (mul (const 2) var)) (Lz.subst (mul var var))`),
-the hybrid index `k_n`, `e₀`, `π₀` and `D.advice n²`; its coins are the other attempts' blocks
-and `D`'s coins (`NUPPT.exists_split`); it runs `V'`'s machine and `D`'s machine
-(`NUPPT.exists_seq`, `NUPPT.exists_comp`, `polyTimeComputable_iterateFind` for the attempts,
-`polyTimeComputable_blockMap ℓ` with `hC.easy` for the commitments, `msgAt` projections by
-`polyTimeComputable_iterate_pairFstD`). `hC.multiHiding var B` gives a negligible `ε_B` with
-`distAdv (multiCom Com v ·) (multiCom Com v' ·) (B.distinguisherL n) ≤ ε_B n` for all `n`-vectors
-`v, v'`. Put
-`ε N := N · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N)) + 2 N² (1/4)^N + N² (1/2)^N + (1/4)^N`,
+**Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
+and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
+the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
+on the encoded optional view (`⊥ ↦ []`).
+
+(1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
+uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
+randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
+`decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
+`some ∘ colRealView`.
+
+If `m > 0`:
+(2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
+`(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
+`statClose_sampleColorPair` — the colour-pair analogue of `statClose_samplePerm3`, still to be
+added: the fill ladder's first step, gate 03g review M3 — and `StatClose.prod` over the blocks).
+(3) `uprob_colSimTruncW_eq`.
+(4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
+`distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
+`CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
+With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
+`cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
+(5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
+`distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.
+
+If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
+`0`). For each fixed `π`, `D`'s advantage is the hiding gap of
+`cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`, with `r_V` fixed by `exists_fixCoins`. Average over `π`.
+If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
+from the real tape when `V'.coinLen 0 > 0`.
+
+The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
+because `|z| ≤ Lz(n²)`: this is where the bound `Lz` is used, see the `Defs.lean` module
+docstring), take those whose fixed reduction (either case) has the largest gap on its own
+vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and openings,
+`pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially bounded by
+`hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform machine once
+(`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins (`NUPPT.exists_reparam_advice`,
+`φ n = n²`). Its acceptance probabilities on `multiCom` samples are the fixed reduction's (coin
+transport along `finCongr`). `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a
+`distAdv` at every `n`), so the hiding terms are at most
+`K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.
+
+Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
 negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
-(`C = 1`), `negligible_two_pow_neg` (with `(1/4)^N ≤ (1/2)^N`), `Negligible.add`,
-`Negligible.const_mul`. Now fix `x = encGraph G`, `y = encColoring c` with `c` proper
-(`R3COL`), `|z| ≤ Lz |x|`, `n` the vertex count, `m = |E|`. If `m = 0` the real view is
-`⟨⟨x,z⟩,⟨r_V,[colCommit (π ∘ c) r, []]⟩⟩` and the simulated one has the all-zero colours, so
-`D`'s advantage is at most `ε_B n` by `hC.multiHiding` applied to a machine `B'` built like
-`B` (absorbed into `B` by a case split on `m` in its advice). Otherwise `n ≥ 2` and the chain is:
-(1) the real view with `π = samplePerm3 |x| …` is within `(1/4)^{|x|}` of the view with a
-uniform `π` (`statClose_samplePerm3`, `StatClose.prod` with `StatClose.refl` for the
-randomness and `V'`'s tape, `StatClose.map` by the view encoding; `exec_succ` three times,
-`decGraph_encGraph`, `decColoring_encColoring`, `colProver`/`colVerifier` unfold to
-`colRealView` with `V com r_V := V'.next x z r_V [com]`); (2) `colSim` is `(Option.map enc
-(colSimTrunc … (n m) w)).getD []` with the `t`-th attempt's coins read from the `t`-th block
-(`colCoinSlice`, `colSimBlock`), within `n m ((1/2)^{|x|} + (1/4)^{|x|})` of the same with
-uniform `(e'_t, (a_t, b_t))` (`statClose_sampleEdgeIdx`, the colour-pair analogue of
-`statClose_samplePerm3`, `StatClose.prod` over the blocks); (3) `uprob_colSimTruncW_eq` makes
-that the law of `colSimTruncW`; (4) `exists_colSimRed_ge` with `N := n m` gives `k, e₀, π₀`
-with `distAdv (truncW) (truncH) D' ≤ n m · distAdv (X) (Y) (colSimRed …)`, and
-`colSimRed … = B.distinguisherL n` up to the coin bijection (`acceptProb_comp_equiv`), so
-`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`; (5) `statClose_colSimTruncH` and
-`one_sub_inv_pow_mul_le_exp` give `distAdv (truncH) (some ∘ colRealView) D' ≤ e^{-n}`
-(`distAdv_le_of_statClose`). The triangle inequality for `distAdv` (`abs_sub_le` on the
-acceptance probabilities) sums the five terms, and `Nat.sqrt |x| = n` (`length_encGraph`,
-`Nat.sqrt_eq`). -/
+(`C = 1`), `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is
+`1`. Use the triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
+(`length_encGraph`, `Nat.sqrt_eq`). -/
 theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
     ZK (colProtocol Com ℓ) R3COL := by
   sorry
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index 61fb0276..f6e3c056 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -423,6 +423,8 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.Commitment.multiHiding
 -- Ruling G3-3: bounded honest prover messages in the proof systems.
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.mono
+-- Round 2, finding 2: the reading lemma of `Protocol.ProverBounded`.
+#print axioms TCSlib.Cryptography.Protocol.proverBounded_iff
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.exists_complete
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.pullback
 #print axioms TCSlib.Cryptography.InteractiveProof.exists_accept
@@ -439,6 +441,11 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 -- Ruling G3-4: perfect zero-knowledge with abort implies statistical ZK (error 2^{-|x|}).
 #print axioms TCSlib.Cryptography.AbortRetry.statClose_retry
 #print axioms TCSlib.Cryptography.AbortRetry.exists_retrySimulator
+-- Round 2, finding 2: the reading lemmas of `AbortRetry.attempt` and `AbortRetry.retry`.
+#print axioms TCSlib.Cryptography.AbortRetry.attempt_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_attempt
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_nil
 #print axioms TCSlib.Cryptography.PerfectZKAbort.statZK
 #print axioms TCSlib.Cryptography.PerfectZKAbort.zk
 #print axioms TCSlib.Cryptography.perfectZK_zeroRounds
diff --git a/machine-library-design.md b/machine-library-design.md
index 1dea9731..52be0e2d 100644
--- a/machine-library-design.md
+++ b/machine-library-design.md
@@ -3087,7 +3087,7 @@ and a statement gate before a second consumer is briefed.
 | H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index (their answers `indicator_inputBitLang`/`indicator_inputLenLang`), the stride decoder `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance), the increment/decrement chain `arm_chain`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` were done in the payback (PR #101, landed 2026-10-15): `Codec/Engine`'s `decodeStride_loop` and `incChain`/`decChain` are instances of `boundedDecodeStride_loop` and `arm_chain` | every received ARM customer through its decider bank; `Codec/Engine` (its decoder and chains are instances); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
 | H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius` directly, `ISCountGenCorrect` transitively) |
 | H13 | **The customer machines**, each with its named consumers and its own reachability notion: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |
-| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`) | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round.** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
+| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`); head envelopes `Clean.envelope` (a clean module's heads stay within `B \|arg\|` cells of the origin at every time), `host_call_envelope` (within `t` cells up to time `t` of a call) and `host_clean_envelope` (`host_clean` with the envelope `B \|arg\|` throughout the call), the coarse envelopes from the time bounds and the unit head moves of `Turing.MultiTapeTM.workTapePos_step_le` | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round; head-envelope clauses added 2026-11-06 (gate 03l round 2, finding 1).** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
 
 **The received ARM machinery, H7–H13** (registered 2026-10-14: the ARM fill gate's round 2,
 finding 5; user decision 3). The rows' public contracts, with file and line, are in

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/replay.log =====

# replay 2026-11-06T00:49:44Z HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans; order=replay-order.txt (downstream2.py of the changed modules, DOWN, + audits/pass-shelat/Checks)
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/SAT rc=0 38s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLipton rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily rc=0 13s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UniformTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifier rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSound rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerComplete rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigma rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Meyer rc=0 7s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CookLevin/Hardness rc=0 385s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Tautology rc=0 10s errors=0 sorry=0
TCSlib/Complexity/ClassNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassOracle/SATOracle rc=0 2s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Inclusions rc=0 29s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHard rc=0 12s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBF rc=0 28s errors=0 sorry=21
TCSlib/Complexity/Randomized/Inclusions rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/Reductions rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/PTMEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPOperator rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPAmplify rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPTIMEThreshold rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoin rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoinHalting rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primality rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Matching rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/NPPoly rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/RPExpected rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Yap rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHosts rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHostsClasses rc=0 45s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroP rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPPIT rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPReduce rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 42s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 23s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 8s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 3s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 4s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 125s errors=0 sorry=0
# done 2026-11-06T01:12:45Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/axioms.log =====

# Axiom prints, gate 03 repair batch, HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba, tree /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (after replay.log)
# Input: axrun/all.lean, generated by g03l-ax/axgen.py over every changed .lean file (changed-lean.txt): 549 #print lines (548 names).
# Base comparison: axrun/base.lean (the same list without the 10 new lemmas) against the untouched #203 tree g03l-oleans (read-only; #203 = BASE in Lean code), axrun/base.out.
# Item B's eight simps equations and the three envelope lemmas: axioms-03l.log.

## Comparison (axcmp.py)
HEAD prints: 548; base prints: 538
sorryAx at HEAD: 100 ; at base: 100
non-standard axioms other than sorryAx at HEAD: []
new names: 10
  NEW TCSlib.Cryptography.AbortRetry.attempt_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_attempt ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_nil ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.Candidates.rejectBlocksL_eq []
  NEW TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL ['Quot.sound']
  NEW TCSlib.Cryptography.Protocol.proverBounded_iff ['propext']
  NEW Turing.ModuleHost.Clean.envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_call_envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_clean_envelope ['Classical.choice', 'Quot.sound', 'propext']
changed axiom sets: 0
missing at HEAD: []
TCSlib.Cryptography.zk_proof_of_witnessRelation ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']
TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']

## HEAD output (axrun/all.out)
'Turing.ModuleHost.first_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.live_prefix' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.clean_iff' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.Clean.envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_install' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_emit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.request_budget' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.state_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.entry_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.hostTM_step_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.guard_add' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.host_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_clean_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_eq_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_ofString_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofString_id_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.blocks_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_blocks_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.Easy.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.eval_yaoBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.eval_yaoRounds' depends on axioms: [propext]
'TCSlib.Cryptography.yaoBlocks_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_38_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.weak_to_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.strong_prod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.weak' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_ofString_id_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_strongOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_weakOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_worstCaseOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermFamily.toFunFamily_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exp_neg_le_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.primesPairEquiv_apply_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_card_primes_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_ne_q' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.ext' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.encodeDistinctPrimes_of_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rejectBlocksL_eq' does not depend on any axioms
'TCSlib.Cryptography.Candidates.rejectBlocksL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_rejectBlocksL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.length_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.dlP_lt_two_pow' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow_dlW' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coprime_dlG_dlP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coe_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expDec_expEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEnc_of_expDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expF_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expValid_dlDefaultIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGenFun_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sampleBelowL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index_of_lt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_D' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.SafePrimeValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlAssumption_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.IsGenerator.orderOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_dlog' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlog_expo' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.two_mul_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_one_ne_one_units' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_half_eq_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_mem_QR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sq_eq_pow_two_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_eq_dlBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlBits_pow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_trial_ge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_shiftInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_dlInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.good_instances' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.FullGroupValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.halfPred_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.halfStr_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_hardCore' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.safe_ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.five_le_safe' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.safe_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_QR_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mem_QR_iff_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_eq_of_mem_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.zpowers_eq_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eq_QR_of_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_sqrt_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_sqTo_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_sq_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_of_uprob_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sq_generator' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.eval_ddhLen' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.length_ddhTuple' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ddhExpo_statClose' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.constSelector_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_pos' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egEncRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egEnc_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egDecStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egDecStr_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egSquareGen_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGroupGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGenMachine_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_valid' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_wellFormed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_secure' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inv_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_easy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.modulusBits_eq_fmult' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.factorProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coins_oneCallFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultWeakPoly' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_weakOneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exists_plantFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.samplePairOut_eq_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_samplePairRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_spec' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_collectionFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.collectionFactorer_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mul_inv_val_modEq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaDec_rsaEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEnc_of_rsaDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleUnitL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.N_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.e_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.d_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaN_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaE_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaValid_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaInvRaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rsaGenErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaBreaker' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaBreaker_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaFromFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorer_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_rsaProb' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsa_imp_factoring' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumDistinctPrimes.ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.oddFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_factoring' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabin_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.oddGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_rabinIndexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinMod_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinDec_rabinEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinEval_spec' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rabinErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinFactorer_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumValid.exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sqTo_bijective_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blum_val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumDec_blumEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumInverter_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_mrExp_mul_mrOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_mul_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mem_mrLiars' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.MRLiar.ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.millerRabin_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.statClose_samplePrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.bitsToNat_eq_listToNat' does not depend on any axioms
'TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins' depends on axioms: [propext]
'TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.simulate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_const_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perfectZK_zeroRounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_attempt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.exists_retrySimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.firstHit_map_getD_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.statClose_retry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.uprob_not_ne_nil_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_exp_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.inv_pow_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.refl' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Isomorphic.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.trans' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.isomorphic_permGraph' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.permGraph_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_isomorphic_both' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_honest_reply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraphAt_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraph_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertices_length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertexCount_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Liso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Lniso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_mem_Lniso_of_mem_Liso' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Riso_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.permCoinLen_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_samplePerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_mul_permFailBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_cheat_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_rep_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gni_rep_cheat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_honest_reply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocolRep_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gniProver_next_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_vTapeSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.permCoinLen_le_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_giBitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.exec_repViews' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.length_Vs' depends on axioms: [propext]
'TCSlib.Cryptography.GI.getD_Vs_even' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.getD_Vs_odd' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOf_congr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_prefixLT' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_init_prefixLE' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.prefixLE_last' does not depend on any axioms
'TCSlib.Cryptography.GI.giVerifierRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProtocolRep_outV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.honest_views' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.encodeMsgs_nil' does not depend on any axioms
'TCSlib.Cryptography.Strategy.encodeMsgs_cons' does not depend on any axioms
'TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.Efficient.exists_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.ReadsPrefix.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.moverIsV_true' does not depend on any axioms
'TCSlib.Cryptography.moverIsV_false' does not depend on any axioms
'TCSlib.Cryptography.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.exec_length' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Protocol.proverBounded_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.ProverBounded.mono' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.withV_V' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_P' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_rounds' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_verifierFirst' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_self' does not depend on any axioms
'TCSlib.Cryptography.Protocol.outV_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outP_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.transcript_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_withV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.exists_proverCoins_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.exists_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_witnessLanguage' does not depend on any axioms
'TCSlib.Cryptography.mem_witnessSet' does not depend on any axioms
'TCSlib.Cryptography.WitnessRelation.eq_witnessLanguage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_witnessRelation_of_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.EfficientProverProofErr.efficientProverProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.EfficientProverProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_outV' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_readsPrefix' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_proverBounded' depends on axioms: [propext]
'TCSlib.Cryptography.npProtocol_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NP_subset_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.coinLen_pullback' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.pullback_outV' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.pullback_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_owp_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encGraph_mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_edgeList_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeOf_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.exists_edgeOf_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_eq_some_edgeOf' depends on axioms: [propext]
'TCSlib.Cryptography.edgeAt_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_isSome' does not depend on any axioms
'TCSlib.Cryptography.edgeAt_eq_none_iff' depends on axioms: [propext]
'TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exp_neg_le_inv_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decColor_encColor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encColor_getD_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.padColor_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.sampleEdgeIdx_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeIdxOfMsg_edgeMsg' depends on axioms: [propext]
'TCSlib.Cryptography.edgeIdxOfMsg_lt' does not depend on any axioms
'TCSlib.Cryptography.statClose_samplePerm3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_sampleEdgeIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.msgAt_encodeMsgs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.committedColor_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_bad_edge' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_col_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colWellFormed_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_multiCom_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.R3COL_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_efficientProverProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_interactiveProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.card_colorPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perm3_ext_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colorPairEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.simColorsW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.firstSome_eq_none_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_colSimTruncH' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_hvzk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zeroKnowledgeProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/seal.log =====

## Part 1: consumers of TCSlib.Cryptography.Protocol.ProverBounded (whole files sealed)

TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (2 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:236:22: error: Function expected at
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:470:2: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/NP.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_NP_sealed_control.lean:279:8: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:928:39: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:932:42: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:938:3: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:611:13: error: Application type mismatch: The argument
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:612:2: error: No goals to be solved
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:882:40: error: Function expected at
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_Soundness_sealed_control.lean:322:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_SoundnessRepGI_sealed_control.lean:478:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

## Part 2: new proofs that read another file's definitions (copies in a SealTest namespace)

TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean: Clean.envelope, host_call_envelope, host_clean_envelope
  seal: ofWords stateWord runFrom step
  sealed current: PASS
  control (Clean.envelope with the seam's head position read by `rfl` through `Cfg.ofWords`): FAIL (1 error lines); expected fail: as expected
    ctl: ModuleHost_envelopes_sealed_control.lean:29:89: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/ZeroKnowledge/Defs.lean: attempt_eq, retry_eq, retry_eq_attempt, retry_eq_nil
  seal: firstIdx layout inParam inArg inCoins output coinLen
  sealed current: PASS
  control (the copies plus one `rfl` read of `firstIdx` (seal-active check)): FAIL (1 error lines); expected fail: as expected
    ctl: Defs_AbortRetry_sealed_control.lean:41:45: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/Candidates/DiscreteLog.lean: sampleBelowL_eq_rejectBlocksL
  seal: rejectBlocksL
  sealed current: PASS
  control (the lemma proved by `funext r; rfl`, reading `rejectBlocksL` through its body): FAIL (1 error lines); expected fail: as expected
    ctl: DiscreteLog_sampleBelowL_sealed_control.lean:15:2: error: Tactic `rfl` failed: The left-hand side
  the same control unsealed: PASS (so its sealed failure is due to the seal)


## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/lint.log =====

# Lint (check 4), HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba vs BASE 092083cd10be7a284db4e97fcf42eddb8296edf7 (archive in g03batch/basetree)
# lint.sh: scripts/style_lint.py on the 21 changed .lean files; scripts/campaign_style_lint.py --check8b per directory, filtered to them.
# Normalized diff base -> head (line numbers masked):
#   26c26,27
#   < INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          548 lines; 16 public / 13 private declarations
#   ---
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
#   28,29c29,30
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines > target 600
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines; 44 public / 6 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
#   45,56c46,57
#   < INFO  TCSlib/Cryptography/Candidates/Concrete.lean             561 lines; 39 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines; 65 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  585 lines; 45 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines; 60 public / 4 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines; 47 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines; 85 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines; 96 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
#   58,60c59,61
#   < INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          308 lines; 11 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines > target 600
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines; 30 public / 30 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
#   67c68
#   < WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       10 public def(s) without a lemma beside them (check 8): Efficient, ProverBounded, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   ---
#   > WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   73,86c74,87
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  981 lines; 68 public / 7 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       464 lines; 49 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 544 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines; 23 public / 5 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
#   89,90c90,91
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   94,98c95,99
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations
# => no new WARN/FAIL; Interaction.lean's check-8 list loses ProverBounded; ModuleHost.lean passes the 600-line target (INFO, 663 lines); the rest are line counts.

### HEAD raw
### scripts/style_lint.py on the changed .lean files

1 findings in 21 files



















TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:723: `colProtocol_sound` proof is 99 lines, no **Proof sketch.**

### scripts/campaign_style_lint.py --check8b, per directory, filtered to the changed files
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
WARN  TCSlib/Cryptography/Asymptotic/OneWay.lean                5 public def(s) without a lemma beside them (check 8): Easy, LengthRegular, OneWayPermutation, strOutLen, yaoRounds
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
FAIL  TCSlib/Cryptography/Candidates/ElGamal.lean              line 749: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 145: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 347: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 532: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 805: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 892: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 927: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 951: `sorry` without a proof sketch in the preceding docstring
WARN  TCSlib/Cryptography/Candidates/Concrete.lean             1 public def(s) without a lemma beside them (check 8): default
WARN  TCSlib/Cryptography/Candidates/DiscreteLog.lean          11 public def(s) without a lemma beside them (check 8): DLAssumption, DLHard, FullLength, FullLengthExcept, SafePrimeValid, WellFormedIndex, dlDefaultIndex, dlG, dlM, expSampleRaw, expUnit
WARN  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  9 public def(s) without a lemma beside them (check 8): FullDLAssumption, FullGroupValid, IsGenerator, dlInverter, dlRoot, halfBit, halfOracle, majOracle, shiftInverter
WARN  TCSlib/Cryptography/Candidates/ElGamal.lean              15 public def(s) without a lemma beside them (check 8): DDHAssumption, Secure, challenge, ddhLen, ddhRandom, ddhReal, ddhTuple, egCanon, egEncParts, egEncRaw, egGenCoins, egGenParts, egGenRaw, egGroupGenRaw, egGroupParts
WARN  TCSlib/Cryptography/Candidates/Factoring.lean            7 public def(s) without a lemma beside them (check 8): FactoringAssumption, fmultBlocks, fmultWeakPoly, plantFactor, prodInverter, samplePairRaw, samplePrimeL
WARN  TCSlib/Cryptography/Candidates/RSA.lean                  19 public def(s) without a lemma beside them (check 8): RSAAssumption, RSAValid, rsaBlock, rsaEncVal, rsaFromFactorRaw, rsaGenCoins, rsaGenErr, rsaGenOut, rsaGenParams, rsaGenRaw, rsaIndexOf, rsaInput, rsaInvRaw, rsaPermAt, rsaSampleCoins, rsaSampleRaw, rsaTrapOf, rsaTrials, unitSampleStr
WARN  TCSlib/Cryptography/Candidates/Rabin.lean                28 public def(s) without a lemma beside them (check 8): BlumDensity, BlumFactoringAssumption, BlumValid, blumDefault, blumEnc, blumEncVal, blumInvNat, blumInvRaw, blumPermAt, blumSampleRaw, oddDefault, rabinEnc, rabinErr, rabinF, rabinFactorRaw, rabinFactorStep, rabinGenCoins, rabinGenOut, rabinGenParams, rabinGenRaw, rabinIndexOf, rabinPrimeCoins, rabinRootRaw, rabinRootStep, rabinSampleRaw, rabinTrials, samplePrimePL, smallDistinctPrimes
INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
WARN  TCSlib/Cryptography/NumberTheory/Primality.lean          6 public def(s) without a lemma beside them (check 8): MRLiar, chunk, listToNat, mrExp, mrLiars, samplePrimeCoins
INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete`
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs`
WARN  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              4 public def(s) without a lemma beside them (check 8): HVZK, PerfectZKAbort, StatZK, ZK
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  12 public def(s) without a lemma beside them (check 8): Liso, Lniso, coinSlice, gniProtocolRep, gniProver, instanceG, instanceG, permFailBound, prefixLE, prefixLT, samplePerm, wellFormedInstance
WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
WARN  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 3 public def(s) without a lemma beside them (check 8): IP, witnessLanguage, witnessSet
WARN  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                1 public def(s) without a lemma beside them (check 8): LevinNPHard
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/statements.txt =====

# Statement diff: decls.py (copied from g03l-fix) over every changed .lean file, BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 vs HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba
# Normalized statement text (comments stripped) of every public declaration, compared by full name.

## Summary: 10 added, 2 changed, 0 removed

## Added
- Turing.ModuleHost.Clean.envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:239)
    theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ} (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
- Turing.ModuleHost.host_call_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:567)
    theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) : ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (t : ℤ)
- Turing.ModuleHost.host_clean_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:642)
    theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ) (h : Clean (M i) f g B) (x arg pre : List Bool) : ∃ t, 0 < t ∧ t ≤ B arg.length ∧ (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state ≠ some (.inl c)) ∧ (hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t = {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧ ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (B arg.length : ℤ)
- TCSlib.Cryptography.Candidates.rejectBlocksL_eq (theorem, TCSlib/Cryptography/Candidates/Concrete.lean:525)
    theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : rejectBlocksL E k B T r = (List.range T).findSome? fun t => if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k)) else none
- TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL (theorem, TCSlib/Cryptography/Candidates/DiscreteLog.lean:476)
    theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) : sampleBelowL m k B T = rejectBlocksL (· < m) k B T
- TCSlib.Cryptography.AbortRetry.attempt_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:315)
    theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) : attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) [] (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take (S.coinLen (NUPPT.inParam w).length)))
- TCSlib.Cryptography.AbortRetry.retry_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:334)
    theorem retry_eq (S : NUPPT) (w : List Bool) : retry S w = if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length < (NUPPT.inParam w).length then attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) else []
- TCSlib.Cryptography.AbortRetry.retry_eq_attempt (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:347)
    theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ} (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ []) (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i
- TCSlib.Cryptography.AbortRetry.retry_eq_nil (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:359)
    theorem retry_eq_nil {S : NUPPT} {w : List Bool} (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = []
- TCSlib.Cryptography.Protocol.proverBounded_iff (theorem, TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:338)
    theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : π.ProverBounded R B ↔ ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

## Changed (both by ruling R-03e-r2-1 (A), item C #4)
- TCSlib.Cryptography.zk_proof_of_witnessRelation (TCSlib/Cryptography/ZeroKnowledge/NP.lean:679->682)
    OLD: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
- TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp (TCSlib/Cryptography/ZeroKnowledge/NP.lean:698->701)
    OLD: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)

## Removed
(none)

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/maintainer-recheck.log =====

# maintainer re-check at 73751f5747d8c0a57aba9939cac8bb16f87ba2ba: 8 key modules, one at a time in import order, on a copy of the worker's tree
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
audits/pass-shelat/Checks rc=0 121s errors=0 sorry=0
# done 2026-11-06T01:22:50Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/base-sync.log =====

# base-sync 2026-11-06T00:22:41Z BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (copy of g03l-oleans, #203 Lean files)
TCSlib/Complexity/Randomized/PPT rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 75s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 10s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 63s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 77s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 10s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 3s errors=0 sorry=0
# done 2026-11-06T00:32:55Z

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the simulator

The zero-knowledge half of [PS10, Proposition 127.6]: the simulator of [PS10, Algorithm 128.7]
for one iteration of [PS10, Protocol 127.5] (Alg-128.7), its efficiency (Claim-128.a), and
[PS10, Proposition 128.8] (Prop-128.8) through the hybrid chain of the text's proof,
corrected: the simulator `S` guesses an edge `e'` and a pair of distinct colours, commits to
them at the endpoints of `e'` and to the colour `0` elsewhere, runs `V*` and succeeds if `V*`
asks for `e'`; `S'` (Claim-129.a) uses the witness and a uniform colour permutation `π` at the
two endpoints instead of a uniform distinct pair — identically distributed by the bijection
`π ↦ (π a, π b)` between `S₃` and the distinct pairs (Lem-129.b); `S''` (Claim-129.c) commits
like the honest prover to `π (c k)` for **all** `k` but keeps the restart rule, so each attempt
succeeds with probability exactly `1/|E|` and, conditioned on success, outputs the honest view;
`S' ≈ S''` (Claim-129.d) by a hybrid over the `n|E|` attempts and the multi-value hiding of
the commitment (`Commitment.multiHiding`).

Two layers (D2): the *concrete* layer works over typed coins (`Fin |E|`, `Equiv.Perm (Fin 3)`,
the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → Bool`, and the coins
`ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.

**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT
(D8's definition of `ZK`); it makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as
the text does (Algorithm 128.7, steps 4–5), and the failure costs the text's own term
`(1 − 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
`2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
`(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
all-zero colours and succeeds at once.

## Main definitions

* `TCSlib.Cryptography.ColorPair`, `TCSlib.Cryptography.colorPairEquiv` — the distinct colour
  pairs and the bijection `S₃ ≃ ColorPair` (Lem-129.b).
* `TCSlib.Cryptography.colRealView` — the view of `V*` in one honest iteration (typed).
* `TCSlib.Cryptography.colSimAttempt`, `TCSlib.Cryptography.colSimAttemptW`,
  `TCSlib.Cryptography.colSimAttemptH` — one attempt of `S`, `S'`, `S''`;
  `TCSlib.Cryptography.colSimTrunc`, `colSimTruncW`, `colSimTruncH` — their `N`-fold truncations;
  `TCSlib.Cryptography.colSimHyb`, `TCSlib.Cryptography.colSimAttemptPlanted`,
  `TCSlib.Cryptography.colSimRed` — the hybrids and the hiding reduction (Claim-129.d).
* `TCSlib.Cryptography.colSim`, `TCSlib.Cryptography.colSimCoins` — the string simulator
  [PS10, Algorithm 128.7] (Alg-128.7).

## Main results

* `TCSlib.Cryptography.uprob_colSimTruncW_eq` — `S ≡ S'` (Claim-129.a, proved).
* `TCSlib.Cryptography.uprob_colSimAttemptH_none`, `uprob_colSimAttemptH_some`,
  `TCSlib.Cryptography.statClose_colSimTruncH` — `S''` fails with probability `(1 - 1/|E|)^N`
  and is perfect given success (Claim-129.c).
* `TCSlib.Cryptography.exists_colSimRed_ge` — `S' ≈ S''` by hybrids (Claim-129.d).
* `TCSlib.Cryptography.exists_colSimulator` — the simulator is a uniform PPT (Claim-128.a).
* `TCSlib.Cryptography.col_zk` — **[PS10, Proposition 128.8]**: the protocol is
  zero-knowledge for `R_3COL`; `TCSlib.Cryptography.col_zeroKnowledgeProof` — **[PS10,
  Proposition 127.6]** assembled (Prop-127.6).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6, Algorithm 128.7, Proposition 128.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (hybrid arguments at the concrete layer).
-/

namespace TCSlib.Cryptography

open Complexity Turing ColSimLemmas

/-! ### Distinct colour pairs (Lem-129.b) -/

/-- The ordered pairs of distinct colours, the simulator's guess `(c'_{i'}, c'_{j'})` of
[PS10, Algorithm 128.7, step 1]. -/
abbrev ColorPair : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- There are six distinct colour pairs. -/
theorem card_colorPair : Fintype.card ColorPair = 6 := by decide

/-- A permutation of the three colours is determined by its values on two distinct colours. -/
theorem perm3_ext_of_ne : ∀ a b : Fin 3, a ≠ b → ∀ π σ : Equiv.Perm (Fin 3),
    π a = σ a → π b = σ b → π = σ := by
  decide

/-- **`π ↦ (π a, π b)` is a bijection from `S₃` to the distinct colour pairs** for `a ≠ b`
[PS10, proof of Proposition 128.8, "`S` and `S'` are identically distributed"] (Lem-129.b):
injective by `perm3_ext_of_ne`, bijective since both sides have six elements. -/
noncomputable def colorPairEquiv {a b : Fin 3} (hab : a ≠ b) : Equiv.Perm (Fin 3) ≃ ColorPair :=
  Equiv.ofBijective (fun π => ⟨(π a, π b), fun h => hab (π.injective h)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun π σ h => perm3_ext_of_ne a b hab π σ (congrArg (fun p : ColorPair => p.1.1) h)
        (congrArg (fun p : ColorPair => p.1.2) h),
        by rw [Fintype.card_perm, Fintype.card_fin, card_colorPair]; rfl⟩)

/-- Unfolding of `colorPairEquiv`. -/
@[simp] theorem colorPairEquiv_apply {a b : Fin 3} (hab : a ≠ b) (π : Equiv.Perm (Fin 3)) :
    (colorPairEquiv hab π : Fin 3 × Fin 3) = (π a, π b) := rfl

/-! ### The typed views of one iteration -/

/-- The simulator's colouring [PS10, Algorithm 128.7, step 1]: the guessed pair at the
endpoints of the guessed edge `p = (i', j')`, the colour `0` ("`1`" in the text) elsewhere. -/
def simColors {n : ℕ} (p : Fin n × Fin n) (ab : ColorPair) : Fin n → Fin 3 :=
  fun k => if k = p.1 then ab.1.1 else if k = p.2 then ab.1.2 else 0

/-- The colouring of the hybrid simulator `S'` [PS10, proof of Proposition 128.8]: the
witness colours permuted by `π` at the endpoints of `p`, the colour `0` elsewhere. -/
def simColorsW {n : ℕ} (p : Fin n × Fin n) (π : Equiv.Perm (Fin 3)) (c : Fin n → Fin 3) :
    Fin n → Fin 3 :=
  fun k => if k = p.1 then π (c p.1) else if k = p.2 then π (c p.2) else 0

/-- `S'`'s colouring is `S`'s colouring at the pair `(π (c i'), π (c j'))`. -/
theorem simColorsW_eq {n : ℕ} (p : Fin n × Fin n) (π : Equiv.Perm (Fin 3)) {c : Fin n → Fin 3}
    (hp : c p.1 ≠ c p.2) : simColorsW p π c = simColors p (colorPairEquiv hp π) := rfl

/-- A typed view of `V*` in one iteration: its coins, the commitment message and the
prover's last message (the common input and `z` being fixed). -/
abbrev ColView (ρ : Type*) : Type _ := ρ × List Bool × List Bool

section Typed

variable (Com : List Bool → List Bool) {n : ℕ} (ℓn : ℕ) (G : Graph n) {ρ : Type*}

/-- The view of `V*` (reply function `V`, coins `ρ`) in one honest iteration of
[PS10, Protocol 127.5] with witness `c`, prover coins `(π, r)`: the commitments to `π (c i)`,
and the opening of the edge `V*` names (or `[]` if `E = ∅`). -/
def colRealView (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) : ColView ρ :=
  let c' : Fin n → Fin 3 := fun i => w.1.1 (c i)
  let com := colCommit Com n ℓn c' w.1.2
  (w.2, com, match edgeAt G (edgeIdxOfMsg (edgeCount G) (V com w.2)) with
    | some p => colOpen c' w.1.2 p
    | none => [])

/-- One attempt of the simulator [PS10, Algorithm 128.7] (Alg-128.7, typed) on the coins
`((e', (a, b)), r, r_{V*})`: commit to `simColors (edgeOf G e') (a, b)`, run `V*`, and output
the view if `V*` names the edge `e'`, `none` otherwise. -/
def colSimAttempt (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ) : Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' := simColors p w.1.1.2
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- One attempt of the hybrid simulator `S'` [PS10, proof of Proposition 128.8]: as
`colSimAttempt` with the colours `(π (c i'), π (c j'))` at the endpoints for a uniform `π`. -/
def colSimAttemptW (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' := simColorsW p w.1.1.2 c
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- One attempt of the hybrid simulator `S''` [PS10, proof of Proposition 128.8]: commit to
`π (c k)` for every `k` (like the honest prover), but output the view only if `V*` names the
guessed edge `e'`. -/
def colSimAttemptH (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' : Fin n → Fin 3 := fun i => w.1.1.2 (c i)
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- The coin bijection of Claim-129.a: `((e', π), r, ρ) ↦ ((e', (π (c i'), π (c j'))), r, ρ)`
for a proper colouring `c` (`colorPairEquiv` fibrewise over `e'`). -/
noncomputable def simCoinsEquiv {c : Fin n → Fin 3} (hc : ProperColoring G c) :
    ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ ≃
      ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ :=
  Equiv.prodCongr (Equiv.prodCongr
    (Equiv.prodCongrRight fun e => colorPairEquiv (hc _ _ (edgeOf_adj G e))) (Equiv.refl _))
    (Equiv.refl ρ)

/-- **`S ≡ S'`, one attempt** [PS10, proof of Proposition 128.8, "it directly follows that
`S(x, z)` and `S'(x, z, y)` are identically distributed"] (Claim-129.a): for a proper colouring
`c` the attempts of `S'` and `S` have the same law — they agree pointwise along the coin
bijection `simCoinsEquiv` (`uprob_comp_equiv`). -/
theorem uprob_colSimAttemptW_eq [Fintype ρ] {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (V : List Bool → ρ → List Bool) (T : Option (ColView ρ) → Prop) :
    uprob (fun w => T (colSimAttemptW Com ℓn G c V w)) =
      uprob (fun w => T (colSimAttempt Com ℓn G V w)) := by
  rw [← uprob_comp_equiv (simCoinsEquiv ℓn G (ρ := ρ) hc)]
  rfl

/-! ### The truncated simulators -/

/-- The first `some` among `N` optional values (the output of the first successful attempt). -/
def firstSome {α : Type*} {N : ℕ} (f : Fin N → Option α) : Option α :=
  (List.finRange N).findSome? f

/-- `firstSome` is `none` iff every attempt fails. -/
theorem firstSome_eq_none_iff {α : Type*} {N : ℕ} (f : Fin N → Option α) :
    firstSome f = none ↔ ∀ t, f t = none := by
  unfold firstSome
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The simulator truncated at `N` attempts with independent coins [PS10, Algorithm 128.7,
steps 4–5] (Alg-128.7, typed): the first successful attempt's view, `none` (`fail`) if all
`N` fail. -/
def colSimTrunc (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttempt Com ℓn G V (w t)

/-- `S'` truncated at `N` attempts. -/
def colSimTruncW (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttemptW Com ℓn G c V (w t)

/-- `S''` truncated at `N` attempts. -/
def colSimTruncH (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttemptH Com ℓn G c V (w t)

/-- **`S ≡ S'`, `N` attempts** (Claim-129.a): the truncated `S'` and `S` have the same law
(`simCoinsEquiv` on every attempt, `Equiv.piCongrRight`). -/
theorem uprob_colSimTruncW_eq [Fintype ρ] {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (V : List Bool → ρ → List Bool) (N : ℕ) (T : Option (ColView ρ) → Prop) :
    uprob (fun w => T (colSimTruncW Com ℓn G c V N w)) =
      uprob (fun w => T (colSimTrunc Com ℓn G V N w)) := by
  rw [← uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin N => simCoinsEquiv ℓn G (ρ := ρ) hc)]
  rfl

/-- **An attempt of `S''` fails with probability exactly `1 - 1/|E|`** [PS10, proof of
Proposition 128.8, "as `i, j` and `i', j'` are independently chosen"] (Claim-129.c (i)).

**Proof sketch.** The commitment message and `V*`'s reply do not depend on `e'`, so after
reindexing the coins as `Fin |E| × ((S₃ × randomness) × ρ)` (`Equiv.prodAssoc`,
`uprob_comp_equiv`) and conditioning on the second component (`uprob_prod`), the failure event
is `e' ≠ f(rest)` for a fixed index, of probability `1 - 1/|E|`
(`OneWay.uprob_eq_one_div_card`, `uprob_not`, `edgeIdxOfMsg_lt`). -/
theorem uprob_colSimAttemptH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) :
    uprob (fun w => colSimAttemptH Com ℓn G c V w = none) = 1 - 1 / (edgeCount G : ℝ) := by
  rw [← uprob_comp_equiv (attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm]
  have key : ∀ z : ((Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) × Fin (edgeCount G),
      colSimAttemptH Com ℓn G c V
          ((attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm z) = none ↔
        ¬ edgeIdxOfMsg (edgeCount G)
          (V (colCommit Com n ℓn (fun i => z.1.1.1 (c i)) z.1.1.2) z.1.2) = (z.2 : ℕ) := by
    rintro ⟨⟨⟨π, r⟩, ρ₀⟩, e⟩
    show (if edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) = (e : ℕ)
        then some (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          colOpen (fun i => π (c i)) r (edgeOf G e)) else none) = none ↔ _
    by_cases h : edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
      (e : ℕ)
    · rw [if_pos h]
      exact ⟨fun h' => (Option.some_ne_none _ h').elim, fun h' => (h' h).elim⟩
    · rw [if_neg h]
      exact ⟨fun _ => h, fun _ => rfl⟩
  rw [OneWay.uprob_congr key]
  exact uprob_ne_idx hm (fun a : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
    edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => a.1.1 (c i)) a.1.2) a.2))
    (fun a => edgeIdxOfMsg_lt hm _)

/-- **Conditioned on success, an attempt of `S''` is the honest view** [PS10, proof of
Proposition 128.8, "the following distributions are identical"] (Claim-129.c (ii)): for every
test set `T`, the probability that an attempt succeeds with a view in `T` is `1/|E|` times the
probability that the real view lies in `T`.

**Proof sketch.** On the coins `((e', π), r, ρ)` the attempt commits exactly as the honest
prover with `(π, r)`; it succeeds iff `V*`'s reply decodes to `e'` and then outputs
`colRealView (π, r, ρ)` (`edgeAt_eq_some_edgeOf` identifies the opened edge). Reindex as in
`uprob_colSimAttemptH_none` and condition on `(π, r, ρ)`: the inner probability over `e'` is
`1/|E|` if `T (colRealView …)` holds and `0` otherwise (`OneWay.uprob_eq_one_div_card`,
`uprob_false`); `uprob_prod` and `uexp` linearity give the product. -/
theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (T : ColView ρ → Prop) :
    uprob (fun w => ∃ v, colSimAttemptH Com ℓn G c V w = some v ∧ T v) =
      1 / (edgeCount G : ℝ) *
        uprob (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
          T (colRealView Com ℓn G c V w)) := by
  rw [← uprob_comp_equiv (attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm]
  have key : ∀ z : ((Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) × Fin (edgeCount G),
      (∃ v, colSimAttemptH Com ℓn G c V
          ((attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm z) = some v ∧ T v) ↔
        (edgeIdxOfMsg (edgeCount G)
          (V (colCommit Com n ℓn (fun i => z.1.1.1 (c i)) z.1.1.2) z.1.2) = (z.2 : ℕ) ∧
          T (colRealView Com ℓn G c V z.1)) := by
    rintro ⟨⟨⟨π, r⟩, ρ₀⟩, e⟩
    show (∃ v, (if edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
        (e : ℕ) then some (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          colOpen (fun i => π (c i)) r (edgeOf G e)) else none) = some v ∧ T v) ↔
      (edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) = (e : ℕ) ∧
        T (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          match edgeAt G (edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀))
            with
          | some p => colOpen (fun i => π (c i)) r p
          | none => []))
    by_cases h : edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
      (e : ℕ)
    · rw [if_pos h, h, edgeAt_eq_some_edgeOf]
      exact ⟨fun ⟨v, hv, hT⟩ => ⟨rfl, by rw [← Option.some.inj hv] at hT; exact hT⟩,
        fun ⟨_, hT⟩ => ⟨_, rfl, hT⟩⟩
    · rw [if_neg h]
      exact ⟨fun ⟨v, hv, _⟩ => (Option.noConfusion hv), fun ⟨h', _⟩ => (h h').elim⟩
  rw [OneWay.uprob_congr key]
  exact uprob_eq_idx_and hm (fun a : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
    edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => a.1.1 (c i)) a.1.2) a.2))
    (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))

/-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
128.8, "`S'` [sic: `S''`] fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the
attempts use disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability
`1 - 1/|E|` (`uprob_colSimAttemptH_none`). -/
theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
    uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
  unfold colSimTruncH
  rw [OneWay.uprob_congr fun w => firstSome_eq_none_iff _,
    OneWay.uprob_pi_forall (ι := Fin N) (fun w => colSimAttemptH Com ℓn G c V w = none),
    uprob_colSimAttemptH_none Com ℓn G hm c V, Fintype.card_fin]

/-- **The truncated `S''` is statistically `(1 - 1/|E|)^N`-close to the honest view**
[PS10, proof of Proposition 128.8, "`view_{V*}` and `S''` can be distinguished with probability
at most `O(e^{-n})`"] (Claim-129.c): for every test set `T` of optional views,
`|Pr[T(S''_N)] - Pr[T(some view)]| ≤ (1 - 1/|E|)^N`.

**Proof sketch.** Decompose the event `T(S''_N)` by the index of the first successful attempt
(`firstSome`/`List.findSome?` on `List.finRange N`): the attempts have disjoint coins, so by
`uprob_prod`/`OneWay.uprob_update` the `t`-th term is `(1 - 1/|E|)^t · Pr[∃ v, attempt = some v ∧
T (some v)] = (1 - 1/|E|)^t (1/|E|) Pr[T (some view)]` (`uprob_colSimAttemptH_some`,
`uprob_colSimAttemptH_none`); the geometric sum gives
`Pr[T(S''_N)] = (1 - (1 - 1/|E|)^N) Pr[T (some view)] + (1 - 1/|E|)^N [T none]`
(`uprob_colSimTruncH_none`), within `(1 - 1/|E|)^N` of `Pr[T (some view)]`. -/
theorem statClose_colSimTruncH [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
    StatClose (colSimTruncH Com ℓn G c V N)
      (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
        some (colRealView Com ℓn G c V w))
      ((1 - 1 / (edgeCount G : ℝ)) ^ N) := by
  have hθ : 0 ≤ 1 - 1 / (edgeCount G : ℝ) := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast hm
  haveI : Nonempty (AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :=
    ⟨(((⟨0, hm⟩, 1), fun _ _ => false), Classical.arbitrary ρ)⟩
  exact statClose_truncAttempts (colSimAttemptH Com ℓn G c V) (colRealView Com ℓn G c V) hθ
    (uprob_colSimAttemptH_none Com ℓn G hm c V)
    (fun T => by rw [uprob_colSimAttemptH_some Com ℓn G hm c V T]; congr 1; ring) N

/-! ### The hybrids `S' ≈ S''` (Claim-129.d) -/

/-- The `k`-th hybrid simulator [PS10, proof of Proposition 128.8, "`S_k` proceeds as `S''` in
the first `k` iterations and like `S'` in the remaining ones"]: attempts `< k` are `S''`
attempts, the others `S'` attempts. -/
def colSimHyb (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N k : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => if (t : ℕ) < k then colSimAttemptH Com ℓn G c V (w t)
    else colSimAttemptW Com ℓn G c V (w t)

/-- The zeroth hybrid is `S'`. -/
theorem colSimHyb_zero (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    colSimHyb Com ℓn G c V N 0 w = colSimTruncW Com ℓn G c V N w := by
  simp [colSimHyb, colSimTruncW]

/-- The `N`-th hybrid is `S''`. -/
theorem colSimHyb_self (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    colSimHyb Com ℓn G c V N N w = colSimTruncH Com ℓn G c V N w := by
  simp [colSimHyb, colSimTruncH]

/-- The planted attempt of the hiding reduction: with the guessed edge `e₀` and permutation
`π₀` fixed, the commitments at the endpoints of `e₀` are made by the reduction itself (to
`π₀ (c i')`, `π₀ (c j')`, which `S'` and `S''` share) and all other commitments are read from
the challenger's vector `cv` (`msgAt`); the restart rule and the opening are as in the
attempts. -/
def colSimAttemptPlanted (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3)) (cv : List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G e₀
  let c' : Fin n → Fin 3 := fun i => π₀ (c i)
  let com := Strategy.encodeMsgs (List.ofFn fun i =>
    if i = p.1 ∨ i = p.2 then Com (pairEncode (List.ofFn (padColor n (c' i))) (List.ofFn (w.1.2 i)))
    else msgAt cv i)
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (e₀ : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- The hiding reduction at hybrid index `k` with the worst `(e₀, π₀)` planted
[PS10, proof of Proposition 128.8, the reduction to the hiding property] (Claim-129.d): on a
challenge commitment vector `cv` it runs attempts `< k` as `S''`, attempt `k` as the planted
attempt on `cv`, the later attempts as `S'`, and hands the first success to `D`. -/
def colSimRed {ρ' : Type*} (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3))
    (D : Option (ColView ρ) → ρ' → Bool) :
    List Bool →
      (Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) × ρ' →
        Bool :=
  fun cv z => D (firstSome fun t =>
    if (t : ℕ) < k then colSimAttemptH Com ℓn G c V (z.1 t)
    else if t = k then colSimAttemptPlanted Com ℓn G c V e₀ π₀ cv (z.1 t)
    else colSimAttemptW Com ℓn G c V (z.1 t)) z.2

/-- The `S'` colouring at an endpoint of `p` is the permuted witness colour. -/
private theorem simColorsW_of_mem {m : ℕ} (p : Fin m × Fin m) (π : Equiv.Perm (Fin 3))
    (c : Fin m → Fin 3) {i : Fin m} (hi : i = p.1 ∨ i = p.2) :
    simColorsW p π c i = π (c i) := by
  unfold simColorsW
  rcases hi with rfl | rfl
  · rw [if_pos rfl]
  · by_cases h : p.2 = p.1
    · rw [if_pos h, h]
    · rw [if_neg h, if_pos rfl]

/-- **The planted attempt on the `S'` commitment vector is an `S'` attempt** with the merged
randomness (the reduction's at the endpoints of the planted edge, the challenger's elsewhere)
and the planted `(e₀, π₀)`.

**Proof sketch.** The commitment messages agree position by position: at the endpoints both
commit to `π₀ (c i)` (`simColorsW_of_mem`) with the attempt's randomness, elsewhere the planted
attempt reads `Com ⟨pad (simColorsW … i), r' i⟩` off the challenge (`msgAt_multiCom`) and
`mergeAt` selects `r' i`; the openings agree since `mergeAt` is the attempt's randomness at the
endpoints (`mergeAt_fst`, `mergeAt_snd`); the success test and the output then coincide. -/
private theorem colSimAttemptPlanted_W (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (ep : Fin (edgeCount G) × Equiv.Perm (Fin 3)) (r' : Fin n → Fin ℓn → Bool)
    (w : AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :
    colSimAttemptPlanted Com ℓn G c V ep.1 ep.2
        (multiCom Com (fun i => padColor n (simColorsW (edgeOf G ep.1) ep.2 c i)) r') w =
      colSimAttemptW Com ℓn G c V ((ep, mergeAt (edgeOf G ep.1) w.1.2 r'), w.2) := by
  set p := edgeOf G ep.1 with hp
  have hcom : Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i) =
      colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r') := by
    show _ = Strategy.encodeMsgs (List.ofFn fun i =>
      Com (pairEncode (List.ofFn (padColor n (simColorsW p ep.2 c i)))
        (List.ofFn (mergeAt p w.1.2 r' i))))
    congr 2
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · rw [if_pos hi, simColorsW_of_mem p ep.2 c hi]
      simp only [mergeAt, hi, if_true]
    · rw [if_neg hi, msgAt_multiCom]
      simp only [mergeAt, hi, if_false]
  have hopen : colOpen (fun i => ep.2 (c i)) w.1.2 p =
      colOpen (simColorsW p ep.2 c) (mergeAt p w.1.2 r') p := by
    unfold colOpen
    rw [mergeAt_fst, mergeAt_snd, simColorsW_of_mem p ep.2 c (Or.inl rfl),
      simColorsW_of_mem p ep.2 c (Or.inr rfl)]
  show (if edgeIdxOfMsg (edgeCount G) (V (Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i)) w.2) =
        (ep.1 : ℕ) then
      some (w.2, Strategy.encodeMsgs (List.ofFn fun i =>
        if i = p.1 ∨ i = p.2 then
          Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
        else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i),
        colOpen (fun i => ep.2 (c i)) w.1.2 p)
    else none) =
    (if edgeIdxOfMsg (edgeCount G)
        (V (colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r')) w.2) = (ep.1 : ℕ) then
      some (w.2, colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r'),
        colOpen (simColorsW p ep.2 c) (mergeAt p w.1.2 r') p)
    else none)
  rw [hcom, hopen]

/-- **The planted attempt on the `S''` commitment vector is an `S''` attempt** with the merged
randomness and the planted `(e₀, π₀)`.

**Proof sketch.** As `colSimAttemptPlanted_W`: every position of the challenge commits to
`π₀ (c i)` (`msgAt_multiCom`), so the planted message is `colCommit (π₀ ∘ c)` with the merged
randomness, and the openings agree by `mergeAt_fst`, `mergeAt_snd`. -/
private theorem colSimAttemptPlanted_H (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (ep : Fin (edgeCount G) × Equiv.Perm (Fin 3)) (r' : Fin n → Fin ℓn → Bool)
    (w : AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :
    colSimAttemptPlanted Com ℓn G c V ep.1 ep.2
        (multiCom Com (fun i => padColor n (ep.2 (c i))) r') w =
      colSimAttemptH Com ℓn G c V ((ep, mergeAt (edgeOf G ep.1) w.1.2 r'), w.2) := by
  set p := edgeOf G ep.1 with hp
  have hcom : Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i) =
      colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') := by
    show _ = Strategy.encodeMsgs (List.ofFn fun i =>
      Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (mergeAt p w.1.2 r' i))))
    congr 2
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · rw [if_pos hi]
      simp only [mergeAt, hi, if_true]
    · rw [if_neg hi, msgAt_multiCom]
      simp only [mergeAt, hi, if_false]
  have hopen : colOpen (fun i => ep.2 (c i)) w.1.2 p =
      colOpen (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') p := by
    unfold colOpen
    rw [mergeAt_fst, mergeAt_snd]
  show (if edgeIdxOfMsg (edgeCount G) (V (Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i)) w.2) =
        (ep.1 : ℕ) then
      some (w.2, Strategy.encodeMsgs (List.ofFn fun i =>
        if i = p.1 ∨ i = p.2 then
          Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
        else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i),
        colOpen (fun i => ep.2 (c i)) w.1.2 p)
    else none) =
    (if edgeIdxOfMsg (edgeCount G)
        (V (colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r')) w.2) = (ep.1 : ℕ) then
      some (w.2, colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r'),
        colOpen (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') p)
    else none)
  rw [hcom, hopen]

/-- **`S' ≈ S''` by hybrids and multi-value hiding** [PS10, proof of Proposition 128.8,
"by the hybrid lemma … `D` distinguishes `S_k` and `S_{k+1}`"] (Claim-129.d, concrete): for
every distinguisher `D` of optional views there are a hybrid index `k < N`, an edge `e₀` and a
permutation `π₀` such that the advantage of `D` between the truncated `S'` and `S''`, divided
by `N`, is at most the advantage of the explicit reduction `colSimRed … k e₀ π₀ D` between the
commitment vectors (`multiCom`) to the `S'` colours `simColorsW (edgeOf G e₀) π₀ c` and to the
`S''` colours `π₀ ∘ c`.

**Deviation:** `N` hybrid steps (the text's `2n|E|`), the `6|E|` sub-hybrid replaced by the
non-uniform choice of `(e₀, π₀)`.

**Proof sketch.** `exists_hybrid_gap` on `k ↦ acceptProb (colSimHyb … N k) D`
(`colSimHyb_zero`, `colSimHyb_self` are the ends) gives `k` with gap `≥ distAdv / N`. The gap at
`k` is the average over attempt `k`'s `(e', π)` (`uprob_prod` on the `k`-th block,
`acceptProb_update`) of the difference between the planted attempt fed the `S'` vector and
fed the `S''` vector: on `cv = multiCom (pad ∘ simColorsW p π) r'` the planted attempt's
message is `colCommit (simColorsW p π) r''` for the randomness `r''` equal to `r'` off the
endpoints and to `w`'s randomness at the endpoints (`msgAt_encodeMsgs`, `List.getElem_ofFn`),
whose law is uniform (`OneWay.uprob_update` twice), so the acceptance probability is that of
hybrid `k`; likewise the `S''` vector gives hybrid `k + 1`. An average of absolute values
bounds the absolute value of the average, so some `(e₀, π₀)` attains at least the gap
(`Finset.exists_le_of_sum_le` / `uexp` averaging as in `Protocol.exists_proverCoins_le`). -/
theorem exists_colSimRed_ge [Fintype ρ] {ρ' : Type*} [Fintype ρ'] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) (hN : 0 < N)
    (D : Option (ColView ρ) → ρ' → Bool) :
    ∃ (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3)),
      distAdv (colSimTruncW Com ℓn G c V N) (colSimTruncH Com ℓn G c V N) D / N ≤
        distAdv
          (fun r : Fin n → Fin ℓn → Bool =>
            multiCom Com (fun i => padColor n (simColorsW (edgeOf G e₀) π₀ c i)) r)
          (fun r : Fin n → Fin ℓn → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
          (colSimRed Com ℓn G c V N k e₀ π₀ D) := by
  obtain ⟨k, ep, h⟩ := exists_hybRed_ge hm hN (colSimAttemptH Com ℓn G c V)
    (colSimAttemptW Com ℓn G c V) D (edgeOf G)
    (fun ep cv => colSimAttemptPlanted Com ℓn G c V ep.1 ep.2 cv)
    (fun ep r => multiCom Com (fun i => padColor n (simColorsW (edgeOf G ep.1) ep.2 c i)) r)
    (fun ep r => multiCom Com (fun i => padColor n (ep.2 (c i))) r)
    (fun ep r' w => colSimAttemptPlanted_W Com ℓn G c V ep r' w)
    (fun ep r' w => colSimAttemptPlanted_H Com ℓn G c V ep r' w)
  refine ⟨k, ep.1, ep.2, ?_⟩
  have h0 : acceptProb (colSimTruncW Com ℓn G c V N) D =
      acceptProb (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N 0) D := by
    unfold acceptProb
    exact congrArg uprob (funext fun z => by rw [← colSimHyb_zero Com ℓn G c V N z.1]; rfl)
  have hN' : acceptProb (colSimTruncH Com ℓn G c V N) D =
      acceptProb (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N N) D := by
    unfold acceptProb
    exact congrArg uprob (funext fun z => by rw [← colSimHyb_self Com ℓn G c V N z.1]; rfl)
  calc distAdv (colSimTruncW Com ℓn G c V N) (colSimTruncH Com ℓn G c V N) D / N
      = distAdv (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N 0)
          (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N N) D / N := by
        rw [distAdv, distAdv, h0, hN']
    _ ≤ _ := h

end Typed

/-! ### The string simulator [PS10, Algorithm 128.7] (Alg-128.7, Claim-128.a) -/

/-- The coin block of one attempt of the string simulator against `V'` at instance length
`N`: `(N+1)²` bits for the edge sampler, `3N` bits for the colour-pair sampler, `N ℓ(N)` bits
of commitment randomness and the tape of `V'`. -/
def colSimBlock (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .add (.add (.add (.normal 1 2) (.mul (.const 3) .var)) (.mul .var ℓ)) V'.coins

/-- The coin polynomial of the string simulator: `N²` blocks (at most `n|E| ≤ N²` attempts
are made). -/
def colSimCoins (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .mul (.mul .var .var) (colSimBlock ℓ V')

/-- The six distinct colour pairs enumerated by `Fin 6`. -/
noncomputable def pair6Equiv : Fin 6 ≃ ColorPair := (Fintype.equivFinOfCardEq card_colorPair).symm

/-- The simulator's distinct colour pair from `3T` tape bits: `T` rejection trials of three
bits, the pair `(0, 1)` on failure (D10). -/
noncomputable def sampleColorPair (T : ℕ) (r : List Bool) : ColorPair :=
  ((sampleIdx 6 3 T r).map pair6Equiv).getD ⟨(0, 1), by decide⟩

/-- One attempt of the string simulator [PS10, Algorithm 128.7, steps 1–4] on `(x, z)` with
the coin block `blk`: sample `e'` and the colour pair, commit to `simColors (edgeAt G e') (a, b)`
with the randomness read from the block, run `V'` on `[com]` with the rest of the block as its
tape, and output the encoded view `⟨⟨x, z⟩, ⟨r_{V'}, [com, opening]⟩⟩` if `V'` names `e'`;
if `E = ∅`, commit to all-zero colours and output the view with the empty opening. -/
noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  let n := (decGraph x).1
  let G : Graph n := (decGraph x).2
  let m := edgeCount G
  let N := x.length
  let e' := sampleEdgeIdx m N blk
  let ab := sampleColorPair N (blk.drop ((N + 1) ^ 2))
  let rr : Fin n → Fin (ℓ.eval n) → Bool :=
    fun i j => blk.getD ((N + 1) ^ 2 + 3 * N + i * ℓ.eval n + j) false
  let rV := blk.drop ((N + 1) ^ 2 + 3 * N + N * ℓ.eval N)
  match edgeAt G e' with
  | none => some (View.encode ⟨x, z, rV, [colCommit Com n (ℓ.eval n) (fun _ => 0) rr, []]⟩)
  | some p =>
    let c' := simColors p ab
    let com := colCommit Com n (ℓ.eval n) c' rr
    if edgeIdxOfMsg m (V'.next x z rV [com]) = e' then
      some (View.encode ⟨x, z, rV, [com, colOpen c' rr p]⟩)
    else none

/-- The string simulator [PS10, Algorithm 128.7] (Alg-128.7): up to `n|E|` attempts
(`colIterations x`, with `|E| = edgeCount G` counting ordered edge pairs; run-3 audit P11-3) on
the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
after `n|E|` failures; a single attempt if `E = ∅`.

As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|` attempts, then `fail` (`⊥ = []`).
**Deviation (D10):** `e'` and the colour pair are rejection-sampled from the tape (defaults `0`
and `(0, 1)`). -/
noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z r : List Bool) : List Bool :=
  let B := (colSimBlock ℓ V').eval x.length
  let att : ℕ → Option (List Bool) := fun t => colSimAttemptStr Com ℓ V' x z (colCoinSlice B t r)
  if edgeCount (decGraph x).2 = 0 then (att 0).getD []
  else ((List.range (colIterations x)).findSome? att).getD []

/-- **The simulator is a uniform PPT** [PS10, p. 128, "by construction it directly follows that
`S` is a p.p.t."] (Claim-128.a): for a polynomial-time `Com` and an efficient `V'` there is a
uniform `NUPPT` with coin polynomial `colSimCoins ℓ V'` whose activation on `⟨x, z⟩` at
parameter `|x|` is `colSim Com ℓ V' x z r`.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with
`V'.next x z rV [com] = A.runAtL |x| ⟨⟨x, z⟩, encodeMsgs [com]⟩ rV` (`Strategy.ofNUPPT_next`),
polynomial-time by `A.polyTimeComputable_output` and the pairing calculus. One attempt on the
raw layout is polynomial-time: the block is cut by `polyTimeComputable_pairTakePoly`/
`pairDropPoly` with the unary block length (`polyTimeComputable_unaryPoly`); the two samplers
by `polyTimeComputable_iterateFind` over the trials; the `n` commitments by
`polyTimeComputable_blockMap ℓ` composed with `hCom` and `polyTimeComputable_iterateEmit`
for the `encodeMsgs` fold (the colour at position `i` by `polyTimeComputable_ite` on the
comparison with the two endpoints); the comparison of `V'`'s reply with `e'` by
`polyTimeComputable_lenLe`-based modular arithmetic in unary; the view by
`PolyTimeComputable.pairEncode`. The loop over `t < n|E|` is
`Complexity.polyTimeComputable_iterateFind` with the attempt index in the state and the
accepting test "the attempt succeeded" (`R := mul var var`, `P :=` the layout length), the
`E = ∅` case by `polyTimeComputable_ite`; the result is packaged by `NUPPT.ofPolyTimeUniform`
with coins `colSimCoins ℓ V'` (`NUPPT.runAtL_ofPolyTimeUniform`,
`NUPPT.ofPolyTimeUniform_uniform`). -/
theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = colSimCoins ℓ V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = colSim Com ℓ V' x z (List.ofFn r) := by
  obtain ⟨S, hS, hc, hsim⟩ := ColSimMachine.exists_simulator hCom ℓ hV'
  exact ⟨S, hS, hc, fun x z r => (hsim x z r).trans rfl⟩

/-! ### Proposition 128.8 -/

/-- A negligible function of `√N` is negligible in `N` (the bookkeeping converting the
commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
Inf-4.4).

**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
`n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
`N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
`|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
    Negligible fun N => μ (Nat.sqrt N) := by
  intro c
  obtain ⟨n₀, hn₀⟩ := hμ (2 * c + 1)
  set K := max (max n₀ (4 ^ c)) 1 with hK
  refine ⟨K * K, fun N hN => ?_⟩
  set n := Nat.sqrt N with hn
  have hKn : K ≤ n := Nat.le_sqrt.2 hN
  have hn₀n : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKn
  have h4n : 4 ^ c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKn
  have h1n : 1 ≤ n := le_trans (le_max_right _ _) hKn
  have hNlt : N < (n + 1) * (n + 1) := Nat.lt_succ_sqrt N
  have hN2 : N ≤ 4 * (n * n) := by nlinarith
  have hNr : (N : ℝ) ≤ 4 * ((n : ℝ) * n) := by exact_mod_cast hN2
  have hμn : |μ n| < 1 / (n : ℝ) ^ (2 * c + 1) := hn₀ n hn₀n
  show |μ n| < 1 / (N : ℝ) ^ c
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1n
  have h4r : (4 : ℝ) ^ c ≤ n := by exact_mod_cast h4n
  have hNc : (N : ℝ) ^ c ≤ (n : ℝ) ^ (2 * c + 1) := by
    calc (N : ℝ) ^ c ≤ (4 * ((n : ℝ) * n)) ^ c := pow_le_pow_left₀ (Nat.cast_nonneg N) hNr c
      _ = 4 ^ c * (n : ℝ) ^ (2 * c) := by rw [_root_.mul_pow, pow_mul, sq]
      _ ≤ n * (n : ℝ) ^ (2 * c) := by gcongr
      _ = (n : ℝ) ^ (2 * c + 1) := by ring
  have hN1 : 1 ≤ N := by
    have hK1 : 1 ≤ K := le_max_right _ _
    have := Nat.mul_le_mul hK1 hK1
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  exact hμn.trans_le (one_div_le_one_div_of_le hNpos hNc)

/-- **One iteration of [PS10, Protocol 127.5] is zero-knowledge for `R_3COL`** [PS10,
Proposition 128.8 and Proposition 127.6, zero-knowledge half] (Prop-128.8, Prop-127.6 (b)):
for a commitment scheme `(Com, ℓ)`, for every efficient verifier `V'` there is a uniform PPT
simulator `S` such that for every auxiliary-input bound `Lz` and every non-uniform PPT `D`
there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| ≤ Lz(|x|)`, the
advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8, D10):** strict PPT simulator (D8's definition of `ZK`), rejection-sampled
`π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
composition, [PS10, §7.2.1], out of scope).

**Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
on the encoded optional view (`⊥ ↦ []`).

(1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
`decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
`some ∘ colRealView`.

If `m > 0`:
(2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
`(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
`statClose_sampleColorPair` — the colour-pair analogue of `statClose_samplePerm3`, still to be
added: the fill ladder's first step, gate 03g review M3 — and `StatClose.prod` over the blocks).
(3) `uprob_colSimTruncW_eq`.
(4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
`distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
`CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
`cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
(5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
`distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.

If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
`0`). For each fixed `π`, `D`'s advantage is the hiding gap of
`cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`, with `r_V` fixed by `exists_fixCoins`. Average over `π`.
If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
from the real tape when `V'.coinLen 0 > 0`.

The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
because `|z| ≤ Lz(n²)`: this is where the bound `Lz` is used, see the `Defs.lean` module
docstring), take those whose fixed reduction (either case) has the largest gap on its own
vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and openings,
`pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially bounded by
`hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform machine once
(`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins (`NUPPT.exists_reparam_advice`,
`φ n = n²`). Its acceptance probabilities on `multiCom` samples are the fixed reduction's (coin
transport along `finCongr`). `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a
`distAdv` at every `n`), so the hiding terms are at most
`K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.

Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
(`C = 1`), `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is
`1`. Use the triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
(`length_encGraph`, `Nat.sqrt_eq`). -/
theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
    ZK (colProtocol Com ℓ) R3COL := by
  sorry

/-- One iteration of [PS10, Protocol 127.5] is honest-verifier zero-knowledge for `R_3COL`
[PS10, Proposition 128.8 with the honest verifier] (`ZK.hvzk`, `colVerifier_efficient`). -/
theorem col_hvzk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
    HVZK (colProtocol Com ℓ) R3COL :=
  (col_zk hC).hvzk (colVerifier_efficient hC.easy ℓ)

/-- **[PS10, Proposition 127.6]: Protocol 127.5 is a zero-knowledge proof for `3COL`**
(Prop-127.6), assembled from its parts: one iteration is an interactive proof with efficient
prover and soundness error `1 - 1/|x| + (1/2)^{|x|}` (`col_efficientProverProofErr`) and is
zero-knowledge (`col_zk`), and the `n|E|`-fold repetition is an interactive proof with
efficient prover and negligible soundness error (`colRep_efficientProverProof`).

**Deviation (DQ5):** the zero-knowledge of the repeated protocol is sequential composition
[PS10, §7.2.1], outside Chapters 2–4, and is not claimed. -/
theorem col_zeroKnowledgeProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
        (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) ∧
      ZK (colProtocol Com ℓ) R3COL ∧
      EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL :=
  ⟨col_efficientProverProofErr hC, col_zk hC, colRep_efficientProverProof hC⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.Asymptotic.Adversary
import Mathlib.Combinatorics.SimpleGraph.Coloring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Graph 3-colouring: the language, its witnesses, edges, colours and samplers

The combinatorial and sampling preliminaries of the zero-knowledge protocol for graph
3-colouring [PS10, §4.7]: the language of 3-colourable graphs and its witness relation
[PS10, Theorem 124.1, step 1] (Def-124.f), the enumeration of the edges of a graph (the set
`E` of [PS10, Protocol 127.5]), the bound `(1 - 1/m)^{nm} ≤ e^{-n}` of the soundness analysis
(Claim-125.a), colours as `n`-bit committed values (DQ4), and the rejection samplers of the
honest parties for the colour permutation `π ← S₃` and the edge `e ← E` (D10).

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours
(`ThreeColorable` agrees with Mathlib's `SimpleGraph.Colorable 3` on simple graphs,
`threeColorable_ofSimpleGraph_iff`). The edges are listed in lexicographic order
(`edgeList`), the verifier's challenge is an index into that list, sent in unary
(`edgeMsg`) and decoded totally (`edgeIdxOfMsg`).

**Deviation (run-3 audit P11-3):** `Graph n` is an arbitrary Boolean relation and `edgeList`
lists the *ordered* pairs `(u, v)` with `G u v` (loops included), so for the text's symmetric
loopless `G = (V, E)` the formal `|E| := edgeCount G` is `2|E|`: one iteration has soundness
error `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|` times; the challenge is
uniform over the ordered pairs, i.e. uniform over the undirected edges, and the bound
`(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. Throughout `ThreeColoring/`, `|E|` means `edgeCount G`.

**Deviation (DQ4, D10):** colours are padded to `n` bits (`padColor`; the text commits to
2-bit colours, i.e. at security parameter `2`); `π` and `e` are sampled by rejection from the
bit tapes (`samplePerm3`, `sampleEdgeIdx`) within statistical error `(1/4)^T`, `(1/2)^T`.

## Main definitions

* `TCSlib.Cryptography.ProperColoring`, `TCSlib.Cryptography.ThreeColorable`,
  `TCSlib.Cryptography.L3COL`, `TCSlib.Cryptography.R3COL` — 3-colourings, the language of
  3-colourable graphs and its witness relation (Def-124.f).
* `TCSlib.Cryptography.edgeList`, `TCSlib.Cryptography.edgeCount`,
  `TCSlib.Cryptography.edgeOf`, `TCSlib.Cryptography.edgeAt` — the edges and their indices.
* `TCSlib.Cryptography.encColor`, `TCSlib.Cryptography.decColor`,
  `TCSlib.Cryptography.padColor` — colours as 2-bit strings and as `n`-bit values.
* `TCSlib.Cryptography.sampleIdx`, `TCSlib.Cryptography.samplePerm3`,
  `TCSlib.Cryptography.sampleEdgeIdx`, `TCSlib.Cryptography.edgeMsg`,
  `TCSlib.Cryptography.edgeIdxOfMsg` — the samplers and the challenge encoding.

## Main results

* `TCSlib.Cryptography.mem_L3COL_iff`, `TCSlib.Cryptography.encGraph_mem_L3COL_iff`,
  `TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff` — the language and its witnesses.
* `TCSlib.Cryptography.mem_edgeList_iff`, `TCSlib.Cryptography.edgeAt_adj`,
  `TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero`,
  `TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable` — edges (all proved).
* `TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp`, `TCSlib.Cryptography.exp_neg_le_inv_two_pow`
  — `(1 - 1/m)^{nm} ≤ e^{-n} ≤ 2^{-n}` (Claim-125.a, proved).
* `TCSlib.Cryptography.padColor_injective` — padding to `n ≥ 2` bits is injective (proved).
* `TCSlib.Cryptography.statClose_samplePerm3`, `TCSlib.Cryptography.statClose_sampleEdgeIdx`
  — the samplers are statistically close to uniform (D10, proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### 3-colourings and the language `3COL` (Def-124.f) -/

/-- A proper 3-colouring of the graph `G` [PS10, §4.7, Theorem 124.1, step 1]: the endpoints
of every edge receive different colours (`c : Fin n → Fin 3`, colours `{1, 2, 3}` as `Fin 3`). -/
def ProperColoring {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : Prop :=
  ∀ u v, G u v = true → c u ≠ c v

instance {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : Decidable (ProperColoring G c) := by
  unfold ProperColoring
  infer_instance

/-- A graph is 3-colourable when it has a proper 3-colouring [PS10, §4.7] (Def-124.f, typed). -/
def ThreeColorable {n : ℕ} (G : Graph n) : Prop := ∃ c, ProperColoring G c

/-- The graph of a Mathlib simple graph on `Fin n` as a Boolean relation. -/
def Graph.ofSimpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : Graph n :=
  fun u v => decide (H.Adj u v)

/-- Sanity: for a simple graph the notion agrees with Mathlib's `SimpleGraph.Colorable 3`
(a `Coloring` into `Fin 3` is exactly a proper 3-colouring). -/
theorem threeColorable_ofSimpleGraph_iff {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    ThreeColorable (Graph.ofSimpleGraph H) ↔ H.Colorable 3 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {u v} h => hc u v (decide_eq_true h)⟩
  · rintro ⟨C⟩
    exact ⟨C, fun u v h => C.valid (of_decide_eq_true h)⟩

/-- The language of 3-colourable graphs [PS10, §4.7, "Graph 3-Coloring"] (Def-124.f): the
adjacency-matrix encodings of the 3-colourable graphs. -/
def L3COL : Language Bool := {x | ∃ (n : ℕ) (G : Graph n), x = encGraph G ∧ ThreeColorable G}

/-- The witness relation of `3COL` [PS10, §4.7] (Def-124.f): `y` is the encoding of a proper
3-colouring of the graph encoded by `x`. -/
def R3COL (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G : Graph n) (c : Fin n → Fin 3),
    x = encGraph G ∧ y = encColoring c ∧ ProperColoring G c

/-- `x ∈ 3COL` iff `x` has a witness for `R_3COL`. -/
theorem mem_L3COL_iff (x : List Bool) : x ∈ L3COL ↔ ∃ y, R3COL x y := by
  constructor
  · rintro ⟨n, G, rfl, c, hc⟩
    exact ⟨encColoring c, n, G, c, rfl, rfl, hc⟩
  · rintro ⟨y, n, G, c, rfl, -, hc⟩
    exact ⟨n, G, rfl, c, hc⟩

/-- An encoded graph is in `3COL` iff the graph is 3-colourable (`decGraph_encGraph`
identifies the graph from its encoding). -/
theorem encGraph_mem_L3COL_iff {n : ℕ} (G : Graph n) : encGraph G ∈ L3COL ↔ ThreeColorable G := by
  constructor
  · rintro ⟨n', G', h, hG'⟩
    have hd := decGraph_encGraph G
    rw [h, decGraph_encGraph] at hd
    cases hd
    exact hG'
  · intro h
    exact ⟨n, G, rfl, h⟩

/-! ### Edges -/

/-- The list of edges of `G`: the **ordered** pairs `(u, v)` with `G u v = true` (loops
included), in lexicographic order — the set `E` of [PS10, Protocol 127.5] in the formal model;
in the docstrings of `ThreeColoring/` the notation `|E|` means `edgeCount G = (edgeList G).length`.

**Deviation (run-3 audit P11-3):** `Graph n` is an arbitrary Boolean relation, so `E` is the
list of ordered pairs `(u, v)` with `G u v`; for a symmetric loopless graph (the text's
`G = (V, E)`) `edgeCount G = 2|E|`, one iteration of the protocol has soundness error
`1 − 1/(2|E|)` and the repeated protocol runs `n · edgeCount G = 2n|E|` iterations. The
verifier's challenge is uniform over the ordered pairs, i.e. uniform over the text's
undirected edges, and the bound `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged; a loop `(u, u)` is an
edge and makes the graph non-colourable, as it should. -/
def edgeList {n : ℕ} (G : Graph n) : List (Fin n × Fin n) :=
  (List.finRange n ×ˢ List.finRange n).filter fun p => G p.1 p.2

/-- The number `m` of (ordered) edge pairs of `G`, written `|E|` in the docstrings of
`ThreeColoring/` — for a symmetric loopless graph twice the `|E| = m` of
[PS10, Protocol 127.5] (see `edgeList`; run-3 audit P11-3). -/
abbrev edgeCount {n : ℕ} (G : Graph n) : ℕ := (edgeList G).length

/-- A pair is in the edge list iff it is an edge. -/
theorem mem_edgeList_iff {n : ℕ} (G : Graph n) (p : Fin n × Fin n) :
    p ∈ edgeList G ↔ G p.1 p.2 = true := by
  rcases p with ⟨u, v⟩
  simp [edgeList, List.mem_filter, List.mem_finRange]

/-- The edge of index `e : Fin |E|`. -/
def edgeOf {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) : Fin n × Fin n := (edgeList G).get e

/-- The endpoints of `edgeOf G e` are adjacent. -/
theorem edgeOf_adj {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) :
    G (edgeOf G e).1 (edgeOf G e).2 = true :=
  (mem_edgeList_iff G _).1 (List.get_mem _ _)

/-- Every edge is `edgeOf G e` for some index `e`. -/
theorem exists_edgeOf_eq {n : ℕ} (G : Graph n) {u v : Fin n} (h : G u v = true) :
    ∃ e : Fin (edgeCount G), edgeOf G e = (u, v) := by
  obtain ⟨e, he⟩ := List.mem_iff_get.1 ((mem_edgeList_iff G (u, v)).2 h)
  exact ⟨e, he⟩

/-- The edge of the (arbitrary) index `e : ℕ`, reduced modulo `|E|`; `none` iff `E = ∅`
(the total decoding of the verifier's challenge). -/
def edgeAt {n : ℕ} (G : Graph n) (e : ℕ) : Option (Fin n × Fin n) := (edgeList G)[e % edgeCount G]?

/-- On an in-range index `edgeAt` is `edgeOf`. -/
theorem edgeAt_eq_some_edgeOf {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) :
    edgeAt G e = some (edgeOf G e) := by
  unfold edgeAt edgeOf
  rw [Nat.mod_eq_of_lt e.isLt, List.getElem?_eq_getElem e.isLt, List.get_eq_getElem]

/-- The endpoints of `edgeAt G e` are adjacent. -/
theorem edgeAt_adj {n : ℕ} (G : Graph n) {e : ℕ} {p : Fin n × Fin n} (h : edgeAt G e = some p) :
    G p.1 p.2 = true :=
  (mem_edgeList_iff G p).1 (List.mem_of_getElem? h)

/-- With at least one edge every index decodes to an edge. -/
theorem edgeAt_isSome {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :
    ∃ p, edgeAt G e = some p :=
  ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hm)⟩

/-- `edgeAt` is `none` exactly when there are no edges. -/
theorem edgeAt_eq_none_iff {n : ℕ} (G : Graph n) (e : ℕ) : edgeAt G e = none ↔ edgeCount G = 0 := by
  constructor
  · intro h
    by_contra hm
    obtain ⟨p, hp⟩ := edgeAt_isSome G (Nat.pos_of_ne_zero hm) e
    rw [h] at hp
    exact Option.noConfusion hp
  · intro h
    unfold edgeAt
    rw [List.getElem?_eq_none_iff]
    change (edgeList G).length = 0 at h
    rw [h]
    exact Nat.zero_le _

/-- An edgeless graph is 3-colourable (constant colouring). -/
theorem threeColorable_of_edgeCount_eq_zero {n : ℕ} {G : Graph n} (h : edgeCount G = 0) :
    ThreeColorable G := by
  refine ⟨fun _ => 0, fun u v huv => ?_⟩
  have hmem := (mem_edgeList_iff G (u, v)).2 huv
  rw [List.length_eq_zero_iff.1 h] at hmem
  exact absurd hmem (List.not_mem_nil)

/-- A graph that is not 3-colourable has an edge. -/
theorem edgeCount_pos_of_not_threeColorable {n : ℕ} {G : Graph n} (h : ¬ ThreeColorable G) :
    0 < edgeCount G :=
  Nat.pos_of_ne_zero fun h0 => h (threeColorable_of_edgeCount_eq_zero h0)

/-! ### Claim-125.a -/

/-- `(1 - 1/m)^{n m} ≤ e^{-n}` for `m ≥ 1` [PS10, proof of Proposition 127.6,
"`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Claim-125.a): `Real.one_sub_div_pow_le_exp_neg` with `N := n m`
and `t := n`, after rewriting `n / (n m) = 1 / m`. -/
theorem one_sub_inv_pow_mul_le_exp (m n : ℕ) (hm : 0 < m) :
    (1 - 1 / (m : ℝ)) ^ (n * m) ≤ Real.exp (-(n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.one_sub_div_pow_le_exp_neg (n := n * m) (t := (n : ℝ))
    (by exact_mod_cast Nat.le_mul_of_pos_right n hm)
  have hnm : (n : ℝ) / ((n * m : ℕ) : ℝ) = 1 / m := by
    rw [Nat.cast_mul]
    field_simp
  rwa [hnm] at h

/-- `e^{-n} ≤ 2^{-n}` (the text's "`≈ e^{-n}`" bounded by the dyadic negligible function):
`2 ≤ e` by `Real.add_one_le_exp`. -/
theorem exp_neg_le_inv_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  rw [Real.exp_neg, show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul, ← inv_pow]
  exact pow_le_pow_left₀ (by positivity)
    (inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])) n

/-! ### Colours as `n`-bit values (DQ4) -/

/-- The two-bit encoding of a colour (`encColoring` of a one-vertex colouring). -/
def encColor (a : Fin 3) : List Bool := encColoring fun _ : Fin 1 => a

/-- The total decoding of a colour from a string (`decColoring` at one vertex). -/
def decColor (w : List Bool) : Fin 3 := decColoring 1 w 0

/-- Decoding an encoded colour gives the colour back. -/
@[simp] theorem decColor_encColor (a : Fin 3) : decColor (encColor a) = a :=
  congrFun (decColoring_encColoring fun _ : Fin 1 => a) 0

/-- A colour padded to an `n`-bit value (DQ4): the two bits of `encColor a` followed by
zeros. The value committed to by the prover of [PS10, Protocol 127.5] at security parameter
`n`. -/
def padColor (n : ℕ) (a : Fin 3) : Fin n → Bool := padFin n (encColor a)

/-- The two-bit encodings of distinct colours differ in one of the two bits. -/
theorem encColor_getD_ne {a b : Fin 3} (hab : a ≠ b) :
    (encColor a).getD 0 false ≠ (encColor b).getD 0 false ∨
      (encColor a).getD 1 false ≠ (encColor b).getD 1 false := by
  revert a b
  decide

/-- Padding to `n ≥ 2` bits is injective on colours. -/
theorem padColor_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (padColor n) := by
  intro a b h
  by_contra hab
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [padColor, padFin] at h0 h1
  rcases encColor_getD_ne hab with hne | hne
  · exact hne h0
  · exact hne h1

/-! ### Samplers of the honest parties (D10) -/

/-- `T` rejection trials of `k` bits read consecutively from a tape (bit `j` of trial `t` at
position `t k + j`), the first accepted value in `Fin m` (`rejectionSample`, D10). -/
def sampleIdx (m k T : ℕ) (r : List Bool) : Option (Fin m) :=
  rejectionSample m k T fun t j => r.getD (t * k + j) false

/-- The six permutations of the three colours enumerated by `Fin 6`. -/
noncomputable def perm3Equiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_perm, Fintype.card_fin]; rfl)).symm

/-- The honest prover's colour permutation `π ← S₃` of [PS10, Protocol 127.5] from the first
`3T` bits of its tape: `T` rejection trials of three bits (success probability `6/8` each),
the identity on failure (D10). -/
noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
  ((sampleIdx 6 3 T r).map perm3Equiv).getD 1

/-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
rejection trials of `k = Nat.size m` bits (for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds
with probability `≥ 1/2`; for `m = 0` the sampler returns the default), the index `0` on
failure (D10). -/
def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
  ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0

/-- With at least one edge the sampled index is in range. -/
theorem sampleEdgeIdx_lt {m : ℕ} (hm : 0 < m) (T : ℕ) (r : List Bool) : sampleEdgeIdx m T r < m := by
  unfold sampleEdgeIdx
  cases sampleIdx m (Nat.size m) T r with
  | none => simpa using hm
  | some e => simp [e.isLt]

/-- The unary encoding of the verifier's challenge: the edge index `e` as `1^e`. -/
def edgeMsg (e : ℕ) : List Bool := List.replicate e true

/-- The total decoding of a challenge string as an edge index in `[m]`: its length modulo `m`
(every string names an edge when `E ≠ ∅`). -/
def edgeIdxOfMsg (m : ℕ) (w : List Bool) : ℕ := w.length % m

/-- The challenge `1^e` decodes to `e` when `e < m`. -/
@[simp] theorem edgeIdxOfMsg_edgeMsg {m e : ℕ} (he : e < m) : edgeIdxOfMsg m (edgeMsg e) = e := by
  simp [edgeIdxOfMsg, edgeMsg, Nat.mod_eq_of_lt he]

/-- The decoded index is in range when `m > 0`. -/
theorem edgeIdxOfMsg_lt {m : ℕ} (hm : 0 < m) (w : List Bool) : edgeIdxOfMsg m w < m :=
  Nat.mod_lt _ hm

/-- A tape of `T k` bits read as `T` trials of `k` bits: bit `j` of trial `t` is tape bit
`finProdFinEquiv (t, j) = t k + j` (the curried `finProdFinEquiv`). -/
private def tapeEquiv (T k : ℕ) : (Fin (T * k) → Bool) ≃ (Fin T → Fin k → Bool) where
  toFun r t j := r (finProdFinEquiv (t, j))
  invFun b i := b (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv r := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv b := by
    funext t j
    simp

/-- Bit `t k + j` of the tape `List.ofFn r` is entry `(t, j)` of its trial table. -/
private theorem ofFn_getD_tape {T k : ℕ} (r : Fin (T * k) → Bool) (t : Fin T) (j : Fin k) :
    (List.ofFn r).getD (t * k + j) false = tapeEquiv T k r t j := by
  have hm : ((finProdFinEquiv (t, j) : Fin (T * k)) : ℕ) = t * k + j := by
    simp only [finProdFinEquiv_apply_val]
    ring
  show _ = r (finProdFinEquiv (t, j))
  rw [← hm, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _),
    Option.getD_some, Fin.eta]

/-- On a tape of exactly `T k` bits, `sampleIdx` is `rejectionSample` on the trial table. -/
private theorem sampleIdx_ofFn (m k T : ℕ) (r : Fin (T * k) → Bool) :
    sampleIdx m k T (List.ofFn r) = rejectionSample m k T (tapeEquiv T k r) := by
  unfold sampleIdx
  congr 1
  funext t j
  exact ofFn_getD_tape r t j

/-- The permutation sampler is within `(1/4)^T` of a uniform permutation of the colours (D10).

**Proof sketch.** `statClose_rejectionSample 6 3 T` (with `6 ≤ 2³`) gives closeness
`(1 - 6/8)^T = (1/4)^T` of `(rejectionSample 6 3 T b).getD d` to the identity on `Fin 6`; the
tape-to-trials map `r ↦ (t, j) ↦ r.getD (3t + j)` on `Fin (T * 3) → Bool` is the bijection
`finProdFinEquiv` curried (`StatClose.comp_equiv_left`), and `perm3Equiv` is a bijection
with `perm3Equiv d = 1` for the right default `d` (`StatClose.map`, `StatClose.comp_equiv_right`). -/
theorem statClose_samplePerm3 (T : ℕ) :
    StatClose (fun r : Fin (T * 3) → Bool => samplePerm3 T (List.ofFn r))
      (id : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) ((1 / 4 : ℝ) ^ T) := by
  have h := (((statClose_rejectionSample 6 3 T (by norm_num) (by norm_num)
    (perm3Equiv.symm 1)).map perm3Equiv).comp_equiv_right perm3Equiv.symm).comp_equiv_left
    (tapeEquiv T 3)
  have hδ : (1 - ((6 : ℕ) : ℝ) / 2 ^ 3) ^ T = (1 / 4) ^ T := by norm_num
  rw [hδ] at h
  convert h using 2 with r σ
  · simp only [samplePerm3, sampleIdx_ofFn]
    cases rejectionSample 6 3 T (tapeEquiv T 3 r) with
    | none => simp
    | some i => simp
  · simp

/-- The edge sampler is within `(1/2)^T` of a uniform edge index (D10).

**Proof sketch.** `statClose_rejectionSample m (Nat.size m) T` with `m ≤ 2^{size m}`
(`Nat.lt_size_self`) gives closeness `(1 - m/2^{size m})^T`; since `2^{size m} ≤ 2m` for
`m ≥ 1` (`Nat.size_le`, `Nat.lt_size`), `1 - m/2^{size m} ≤ 1/2` and `pow_le_pow_left₀`;
the tape-to-trials map is the curried `finProdFinEquiv` (`StatClose.comp_equiv_left`), and
`sampleEdgeIdx` is `Fin.val` of the sampler's `getD ⟨0, hm⟩`. -/
theorem statClose_sampleEdgeIdx {m : ℕ} (hm : 0 < m) (T : ℕ) :
    StatClose (fun r : Fin (T * Nat.size m) → Bool =>
        (⟨sampleEdgeIdx m T (List.ofFn r), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : Fin m → Fin m) ((1 / 2 : ℝ) ^ T) := by
  have hk : m ≤ 2 ^ Nat.size m := (Nat.lt_size_self m).le
  have hpos : 0 < Nat.size m := Nat.size_pos.2 hm
  have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (Nat.sub_lt hpos one_pos)
  have h2 : 2 ^ Nat.size m ≤ 2 * m := by
    have : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have h := (statClose_rejectionSample m (Nat.size m) T hm hk ⟨0, hm⟩).comp_equiv_left
    (tapeEquiv T (Nat.size m))
  have h2k : (0 : ℝ) < 2 ^ Nat.size m := by positivity
  have hm' : (m : ℝ) ≤ 2 ^ Nat.size m := by exact_mod_cast hk
  have h2' : (2 : ℝ) ^ Nat.size m ≤ 2 * m := by exact_mod_cast h2
  have hle : (1 - (m : ℝ) / 2 ^ Nat.size m) ^ T ≤ (1 / 2 : ℝ) ^ T := by
    apply pow_le_pow_left₀
    · rw [sub_nonneg, div_le_one h2k]
      exact hm'
    · have : (1 / 2 : ℝ) ≤ m / 2 ^ Nat.size m := by
        rw [div_le_div_iff₀ (by norm_num) h2k]
        linarith
      linarith
  convert h.mono hle using 2 with r
  apply Fin.ext
  simp only [sampleEdgeIdx, sampleIdx_ofFn]
  cases rejectionSample m (Nat.size m) T (tapeEquiv T (Nat.size m) r) with
  | none => simp
  | some i => simp

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ProtocolProofs
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the protocol, completeness and soundness

The protocol of [PS10, Protocol 127.5] for the language `3COL` of `ThreeColoring/Language.lean`
(Def-124.f), built on a commitment scheme
`(Com, ℓ)` of `Commitment.lean`, and the completeness and soundness halves of
[PS10, Proposition 127.6]: one iteration (soundness error `1 - 1/|E|`) and the `n|E|`-fold
sequential repetition (soundness error `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`, Claim-125.a). The
zero-knowledge half is `ThreeColoring/Simulator.lean`; the machine infrastructure behind the
efficiency theorems (the parties as polynomial-time string functions of the interactive
layout) is `ThreeColoring/Machines.lean`, `ThreeColoring/Parties.lean` and
`ThreeColoring/ProtocolProofs.lean`.

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours; the edges
are enumerated by `edgeList` and the verifier's challenge is the index of an edge in that
list, sent in unary. The prover commits to the colour `π (c i)` of every vertex, padded to an
`n`-bit value (`padColor`, DQ4), with `n` the number of vertices as the security parameter of
the commitment.

**Deviations** ([PS10, Protocol 127.5], source errors 41–43 of the plan):
* the verifier checks the two openings against the commitments (the text's "`V` accepts iff
  `c'_i ≠ c'_j`" is unsound without it) and the lengths of the opening randomness;
* if `E = ∅` the verifier accepts outright (every edgeless graph is 3-colourable; the text's
  "random edge" is undefined), and if `E ≠ ∅` but the graph has fewer than two vertices (so
  the edge is a loop and the graph is not colourable) it rejects outright, which is what makes
  the `n`-bit padding of the colours injective in every case that matters;
* colours are padded to `n` bits (DQ4; the text commits to 2-bit colours, i.e. at security
  parameter `2`);
* the witness is `c₁, …, c_n` (the text lists `c₀, …, c_m`), and the protocol is repeated
  `n|E|` times (the text's proof says `|E|²`);
* (D8, D10) the colour permutation `π ← S₃` and the edge `e ← E` are rejection-sampled from
  the parties' bit tapes with `|x|` trials, so the theorems carry the statistical terms
  `(1/4)^{|x|}` and `(1/2)^{|x|}`; the repeated protocol runs `4|x|²` fixed moves of which the
  first `4 n|E|` are the iterations and the rest are empty messages;
* (run-3 audit P11-3) `Graph n` is an arbitrary Boolean relation and `E` is the list of
  ordered pairs `(u, v)` with `G u v` (`edgeList`, loops included), so for the text's
  symmetric loopless graph `edgeCount G = 2|E|`: the per-iteration soundness error
  `1 - 1/edgeCount G` is `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|`
  times; the challenge is uniform over the ordered pairs, i.e. over the text's undirected
  edges, and `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. In this file `|E|` abbreviates
  `edgeCount G`.

## Main definitions

* `TCSlib.Cryptography.colCommit`,
  `TCSlib.Cryptography.colOpen`, `TCSlib.Cryptography.colVerify` — the commitment message,
  the opening message and the verifier's check of one iteration.
* `TCSlib.Cryptography.colProver`, `TCSlib.Cryptography.colVerifier`,
  `TCSlib.Cryptography.colProtocol` — one iteration of [PS10, Protocol 127.5];
  `TCSlib.Cryptography.colProverRep`, `TCSlib.Cryptography.colVerifierRep`,
  `TCSlib.Cryptography.colProtocolRep` — the `n|E|`-fold protocol (Prot-127.5).
* `TCSlib.Cryptography.committedColor` — the colour a commitment string can be opened to
  (Lem-127.f).

## Main results

* `TCSlib.Cryptography.colVerify_honest` — completeness of one iteration (Claim-127.e).
* `TCSlib.Cryptography.committedColor_eq_some`, `TCSlib.Cryptography.exists_bad_edge` — the
  committed colouring and its bad edge (Lem-127.f).
* `TCSlib.Cryptography.uprob_adaptive_escape` — adaptive sequential soundness with escape
  probability `1/m` (Lem-127.g); `TCSlib.Cryptography.uprob_col_cheat_le` — soundness of the
  `k`-fold protocol against adaptive provers (Claim-127.h).
* `TCSlib.Cryptography.col_efficientProverProofErr`,
  `TCSlib.Cryptography.colRep_efficientProverProof` — **[PS10, Proposition 127.6]**, the
  interactive-proof half (Prop-127.6).
* `TCSlib.Cryptography.colProver_length_le`, `TCSlib.Cryptography.colProtocol_proverBounded`
  — the honest provers' messages are polynomially bounded in `|x|` (ruling G3-3).
* `TCSlib.Cryptography.R3COL_witnessRelation` — `R_3COL` is a witness relation for `3COL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring; Chapter 9, zero knowledge.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Messages of one iteration -/

/-- The `i`-th component of an encoded message list (`Strategy.encodeMsgs`): the first
projection after `i` second projections. -/
def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)

/-- `msgAt` reads the `i`-th message of an encoded list. -/
theorem msgAt_encodeMsgs (l : List (List Bool)) (i : ℕ) (hi : i < l.length) :
    msgAt (Strategy.encodeMsgs l) i = l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a l ih =>
    cases i with
    | zero => simp [msgAt]
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [msgAt, Function.iterate_succ_apply] using this

/-- The prover's first message of [PS10, Protocol 127.5]: the commitments to the (permuted)
colours `c' i`, padded to `n` bits, with randomness `r i ∈ {0,1}^{ℓ(n)}`, as one encoded list
(`multiCom`). -/
def colCommit (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3)
    (r : Fin n → Fin ℓn → Bool) : List Bool :=
  multiCom Com (fun i => padColor n (c' i)) r

/-- The prover's opening message of [PS10, Protocol 127.5] for the edge `p = (i, j)`:
`⟨⟨c'_i, r_i⟩, ⟨c'_j, r_j⟩⟩`. -/
def colOpen {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) :
    List Bool :=
  pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1)))
    (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))

/-- The verifier's check of one iteration of [PS10, Protocol 127.5] on the edge of index `e`,
the commitment message `com` and the opening `opn = ⟨⟨a, r_i⟩, ⟨b, r_j⟩⟩`: the randomness has
length `ℓ(n)`, both openings match the commitments, and `a ≠ b`.

**Deviation:** the opening check (the text's "`V` accepts iff `c'_i ≠ c'_j`"); `false` when
`E = ∅` (handled by the verifier before calling this check). -/
def colVerify (Com : List Bool → List Bool) (ℓn : ℕ) {n : ℕ} (G : Graph n) (e : ℕ)
    (com opn : List Bool) : Bool :=
  match edgeAt G e with
  | none => false
  | some p =>
    let a := decColor (pairFstD (pairFstD opn))
    let ri := pairSndD (pairFstD opn)
    let b := decColor (pairFstD (pairSndD opn))
    let rj := pairSndD (pairSndD opn)
    decide (ri.length = ℓn ∧ rj.length = ℓn ∧
      Com (pairEncode (List.ofFn (padColor n a)) ri) = msgAt com p.1 ∧
      Com (pairEncode (List.ofFn (padColor n b)) rj) = msgAt com p.2 ∧ a ≠ b)

/-- **Completeness of one iteration** [PS10, proof of Proposition 127.6, "completeness follows
by inspection"] (Claim-127.e): for a proper colouring `c`, any colour permutation `π`, any
randomness `r` and any edge `p = edgeAt G e`, the honest commitment and opening pass the
verifier's check: the openings match by `msgAt_encodeMsgs`, and `π (c i) ≠ π (c j)` since
`c i ≠ c j` on the edge and `π` is injective. -/
theorem colVerify_honest (Com : List Bool → List Bool) {n ℓn : ℕ} {G : Graph n}
    {c : Fin n → Fin 3} (hc : ProperColoring G c) (π : Equiv.Perm (Fin 3))
    (r : Fin n → Fin ℓn → Bool) {e : ℕ} {p : Fin n × Fin n} (hp : edgeAt G e = some p) :
    colVerify Com ℓn G e (colCommit Com n ℓn (fun i => π (c i)) r)
      (colOpen (fun i => π (c i)) r p) = true := by
  have hadj := edgeAt_adj G hp
  unfold colVerify
  rw [hp]
  simp only [colOpen, pairFstD_pairEncode, pairSndD_pairEncode, decColor_encColor,
    List.length_ofFn, decide_eq_true_eq]
  refine ⟨trivial, trivial, ?_, ?_, fun h => hc _ _ hadj (π.injective h)⟩
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]

/-! ### The committed colouring (Lem-127.f) -/

/-- The colour a commitment string `w` can be opened to at security parameter `n` with
randomness of length `ℓn` (Lem-127.f): `some a` if some `(a, r)` opens `w`, `none` otherwise.
By binding (`committedColor_eq_some`) the colour is unique. -/
noncomputable def committedColor (Com : List Bool → List Bool) (n ℓn : ℕ) (w : List Bool) :
    Option (Fin 3) := by
  classical
  exact if h : ∃ a : Fin 3, ∃ r : Fin ℓn → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w
    then some (Classical.choose h) else none

/-- A list of length `k` is the `ofFn` of its entries read with a default. -/
private theorem ofFn_getD_of_length {r : List Bool} {k : ℕ} (hr : r.length = k) :
    List.ofFn (fun i : Fin k => r.getD i false) = r := by
  subst hr
  exact List.ext_getElem (by simp) fun i _ h₂ => by
    simp [List.getD_eq_getElem?_getD]

/-- **The committed colouring is well defined** [PS10, proof of Proposition 127.6,
"soundness follows by the binding property"] (Lem-127.f): for a commitment scheme, `n ≥ 2`,
an opening `(a, r)` of `w` with `|r| = ℓ(n)` forces `committedColor w = some a` — any other
opening `(a', r')` would give `Com ⟨pad a', r'⟩ = Com ⟨pad a, r⟩` with `pad a' ≠ pad a`
(`padColor_injective`), contradicting `Commitment.binding_ofFn`. -/
theorem committedColor_eq_some {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {a : Fin 3} {r : List Bool}
    (hr : r.length = ℓ.eval n) {w : List Bool}
    (h : Com (pairEncode (List.ofFn (padColor n a)) r) = w) :
    committedColor Com n (ℓ.eval n) w = some a := by
  classical
  have hex : ∃ a : Fin 3, ∃ r : Fin (ℓ.eval n) → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w :=
    ⟨a, fun i => r.getD i false, by rwa [ofFn_getD_of_length hr]⟩
  unfold committedColor
  rw [dif_pos hex, Option.some.injEq]
  obtain ⟨r', hr'⟩ := Classical.choose_spec hex
  by_contra hne
  have hpad : padColor n (Classical.choose hex) ≠ padColor n a :=
    fun h' => hne (padColor_injective hn h')
  have := hC.binding_ofFn hpad r' (fun i => r.getD i false)
  rw [ofFn_getD_of_length hr, hr', h] at this
  exact this rfl

/-- **A non-colourable graph has a bad edge for every partial colouring**
[PS10, proof of Proposition 127.6, "for each coloring there exists at least one edge which
has the same colors on both endpoints"] (Lem-127.f): if `G` is not 3-colourable then for every
`ct : Fin n → Option (Fin 3)` some edge has an uncoloured endpoint or equal colours at both
endpoints — otherwise `i ↦ (ct i).getD 0` would be a proper colouring. -/
theorem exists_bad_edge {n : ℕ} {G : Graph n} (hG : ¬ ThreeColorable G)
    (ct : Fin n → Option (Fin 3)) :
    ∃ e : Fin (edgeCount G), ct (edgeOf G e).1 = none ∨ ct (edgeOf G e).2 = none ∨
      ct (edgeOf G e).1 = ct (edgeOf G e).2 := by
  by_contra hcon
  push_neg at hcon
  refine hG ⟨fun i => (ct i).getD 0, fun u v huv heq => ?_⟩
  obtain ⟨e, he⟩ := exists_edgeOf_eq G huv
  obtain ⟨h1, h2, h3⟩ := hcon e
  simp only [he] at h1 h2 h3
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 h2
  simp only [ha, hb] at h3 heq
  exact h3 (by simpa using heq)

/-! ### Adaptive sequential soundness (Lem-127.g, Claim-127.h) -/

/-- The strict prefix `e_0, …, e_{i-1}` of a challenge tuple (the history an adaptive prover
has seen before challenge `i`). -/
def challengesBefore {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin i → α :=
  fun j => e (Fin.castLE i.isLt.le j)

/-- The prefix `e_0, …, e_i` of a challenge tuple (the history including the current
challenge). -/
def challengesUpTo {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin (i + 1) → α :=
  fun j => e (Fin.castLE i.isLt j)

/-- A `(k+1)`-tuple of challenges with auxiliary data as a `k`-tuple, the data and the last
challenge (`Fin.snoc`): the splitting of the sequential-soundness induction. -/
private def snocEquivW (k m : ℕ) (W : Type*) :
    ((Fin k → Fin m) × W) × Fin m ≃ (Fin (k + 1) → Fin m) × W where
  toFun y := (Fin.snoc y.1.1 y.2, y.1.2)
  invFun z := ((Fin.init z.1, z.2), z.1 (Fin.last k))
  left_inv y := by
    rcases y with ⟨⟨e, w⟩, x⟩
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv z := by
    rcases z with ⟨e, w⟩
    simp [Fin.snoc_init_self]

/-- The history before a non-final challenge of `Fin.snoc e x` is the history before it in `e`. -/
private theorem challengesBefore_snoc_castSucc {k m : ℕ} (e : Fin k → Fin m) (x : Fin m)
    (i : Fin k) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.castSucc i) =
      challengesBefore e i := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (k + 1)) =
      Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- The history before the last challenge of `Fin.snoc e x` is `e`. -/
private theorem challengesBefore_snoc_last {k m : ℕ} (e : Fin k → Fin m) (x : Fin m) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.last k) = e := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.last k).isLt.le j : Fin (k + 1)) = Fin.castSucc j := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- **Adaptive sequential soundness with escape probability `1/m`** [PS10, proof of
Proposition 127.6, "in each iteration a cheating prover is caught with probability `1/|E|`"]
(Lem-127.g): for `k` rounds with uniform challenges `e_i ∈ [m]` and, for every round, a
nonempty set `Bad i` of challenges (depending on the earlier challenges and on the prover's
coins `w`) on which the prover is caught, the probability that no challenge ever lands in its
bad set is at most `(1 - 1/m)^k`.

**Proof sketch.** Induction on `k`. Split the tuple as `Fin.snoc e' e_last` (the bijection
`(Fin (k+1) → Fin m) ≃ (Fin k → Fin m) × Fin m`, `Fin.snocEquiv`; `uprob_comp_equiv`); by
`uprob_prod` the probability is the average over `(e', w)` of the probability over `e_last`,
which is `0` if some earlier round is caught and at most `1 - |Bad k e' w| / m ≤ 1 - 1/m` otherwise
(`uprob_eq_card_filter`, `Finset.card_pos` from `hBad`); so the total is at most `(1 - 1/m)`
times the probability of the `k`-round event (`OneWay.uprob_and_le_mul`), and the induction
hypothesis applies to the latter. -/
theorem uprob_adaptive_escape (m k : ℕ) (hm : 0 < m) {W : Type*} [Fintype W]
    (Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m))
    (hBad : ∀ i h w, (Bad i h w).Nonempty) :
    uprob (fun z : (Fin k → Fin m) × W => ∀ i, z.1 i ∉ Bad i (challengesBefore z.1 i) z.2) ≤
      (1 - 1 / (m : ℝ)) ^ k := by
  induction k with
  | zero => simpa using uprob_le_one _
  | succ k ih =>
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hθ : 0 ≤ 1 - 1 / (m : ℝ) := by
      rw [sub_nonneg, div_le_one hm']
      exact_mod_cast hm
    have hih := ih (fun i h w => Bad (Fin.castSucc i) h w) (fun i h w => hBad _ _ _)
    rw [← uprob_comp_equiv (snocEquivW k m W)]
    have hmono : uprob (fun y : ((Fin k → Fin m) × W) × Fin m => ∀ i,
          ((snocEquivW k m W) y).1 i ∉
            Bad i (challengesBefore ((snocEquivW k m W) y).1 i) ((snocEquivW k m W) y).2) ≤
        uprob (fun y : ((Fin k → Fin m) × W) × Fin m =>
          (∀ i, y.1.1 i ∉ Bad (Fin.castSucc i) (challengesBefore y.1.1 i) y.1.2) ∧
            y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2) := by
      apply uprob_mono
      rintro ⟨⟨e, w⟩, x⟩ h
      refine ⟨fun i => ?_, ?_⟩
      · have := h (Fin.castSucc i)
        simpa [snocEquivW, Fin.snoc_castSucc, challengesBefore_snoc_castSucc] using this
      · have := h (Fin.last k)
        simpa [snocEquivW, Fin.snoc_last, challengesBefore_snoc_last] using this
    have hbound := OneWay.uprob_and_le_mul
      (fun a : (Fin k → Fin m) × W => ∀ i, a.1 i ∉ Bad (Fin.castSucc i) (challengesBefore a.1 i) a.2)
      (fun y : ((Fin k → Fin m) × W) × Fin m => y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2)
      (θ := 1 - 1 / (m : ℝ)) (fun a _ => ?_)
    · calc _ ≤ _ := hmono
        _ ≤ _ := hbound
        _ ≤ (1 - 1 / (m : ℝ)) * (1 - 1 / (m : ℝ)) ^ k := mul_le_mul_of_nonneg_left hih hθ
        _ = (1 - 1 / (m : ℝ)) ^ (k + 1) := by ring
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      classical
      rw [uprob_not, uprob_eq_card_filter, Fintype.card_fin]
      have hcard : 1 ≤ (Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact Finset.card_pos.2 (hBad _ _ _)
      have : (1 : ℝ) / m ≤
          ((Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card : ℝ) / m := by
        gcongr
        exact_mod_cast hcard
      linarith

/-- **Soundness of the `k`-fold protocol against adaptive provers** [PS10, proof of
Proposition 127.6] (Claim-127.h, concrete): for a commitment scheme, a graph on `n ≥ 2`
vertices that is not 3-colourable, and a cheating prover whose `i`-th commitment message
`comF i` depends on the earlier challenges and its coins `w`, and whose `i`-th opening
`opnF i` also depends on the current challenge, the verifier accepts all `k` iterations with
probability at most `(1 - 1/|E|)^k` over the uniform challenges and `w` (`|E| = edgeCount G`,
the number of ordered edge pairs; run-3 audit P11-3).

**Proof sketch.** Apply `uprob_adaptive_escape` with
`Bad i h w := {e | the edge `edgeOf G e` is bad for the committed colouring
`k ↦ committedColor Com n ℓ(n) (msgAt (comF i h w) k)`}`, nonempty by `exists_bad_edge`
(`edgeCount_pos_of_not_threeColorable`). Acceptance in round `i` on the challenge `e_i`
means (`colVerify`, `edgeAt_eq_some_edgeOf`) that both openings `(a, r_i)`, `(b, r_j)` have
randomness of length `ℓ(n)` and match the commitments at the endpoints, so by
`committedColor_eq_some` the committed colours at the endpoints are `some a`, `some b` with
`a ≠ b`: the edge is not bad, i.e. `e_i ∉ Bad i …`. Hence the acceptance event is contained
in the escape event (`uprob_mono`). -/
theorem uprob_col_cheat_le {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G) (k : ℕ) {W : Type*} [Fintype W]
    (comF : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → List Bool)
    (opnF : (i : Fin k) → (Fin (i + 1) → Fin (edgeCount G)) → W → List Bool) :
    uprob (fun z : (Fin k → Fin (edgeCount G)) × W => ∀ i,
      colVerify Com (ℓ.eval n) G (z.1 i) (comF i (challengesBefore z.1 i) z.2)
        (opnF i (challengesUpTo z.1 i) z.2) = true) ≤
      (1 - 1 / (edgeCount G : ℝ)) ^ k := by
  classical
  have hm := edgeCount_pos_of_not_threeColorable hG
  let ct : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Fin n → Option (Fin 3) :=
    fun i h w v => committedColor Com n (ℓ.eval n) (msgAt (comF i h w) v)
  let Bad : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Finset (Fin (edgeCount G)) :=
    fun i h w => Finset.univ.filter fun e => ct i h w (edgeOf G e).1 = none ∨
      ct i h w (edgeOf G e).2 = none ∨ ct i h w (edgeOf G e).1 = ct i h w (edgeOf G e).2
  have hBad : ∀ i h w, (Bad i h w).Nonempty := by
    intro i h w
    obtain ⟨e, he⟩ := exists_bad_edge hG (ct i h w)
    exact ⟨e, by simpa [Bad] using he⟩
  refine le_trans (uprob_mono ?_) (uprob_adaptive_escape (edgeCount G) k hm Bad hBad)
  rintro ⟨es, w⟩ hacc i
  have h := hacc i
  simp only at h ⊢
  unfold colVerify at h
  rw [edgeAt_eq_some_edgeOf] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hri, hrj, hci, hcj, hab⟩ := h
  have h1 := committedColor_eq_some hC hn hri hci
  have h2 := committedColor_eq_some hC hn hrj hcj
  simp only [Bad, ct, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
  rw [h1, h2]
  simp [hab]

/-! ### Protocol 127.5, one iteration (Prot-127.5) -/

/-- The well-formedness test of a common input: `x` is the encoding of the graph it decodes
to (i.e. `|x|` is a perfect square). -/
def colWellFormed (x : List Bool) : Bool := decide (x = encGraph (decGraph x).2)

/-- An encoded graph is well formed. -/
theorem colWellFormed_encGraph {n : ℕ} (G : Graph n) : colWellFormed (encGraph G) = true := by
  unfold colWellFormed
  rw [decide_eq_true_eq]
  have h := decGraph_encGraph G
  rw [show encGraph (decGraph (encGraph G)).2 = encGraph (⟨n, G⟩ : Σ n, Graph n).2 by rw [h]]

/-- The honest prover of one iteration of [PS10, Protocol 127.5] (Prot-127.5): with common
input `x = encGraph G` (`n` vertices) and witness `y = encColoring c`, it samples `π ← S₃` from
the first `3|x|` bits of its tape and `r_i ∈ {0,1}^{ℓ(n)}` from the next `n ℓ(n)` bits; on the
empty history it sends the commitments to `π (c i)` (`colCommit`), and on the challenge `w`
it opens the two commitments of the edge `edgeAt G (edgeIdxOfMsg |E| w)` (`colOpen`), or
sends `[]` if `E = ∅`. Coins: `3|x| + |x| ℓ(|x|)` bits (an upper bound for every `n ≤ |x|`).

**Deviation (D10):** `π` by rejection sampling (identity on failure). -/
noncomputable def colProver (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .add (.mul (.const 3) .var) (.mul .var ℓ)
  next x y r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let c := decColoring n y
    let π := samplePerm3 x.length (r.take (3 * x.length))
    let rr : Fin n → Fin (ℓ.eval n) → Bool :=
      fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false
    let c' : Fin n → Fin 3 := fun i => π (c i)
    match hist with
    | [] => colCommit Com n (ℓ.eval n) c' rr
    | w :: _ =>
      match edgeAt G (edgeIdxOfMsg (edgeCount G) w) with
      | some p => colOpen c' rr p
      | none => []

/-- The verifier of one iteration of [PS10, Protocol 127.5] (Prot-127.5): it samples the
edge index `e ← [|E|]` from its tape (`sampleEdgeIdx` with `|x|` trials); on the commitment
message it sends `1^e`; on the complete history `[com, opn]` it outputs `[true]` iff `x` is
well formed and either `E = ∅` or (`n ≥ 2` and `colVerify` accepts the openings on the edge
`e`). Coins: `(|x| + 1)²` bits.

**Deviation:** opening check, `E = ∅` accepted outright, `n < 2` with `E ≠ ∅` rejected outright,
well-formedness test (see the module docstring); `e` by rejection sampling (D10). -/
noncomputable def colVerifier (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .normal 1 2
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e := sampleEdgeIdx m x.length r
    match hist with
    | [com, opn] => [decide (colWellFormed x = true ∧
        (m = 0 ∨ (2 ≤ n ∧ colVerify Com (ℓ.eval n) G e com opn = true)))]
    | [_] => edgeMsg e
    | _ => [false]

/-- One iteration of [PS10, Protocol 127.5] (Prot-127.5): three messages (commitments,
edge, openings), prover first; the verdict is the verifier's activation on `[com, opn]`. -/
noncomputable def colProtocol (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProver Com ℓ
  V := colVerifier Com ℓ
  rounds := .const 3
  verifierFirst := false

/-! ### The `n|E|`-fold protocol (Prot-127.5, repeated) -/

/-- The `t`-th block of `c` bits of a tape (the coins of iteration `t` of the repeated
protocol). -/
def colCoinSlice (c t : ℕ) (r : List Bool) : List Bool := (r.drop (t * c)).take c

/-- The number of iterations of the repeated protocol on `x`: `n |E|` [PS10, Protocol 127.5,
"repeat the procedure `n|E|` times"], with `|E| = edgeCount G` the number of ordered edge
pairs (for the text's simple graph `2n|E|` iterations; run-3 audit P11-3). -/
def colIterations (x : List Bool) : ℕ := (decGraph x).1 * edgeCount (decGraph x).2

/-- The prover of the `n|E|`-fold protocol: iteration `t = hist.length / 2` (it has received
the challenges and the empty verifier messages of the earlier iterations) runs `colProver`
on the `t`-th block of `3|x| + |x| ℓ(|x|)` coins; after the `n|E|` iterations it sends `[]`. -/
noncomputable def colProverRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.add (.mul (.const 3) .var) (.mul .var ℓ))
  next x y r hist :=
    let t := hist.length / 2
    if t < colIterations x then
      (colProver Com ℓ).next x y
        (colCoinSlice ((colProver Com ℓ).coinLen x.length) t r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []

/-- The verifier of the `n|E|`-fold protocol: it has received `[com_0, opn_0, com_1, …]`; on
an odd history it sends the challenge of iteration `t = hist.length / 2` (from the `t`-th
block of `(|x|+1)²` coins); on the complete history (`2|x|²` received messages) it accepts iff
`x` is well formed and either `E = ∅` or `n ≥ 2` and every one of the `n|E|` iterations passes
`colVerify`; on every other even history it sends `[]`. -/
noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.normal 1 2)
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e : ℕ → ℕ := fun t => sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t r)
    if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (e (hist.length / 2)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (m = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (colIterations x),
        colVerify Com (ℓ.eval n) G (e t) (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []

/-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
per iteration (commitments, edge, openings, and a verifier message, empty except for the final
verdict; D8 fixed alternation), `4|x|²` moves in all, of which the first `4 n|E|` carry the
iterations. -/
noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProverRep Com ℓ
  V := colVerifierRep Com ℓ
  rounds := .mul (.const 4) (.mul .var .var)
  verifierFirst := false

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of one iteration is efficient (D8) when `Com` is polynomial-time
[PS10, Proposition 127.6, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^N, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`): `n = Nat.sqrt |x|`
in unary by `polyTimeComputable_iterateFind` over `polyTimeComputable_lenLe` against unary
squares; `π` by `polyTimeComputable_iterateFind` over the `|x|` three-bit trials
(`pairTakePoly`/`pairDropPoly`); the `n` commitments by `polyTimeComputable_blockMap ℓ` on
the randomness blocks composed with `hCom` on `⟨pad (π (c i)), r_i⟩` (`PolyTimeComputable.pairEncode`,
the colour permutation as a table lookup, `polyTimeComputable_ite`) and
`polyTimeComputable_iterateEmit` for the `encodeMsgs` fold; the opening by the two projections
of the challenge's decoded index (`polyTimeComputable_lenLe` against the unary `|E|`, the edge
list scanned by `polyTimeComputable_iterateFind`); the case split on `msgs = []` by
`polyTimeComputable_lenEq`. The equation with `colProver.next` is
`NUPPT.runAtL_ofPolyTimeUniform` and `Strategy.pairFstD_encodeMsgs`. -/
theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
  ColProofs.colProver_efficient hCom ℓ

/-- The verifier of one iteration is efficient (D8) when `Com` is polynomial-time
[PS10, Definition 116.1 for Proposition 127.6] (Inf-4.2).

**Proof sketch.** As `colProver_efficient`: the edge index by `polyTimeComputable_iterateFind`
over the `|x|` trials of `Nat.size |E|` bits (`|E|` in unary by scanning the matrix with
`polyTimeComputable_iterateEmit`), the challenge `1^e` by `polyTimeComputable_unaryPoly`-style
emission, and the verdict by `polyTimeComputable_and` of the well-formedness test
(`polyTimeComputable_pairEq` on `x` and the re-encoded matrix), the two commitment checks
(`hCom` on the parsed openings, `msgAt` by `polyTimeComputable_iterate_pairFstD`-style
projections, `polyTimeComputable_pairEq`), the length tests (`polyTimeComputable_lenEq`) and
the colour comparison. -/
theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
  ColProofs.colVerifier_efficient hCom ℓ

/-- The prover of the `n|E|`-fold protocol is efficient (D8) (Inf-4.2): `colProver_efficient`
on the coin block `hist.length / 2` cut by `pairTakePoly`/`pairDropPoly`, with the parity and
iteration tests by `polyTimeComputable_lenLe` on unary counters. -/
theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
  ColProofs.colProverRep_efficient hCom ℓ

/-- The verifier of the `n|E|`-fold protocol is efficient (D8) (Inf-4.2): the challenge as in
`colVerifier_efficient` on the block `hist.length / 2`, and the verdict a loop over the
`n|E|` pairs of the history (`polyTimeComputable_iterate` with an accumulated conjunction of
`colVerify` checks). -/
theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
  ColProofs.colVerifierRep_efficient hCom ℓ

/-! ### Bounded prover messages (ruling G3-3 of gate 03) -/

/-- A vector of `q` commitments to `n`-bit values with `m`-bit randomness has at most
`q (2 C (2n + 3 + m)^c + 2)` bits when `C (|w| + 1)^c` bounds `|Com w|`
(`CommitmentLemmas.length_encodeMsgs_le`, `length_pairEncode`). -/
theorem length_multiCom_le {Com : List Bool → List Bool} {C c : ℕ}
    (hC : ∀ w, (Com w).length ≤ C * (w.length + 1) ^ c) {q n m : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin m → Bool) :
    (multiCom Com v r).length ≤ q * (2 * (C * (2 * n + 3 + m) ^ c) + 2) := by
  unfold multiCom
  refine (CommitmentLemmas.length_encodeMsgs_le _ (C * (2 * n + 3 + m) ^ c)
    fun msg hmsg => ?_).trans (by simp)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hmsg
  refine (hC _).trans (le_of_eq ?_)
  rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
  ring_nf

/-- **The honest prover of one iteration sends polynomially bounded messages** (ruling G3-3 of
gate 03): for `C (|w| + 1)^c` bounding `|Com w|` and `n = (decGraph x).1 ≤ |x|`, the
commitment message has at most `n (2 C (2n + 3 + ℓ(n))^c + 2)` bits (`length_multiCom_le`),
the opening `3 ℓ(n) + 20` (`length_pairEncode`, `length_encColoring`) and the empty reply none;
`ℓ` is monotone (`PolyExpr.eval_mono`). The bound holds for every tape and history, since
`colCommit` and `colOpen` have a fixed shape. -/
theorem colProver_length_le {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : ∃ B : PolyExpr, ∀ x y r hist,
      ((colProver Com ℓ).next x y r hist).length ≤ B.eval x.length := by
  obtain ⟨C, c, hC⟩ := hCom.output_length_le
  refine ⟨.add (.mul .var (.add (.mul (.const 2) (.mul (.const C)
    (.pow (.add (.add (.mul (.const 2) .var) (.const 3)) ℓ) c))) (.const 2)))
    (.add (.mul (.const 3) ℓ) (.const 20)), fun x y r hist => ?_⟩
  have hn : (decGraph x).1 ≤ x.length := Nat.sqrt_le_self _
  have hℓ : ℓ.eval (decGraph x).1 ≤ ℓ.eval x.length := ℓ.eval_mono hn
  have hcom : (decGraph x).1 * (2 * (C * (2 * (decGraph x).1 + 3 + ℓ.eval (decGraph x).1) ^ c) + 2)
      ≤ x.length * (2 * (C * (2 * x.length + 3 + ℓ.eval x.length) ^ c) + 2) := by
    gcongr
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var, colProver]
  split
  · exact (length_multiCom_le hC _ _).trans (hcom.trans (Nat.le_add_right _ _))
  · split
    · simp only [colOpen, length_pairEncode, List.length_ofFn, encColor, length_encColoring]
      omega
    · simp

/-- **The honest provers of [PS10, Protocol 127.5] send polynomially bounded messages**, one
iteration and `n|E|`-fold, on every instance (ruling G3-3 of gate 03): the bound of
`colProver_length_le` from the commitment's polynomial-time evaluator; the repeated prover
runs `colProver` on a coin block or sends `[]`. -/
theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) (R : List Bool → List Bool → Prop) :
    ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
      (colProtocolRep Com ℓ).ProverBounded R B := by
  obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
  refine ⟨B, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => hB x y r hist,
    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => ?_⟩
  show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
  simp only [colProverRep]
  split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _

/-! ### Proposition 127.6, interactive-proof half -/

section OneIteration

open ColMachines

/-! ### Unfolding the parties on a decoded instance -/

/-- The verifier's verdict on `[com, opn]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_two_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com opn : List Bool) :
    (colVerifier Com ℓ).next x z r [com, opn] =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length r) com opn = true)))] := by
  show [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
    colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
      (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) com opn = true)))] = _
  rw [hx]

/-- The verifier's challenge on `[com]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_one_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com : List Bool) :
    (colVerifier Com ℓ).next x z r [com] = edgeMsg (sampleEdgeIdx (edgeCount G) x.length r) := by
  show edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) = _
  rw [hx]

/-- The prover's commitments, on an input decoding to `⟨n, G⟩`. -/
private theorem colProver_next_nil_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) :
    (colProver Com ℓ).next x y r [] = colCommit Com n (ℓ.eval n)
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false) := by
  show colCommit Com (decGraph x).1 (ℓ.eval (decGraph x).1)
    (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i))
    (fun i j => r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) = _
  rw [hx]

/-- The prover's opening, on an input decoding to `⟨n, G⟩` with at least one edge. -/
private theorem colProver_next_cons_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : 0 < edgeCount G) (y r w : List Bool)
    (h : List (List Bool)) :
    (colProver Com ℓ).next x y r (w :: h) = colOpen
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun (i : Fin n) (j : Fin (ℓ.eval n)) => r.getD (3 * x.length + i * ℓ.eval n + j) false)
      (edgeOf G ⟨edgeIdxOfMsg (edgeCount G) w % edgeCount G, Nat.mod_lt _ hm⟩) := by
  simp only [colProver]
  rw [hx]
  dsimp only
  rw [edgeAt_eq_some_of_pos G hm]

/-- The verdict of one iteration against any prover `P'`: the verifier's activation on the
two prover messages, the second being the reply to the challenge. -/
private theorem colProtocol_outV (Com : List Bool → List Bool) (ℓ : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (colProtocol Com ℓ).ExecCoins P' x) :
    (colProtocol Com ℓ).outV P' x y z r =
      (colVerifier Com ℓ).next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [],
          P'.next x y (List.ofFn r.1)
            [(colVerifier Com ℓ).next x z (List.ofFn r.2) [P'.next x y (List.ofFn r.1) []]]] := rfl

/-! ### Completeness -/

/-- **The honest execution accepts** on every pair of random tapes: for a proper colouring the
verdict is `[true]`. -/
private theorem colProtocol_outV_honest {Com : List Bool → List Bool} {ℓ : PolyExpr} {n : ℕ}
    {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c) (z : List Bool)
    (r : (colProtocol Com ℓ).ExecCoins (colProtocol Com ℓ).P (encGraph G)) :
    (colProtocol Com ℓ).outV (colProtocol Com ℓ).P (encGraph G) (encColoring c) z r = [true] := by
  have hx : decGraph (encGraph G) = ⟨n, G⟩ := decGraph_encGraph G
  rw [colProtocol_outV]
  show (colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ [], (colProver Com ℓ).next _ _ _
    [(colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ []]]] = _
  rw [colVerifier_next_one_of Com ℓ hx, colProver_next_nil_of Com ℓ hx, colVerifier_next_two_of Com ℓ hx,
    colWellFormed_encGraph, decColoring_encColoring]
  by_cases hm : edgeCount G = 0
  · simp [hm]
  · have hpos := Nat.pos_of_ne_zero hm
    have he := sampleEdgeIdx_lt hpos (encGraph G).length (List.ofFn r.2)
    rw [colProver_next_cons_of Com ℓ hx hpos, decColoring_encColoring]
    simp only [edgeIdxOfMsg_edgeMsg he]
    rw [colVerify_honest Com hc _ _ (edgeAt_eq_some_of_pos G hpos _)]
    simp [ColProofs.two_le_of_edge hc hpos]

/-! ### Soundness -/

/-- **One-round soundness bound against a deterministic prover:** for a non-colourable graph
on `n ≥ 2` vertices, the verifier's check on a uniform edge index `e`, a fixed commitment
message and an opening depending on `e`, passes with probability at most `1 - 1/|E|`
(`uprob_col_cheat_le` at `k = 1`). -/
private theorem uprob_check_uniform_le {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G)
    (com : List Bool) (opn : ℕ → List Bool) :
    uprob (fun e : Fin (edgeCount G) => colVerify Com (ℓ.eval n) G e com (opn e) = true) ≤
      1 - 1 / (edgeCount G : ℝ) := by
  have h := uprob_col_cheat_le hC hn hG 1 (W := Unit) (fun _ _ _ => com)
    (fun i h _ => opn (h (Fin.last i)))
  rw [pow_one] at h
  refine le_trans ?_ h
  rw [← uprob_comp_equiv (ColProofs.finOneEquiv (edgeCount G))]
  apply uprob_mono
  intro e he i
  rw [Fin.fin_one_eq_zero i]
  exact he

/-- **Soundness of one iteration** [PS10, Proposition 127.6]: for `x ∉ 3COL` and any prover,
the verifier rejects with probability at least `1 - (1 - 1/|x| + (1/2)^{|x|})`. -/
private theorem colProtocol_sound {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    (x : List Bool) (hx : x ∉ L3COL) (P' : Strategy) (z : List Bool) :
    1 - (1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length) ≤
      uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
        (colProtocol Com ℓ).outV P' x [] z r = [false]) := by
  have hs0 : (0 : ℝ) ≤ 1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length := by
    have h1 : 1 / (x.length : ℝ) ≤ 1 := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · rw [h]; simp
      · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ x.length := by positivity
    linarith
  -- reduce to a bound on the acceptance probability
  suffices key : uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
      ¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ≤
        1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length by
    rw [uprob_not] at key
    linarith
  set n := (decGraph x).1 with hn_def
  set G := (decGraph x).2 with hG_def
  have hx' : decGraph x = ⟨n, G⟩ := rfl
  have hout : ∀ r : (colProtocol Com ℓ).ExecCoins P' x, (colProtocol Com ℓ).outV P' x [] z r =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
          (P'.next x [] (List.ofFn r.1) [])
          (P'.next x [] (List.ofFn r.1)
            [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true)))] := by
    intro r
    rw [colProtocol_outV, colVerifier_next_one_of Com ℓ hx', colVerifier_next_two_of Com ℓ hx']
  by_cases hwf : colWellFormed x = true
  · have hxG : x = encGraph G := of_decide_eq_true hwf
    have hnc : ¬ ThreeColorable G := fun h => hx (hxG ▸ (encGraph_mem_L3COL_iff G).2 h)
    have hm : 0 < edgeCount G := edgeCount_pos_of_not_threeColorable hnc
    by_cases hn : 2 ≤ n
    · -- the acceptance event is the verifier's check
      have hacc : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          (¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ↔
            colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
              (P'.next x [] (List.ofFn r.1) [])
              (P'.next x [] (List.ofFn r.1)
                [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true := by
        intro r
        rw [hout r]
        simp [hwf, hm.ne', hn]
      -- fix the prover's coins
      obtain ⟨rP, hrP⟩ := (colProtocol Com ℓ).exists_proverCoins_le P' x [] z fun o => ¬ o = [false]
      refine hrP.trans ?_
      rw [OneWay.uprob_congr fun rV => hacc (rP, rV)]
      -- the sampled edge is close to uniform on the verifier's tape
      have hmx : edgeCount G ≤ x.length := by
        have h1 : x.length = n * n := by rw [hxG, length_encGraph]
        rw [edgeCount_eq G x (decGraph_apply x), h1]
        exact countTrue_le _ _
      have hle : x.length * Nat.size (edgeCount G) ≤ (colVerifier Com ℓ).coinLen x.length := by
        show x.length * Nat.size (edgeCount G) ≤ 1 * (x.length + 1) ^ 2
        have h1 : Nat.size (edgeCount G) ≤ x.length :=
          (Nat.size_le_size hmx).trans (Nat.size_le.2 Nat.lt_two_pow_self)
        calc x.length * Nat.size (edgeCount G) ≤ x.length * x.length := Nat.mul_le_mul_left _ h1
          _ ≤ 1 * (x.length + 1) ^ 2 := by nlinarith
      have hclose := (statClose_sampleEdgeIdx hm x.length).comp_pushesUniform
        (ColProofs.pushesUniform_castLE hle)
      have hbound := hclose.uprob_le_add fun e : Fin (edgeCount G) =>
        colVerify Com (ℓ.eval n) G e (P'.next x [] (List.ofFn rP) [])
          (P'.next x [] (List.ofFn rP) [edgeMsg e]) = true
      simp only [id] at hbound
      have hev : ∀ rV : (colVerifier Com ℓ).Coins x.length,
          (colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))
            (P'.next x [] (List.ofFn (rP, rV).1) [])
            (P'.next x [] (List.ofFn (rP, rV).1)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))]) = true) ↔
          (colVerify Com (ℓ.eval n) G
            (sampleEdgeIdx (edgeCount G) x.length (List.ofFn fun i => rV (Fin.castLE hle i)))
            (P'.next x [] (List.ofFn rP) [])
            (P'.next x [] (List.ofFn rP)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length
                (List.ofFn fun i => rV (Fin.castLE hle i)))]) = true) := by
        intro rV
        rw [← ColProofs.sampleEdgeIdx_ofFn_castLE hle rV]
      refine (le_of_eq (OneWay.uprob_congr hev)).trans (hbound.trans ?_)
      have hcheat := uprob_check_uniform_le hC hn hnc (P'.next x [] (List.ofFn rP) [])
        fun e => P'.next x [] (List.ofFn rP) [edgeMsg e]
      have hinv : 1 / (x.length : ℝ) ≤ 1 / (edgeCount G : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmx)
      linarith
    · -- fewer than two vertices with an edge: the verifier rejects outright
      have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
        intro r
        rw [hout r]
        simp [hm.ne', hn]
      rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
      rw [uprob_false]
      exact hs0
  · have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
        ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
      intro r
      rw [hout r]
      simp [hwf]
    rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
    rw [uprob_false]
    exact hs0

end OneIteration


/-- `R_3COL` is a witness relation for `3COL` [PS10, Definition 191.11 for Theorem 124.1]:
witnesses have length `2n ≤ 2|x|`, and the relation is decided in polynomial time by
re-encoding the decoded graph and colouring and checking every edge.

**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))`, correct by `decGraph_encGraph` and
`decColoring_encColoring`, and polynomial-time by `polyTimeComputable_pairEq` on the
re-encodings (`polyTimeComputable_blockMap`, `polyTimeComputable_iterateEmit`) and a scan of
the `n²` entries for the colouring test (`polyTimeComputable_iterate` with an accumulated
conjunction). -/
theorem R3COL_witnessRelation : WitnessRelation L3COL R3COL := by
  refine ⟨mem_L3COL_iff, ⟨.mul (.const 2) .var, ?_⟩, ?_⟩
  · rintro x y ⟨n, G, c, rfl, rfl, -⟩
    rw [length_encColoring, length_encGraph, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_var]
    nlinarith [Nat.zero_le n]
  · sorry

/-- **One iteration of [PS10, Protocol 127.5] is an interactive proof for `3COL` with
efficient prover and soundness error `1 - 1/|x| + (1/2)^{|x|}`** [PS10, Proposition 127.6,
one iteration: "a cheating prover is caught with probability `1/|E|`"] (Prop-127.6,
Claim-127.e, Claim-127.h).

**Deviation (D10):** the error `1 - 1/|E|` is stated through `|E| ≤ |x|`, plus the edge
sampler's failure term `(1/2)^{|x|}`; here `|E| = edgeCount G ≤ n² = |x|` counts ordered
pairs (run-3 audit P11-3), which is what makes `|E| ≤ |x|` immediate.

**Proof sketch.** Completeness for every witness: for `x = encGraph G`, `y = encColoring c`
with `c` proper, the transcript is `[com, opn]` with `com = colCommit (π ∘ c) r` and
`opn = colOpen (π ∘ c) r p` for `p = edgeAt G e` (`exec_succ` three times, `decGraph_encGraph`,
`decColoring_encColoring`, `edgeIdxOfMsg_edgeMsg` with `sampleEdgeIdx_lt`), and the verdict is
`[true]` by `colWellFormed_encGraph`, `colVerify_honest` when `E ≠ ∅` (then `n ≥ 2`: a graph
with an edge and a proper colouring has two distinct vertices) and outright when `E = ∅`, for
every value of `π` and `e` (`HardcoreBit.uprob_eq_one_of_forall`). Completeness of
`InteractiveProofErr` is the witness of `mem_L3COL_iff`. Soundness: for `x ∉ 3COL` either
`colWellFormed x = false` (verdict `[false]` always) or `x = encGraph G` with `¬ ThreeColorable G`
(`encGraph_mem_L3COL_iff`), so `0 < |E|` (`edgeCount_pos_of_not_threeColorable`); if `n < 2`
the verdict is `[false]`; otherwise fix the prover's coins (`Protocol.exists_proverCoins_le`),
replace the sampled edge by a uniform one (`statClose_sampleEdgeIdx`,
`StatClose.abs_uprob_sub_le_prod`, cost `(1/2)^{|x|}`), and apply `uprob_col_cheat_le` with
`k = 1`, `comF :=` the prover's first message and `opnF :=` its reply to `1^e`, giving
`Pr[accept] ≤ 1 - 1/|E| + (1/2)^{|x|} ≤ 1 - 1/|x| + (1/2)^{|x|}` (`|E| ≤ n² = |x|`), i.e. the
`[false]` probability is at least `1 - s |x|` (`uprob_not`). Efficiency:
`colProver_efficient`, `colVerifier_efficient` from `hC.easy`. -/
theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
      (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) where
  efficientV := colVerifier_efficient hC.easy ℓ
  complete := by
    obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
    refine ⟨B, fun x hx => ?_⟩
    obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
    exact ⟨encColoring c,
      fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
      fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
  sound := fun x hx P' z => colProtocol_sound hC x hx P' z
  efficientP := colProver_efficient hC.easy ℓ
  boundedP := (colProtocol_proverBounded hC R3COL).imp fun _ h => h.1
  completeWitness := by
    rintro x y ⟨n, G, c, rfl, rfl, hc⟩ z
    exact HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r

/-- **The `n|E|`-fold [PS10, Protocol 127.5] is an interactive proof for `3COL` with efficient
prover** [PS10, Proposition 127.6, "the probability of successfully cheating in all rounds is
`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Prop-127.6, Claim-127.h, Claim-125.a).

**Deviation:** `n|E|` iterations inside `4|x|²` fixed moves (D8); the soundness error carries the
edge samplers' failure term `|x|² (1/2)^{|x|}` (D10); the text's "`|E|²` times" is the
protocol's `n|E|`.

**Proof sketch.** Completeness as in `col_efficientProverProofErr`, iteration by iteration
(the verifier's history is `[com_0, opn_0, …]` and the parity bookkeeping of `colProverRep`
/ `colVerifierRep` reproduces one iteration on each coin block, `exec_succ`; the empty
messages beyond `n|E|` iterations are ignored). Soundness with
`ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (strict clause): for `x = encGraph G`
not colourable with `n ≥ 2`, fix the prover's coins, condition on all `n|E|` edge samplers
being uniform (`statClose_sampleEdgeIdx` per block, `StatClose.prod` iterated,
`StatClose.abs_uprob_sub_le_prod`, union cost `n|E| (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`), and apply
`uprob_col_cheat_le` with `k = n|E|`, `comF i` the prover's commitment of iteration `i` (a
function of the earlier challenges through `exec`) and `opnF i` its opening: the acceptance
probability is at most `(1 - 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_exp`) with
`n = Nat.sqrt |x|` (`length_encGraph`, `Nat.sqrt_eq`). Negligibility:
`negligible_exp_neg_sqrt_div` with `C = 1`, `Negligible.mul_pow negligible_two_pow_neg 2`,
`negligible_two_pow_neg`, `Negligible.add`. Efficiency: `colProverRep_efficient`,
`colVerifierRep_efficient`. Bounded prover messages (and the bound in the completeness
clause): `colProtocol_proverBounded`. -/
theorem colRep_efficientProverProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL := by
  sorry

/-- The `n|E|`-fold protocol is an interactive proof for `3COL` [PS10, Proposition 127.6]. -/
theorem colRep_interactiveProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : InteractiveProof (colProtocolRep Com ℓ) L3COL :=
  (colRep_efficientProverProof hC).toInteractiveProof

end TCSlib.Cryptography

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
    (ruling G3-5).

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
    24.6 (on the encodings `⟨1^n, y⟩`, which is all `Computes` constrains; gate 03a, round 2,
    R2-1) is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
    unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.
    **Erratum (2026-11-06, gate 03e round 2, finding 1, and gate 03g, finding 6; the frozen text
    above is unchanged).** Only GI is proved statistically (`gi_statZK`: `StatZK` with
    negligible δ, truncated simulator, rejection-sampled permutations). 3COL is proved
    computationally ZK (`col_zk`, by `Commitment.multiHiding`; the truncation and sampling errors
    are statistical terms inside a computational bound), its simulator stopping after `n|E|`
    attempts as the text's does. It cannot be statistical: with a perfectly binding commitment
    the real views of two colourings outside one colour-permutation orbit are statistically far
    apart, and the simulator does not see the witness.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
    question 5, ruled outside the core on 2026-10-27).

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

**As-built note (2026-11-05, gate 03l; the sketch above is unchanged).** The `pairSplitAt`
machine (`Randomized/Build/PairSplit.lean`) uses one work tape, not two: the parser stores `u`,
and the copy scan of `b` doubles each bit while the work head walks across the stored `u`. Its
buffered aligned parser is public (`Turing.PairParse`) and is shared by the `unaryMul` machine
(`Randomized/Build/UnaryMul.lean`), which stores `u` and replays it once per symbol of `v`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

**As-built erratum (2026-11-05, gate 03l, minor 2; the frozen text above is unchanged).** The
machine of `polyTimeComputable_iterateFind` (`Randomized/Build/IterateFind.lean`, with
`Randomized/Build/IterateFindHost.lean` and the public host `TuringMachine/Build/ModuleHost.lean`)
departs from steps 1–5 and 7 as follows. The frozen signatures and decisions are unchanged.
- *Step 1: the guard and the invariant.* The guard tests the **new** point:
  `stepF x w := if |g (pairSndD w)| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`. The guard
  on the old length written above does not close `Inv`: for `x = []`, `P = var` and
  `g s = true :: s`, the word `⟨[], []⟩` satisfies `Inv`, passes the guard `0 ≤ 0`, and steps to
  `⟨[], [true]⟩`, which does not. The machine's invariant is the actual-pair invariant
  `Inv x w := ∃ s, w = pairEncode x s ∧ |s| ≤ P|x|`, which, unlike `pairFstD w = x ∧ …`, excludes
  malformed words and gives the length bound `|w| ≤ 2|x| + 2 + P|x|` that the budget needs.
  (`Repetition.lean`'s `guardedStep` is the same step; its `LoopInv` is the pure invariant above,
  not the machine's.)
- *Steps 2–3: the gluing.* No transition is redirected. A release flag halts each clean-call
  module one silent step after its first positive exit, and the run is cut at its first halt
  (the clean-module contract `Turing.ModuleHost.Clean`, `clean_install`, `clean_emit`). The
  modules are padded to a common bank of tapes and run in one finite host with states
  `Fin 3 ⊕ Σ i, (M i).State` over five modules (copier, startup install `x ↦ ⟨x, x⟩`, verdict
  install, step install, payload emit): the anchor `inl 0`, the branch `inl 1` and the halt
  `inl 2`. This host is now the public clean-module host `Turing.ModuleHost.hostTM`
  (`machine-library-design.md` §14, row H14), harvested on 2026-11-05 from `ClassNP/SAT.lean`'s
  private module layer and this machine's copy of it.
- *Step 4: the startup.* The input is copied onto tape 0 by a two-state copier (`copyTM`: copy and
  turn, then rewind both heads), not by a one-state scan and `timed_rewind`.
- *Step 5: the budget.* Every request has length at most `2n + 6 + P n`, and the common budget is
  `T n = A·(2n + 7 + P n)^D` (`IterateFind.lean`), with `A` and `D` collected from the modules'
  budgets and the fuel machine.
- *Step 7.* `iterate`'s counter test is `R|x| ≤ |cnt|` (`StateLoop.IterLoop.acc`), not `lenEq`.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
carries the cost of §5.25);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

**As-built note (2026-11-06, gate 03g, finding 6; the frozen block above is unchanged).** Ruling
G3-3 changed two signatures. `InteractiveProof(Err).complete` is
`∃ B : PolyExpr, ∀ x ∈ L, ∃ y, (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧ ∀ z, uprob (…) = 1`,
and `EfficientProverProof(Err)` has the field `boundedP : ∃ B : PolyExpr, π.ProverBounded R B`
(`Protocol.ProverBounded`, `Interaction.lean`). See §5 item 8.

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
   by point tests, not formalized; gate 03a, note 14).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length. The honest
   messages are polynomially bounded in `|x|` (`Protocol.ProverBounded`, in
   `InteractiveProof(Err).complete` and the field `EfficientProverProof(Err).boundedP`): for
   Definition 119.5 the source's p.p.t. prover writes at most `t(|x|)` bits; for Definition
   116.1, whose prover is unbounded, it is a normal form (a verifier of time `t(|x|)` reads at
   most `t(|x|)` bits of each message; gate 03e round 2, finding 7). Against a cheating prover the verifier's
   work is polynomial in the message length, not in `|x|` (gate 03e, finding 1; ruling G3-3).
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI: statistical ZK with negligible δ (`gi_statZK`; truncated simulator, rejection-sampled
    permutations). 3COL: computational ZK (`col_zk`; `Commitment.multiHiding`, with the
    statistical errors of the `n|E|`-attempt simulator and of the rejection-sampled edges, colour
    pairs and colour permutations absorbed); not statistical, since with a perfectly binding
    commitment two inequivalent colourings give statistically distinct views (gate 03e round 2,
    finding 1; gate 03g, finding 6). One-iteration ZK; the `n`-fold protocols get soundness only
    (sequential composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are
    stated, but no source protocol attains them under D8/D10; `PerfectZKAbort.statZK` turns the
    abort form into statistical ZK with error `2^{-|x|}` (gate 03e, finding 2; ruling G3-4).
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
    of ch. 2–8 is vacuous by it.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least". (Lemma 50.15's "`N > 2`
    composite" is right as stated: for even `N > 2` the liars also form a proper subgroup, since
    `(−1)^{N−1} = −1`; the formal lemma restricts to odd `N` only for convenience. Corrected on gate
    03f2, F01.)
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary; p. 129 prints "If we assume that `S′` never
    outputs fail" and "`S′` fails with probability …" for `S″` (gate 03g, M2).
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).
51. Definition 121.2 read literally (`∀ z ∈ {0,1}*`, the distinguisher polynomial-time in its
    input) fails for the 3-colouring protocol 127.5 of Proposition 128.8: with `|z|` exponential,
    the distinguisher, whose input (the view) contains `z`, opens the perfectly binding
    commitments by exhaustive search, and on a graph with two proper colourings outside one
    colour-permutation orbit it separates the two real views, which the witness-blind simulator
    cannot match (protocols with exactly simulable views are not affected; gate 03e round 2,
    finding 6). So the bound `∀ Lz : PolyExpr` on `|z|`, and
    indexing the distinguisher's advice by `|x|` rather than by its input length, are necessary,
    not only convenient (gate 03e, finding 9; `ZeroKnowledge/Defs.lean`'s module docstring).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (proved: `two_mul_card_mrLiars_le`, `uprob_millerRabin_le`); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
   The one admission in this area is the optional bridge
   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== briefs/pass-shelat/inventory-ch4.md =====

# Inventory — [PS10] Chapter 4, *Knowledge* (§4.1–4.9)

Run 1 (understand & design) of the Pass–shelat Chapters 2–4 campaign. Source:
`blueprint/src/references/pass-shelat-2010-ch4.raw.md` (plus Appendix B,
`…-appendix.raw.md`, for witness relations). Results are cited as `[PS10, <page>.<counter>]`.

This file is the input of the statement-phase planners. Every item below is one Lean
declaration (or a tight cluster of declarations in one file). Items the chapter leaves
unnumbered carry page-letter ids (`Def-114.a`, `Claim-117.c`, …); campaign infrastructure
items specific to Chapter 4 carry `Inf-4.<k>` ids.

## 0. Reading guide and conventions

* **Two layers, as in the Garg campaign (plan D2).** Every protocol statement has a
  *concrete* form at one common input `x` (typed objects — graphs on `Fin n`, permutations,
  `Fin 3`-colourings; coins ranging over arbitrary finite types; all probabilities are
  `TCSlib.Cryptography.uprob` over the product of the coin types, all indistinguishability
  statements are `distAdv` bounds) and an *asymptotic* form (string common input, PPT /
  nuPPT machines of plan D3/D4, negligible functions of `|x|`). The chapter's mathematics
  lives entirely in the concrete layer; the asymptotic layer adds (i) string encodings
  (`Inf-4.1`), (ii) machine closure for the honest parties and simulators (`Inf-4.2`,
  `Inf-4.3`), (iii) the negligibility bookkeeping `2^{-n(x)}`, `e^{-n(x)}` versus `|x|`
  (`Inf-4.4`).
* **Interaction model (plan D8).** An interactive machine is a *next-message function*
  `(x, z, r, received) ↦ message` plus an output function of the final view; a protocol is a
  pair with a fixed polynomial number of rounds; executions are obtained by iterating the two
  functions; `view_A = (x, z_A, r_A, M_A)`, `transcript = (M_A, M_B)`, `out_A = A.out(view_A)`.
  No tapes, states or idle transitions are modelled (Deviation, recorded once in
  `Interaction.lean`).
* **Simulators are strict PPT (plan D8).** The GI simulator (123.4) is truncated at
  `n` attempts (D8; the text restarts until success) and the 3COL simulator (128.7) stops after
  `n·|E|` attempts as the text's does (Algorithm 128.7, steps 4–5; gate 03g, finding 5); both
  output `⊥` on failure; the resulting theorems
  are *statistical* zero-knowledge with error `2^{-n}` (GI) and a computational bound with an
  additional `e^{-n}` term (3COL). The perfect-simulation lemma is proved as stated
  (conditioned on success). Expected polynomial time (Def-121.a) and the untruncated loop
  (Claim-123.a) are deferred.
* **Scope.** `core` = mandatory content of the plan; `optional` = feasible, nice to have;
  `deferred` = cited without proof in the text and used by nothing downstream, or outside
  the frozen model (expected PPT, §7.2.1 sequential composition, Shamir).
* **Difficulty** 1 (trivial) … 5 (research-level or large machine-building fill).

### Dependencies on the Chapter 2/3 inventories (ids as used there)

Def-23.4 (PPT), Def-23.5 (running time, worst case over coins), Def-24.6 (computes with
probability 1), Def-24.7 (private-key encryption scheme), Def-26.8 (nuPPT, advice form),
Def-27.2 (negligible), Def-27.3 (strong OWF; "one-way permutation" = length-preserving
bijective OWF, single-function reading as in Thm 79.4), Def-55.1 (OWP collection — *not* the
form used in §4.7), Def-69.3/69.4 (ensembles, `≈`), Lem-71.5 (closure under efficient
operations), Lem-71.6 (hybrid lemma), Lem-73.8 (prediction lemma), Def-78.3 (hard-core
predicate), Thm-87.3 (Goldreich–Levin, for the unconditional form of Thm-126.4), Def-91.1
(single-message secure encryption), Def-93.1 (multi-message security, the model for
Claim-126.a), Def-102.1/102.2 (PKE), Thm-104.4 (whose proof is reused verbatim for
Claim-127.c).

### Design questions the panel must settle (DQ)

* **DQ1 — exact uniform sampling of `S_n`, of an edge of `E`, of `S_3`.** With a worst-case
  bounded coin *string* (D3) a PPT cannot sample `σ ∈ S_n` exactly uniformly (`n! ∤ 2^ℓ`),
  nor an edge of `E` when `|E|` is not a power of two. Options: (A) keep D3 and prove
  near-uniform samplers with statistical error `≤ 2^{-n}` at the machine level (every bound
  of the chapter gains a `2^{-n}` term; a large machine-building task); (B) let honest
  strategies and simulators draw their coins uniformly from a *finite type* `ρ n` whose
  elements have polynomial-length encodings, the next-message machine reading the encoding
  (D3 is the special case `ρ n = Fin ℓ → Bool`). Adversaries (`V*`, `P*`, `D`) keep D3/D4.
  Recommendation: (B), recorded as a Deviation; the concrete layer is written over arbitrary
  finite coin types either way, so the choice only affects `Inf-4.2`.
* **DQ2 — typed common inputs.** Concrete-layer protocols take typed common inputs
  (`SimpleGraph (Fin n) × SimpleGraph (Fin n)`, `SimpleGraph (Fin n)`); the asymptotic
  definitions (116.1, 121.1, 121.2) are over `List Bool` and are instantiated through the
  adjacency-matrix encoding and total decoding with defaults (`Inf-4.1`).
* **DQ3 — Theorem 124.1 needs Levin (witness-preserving) reductions**, which neither
  the text's Appendix B nor the repository (`Complexity.NPHard` is Karp-only;
  `SATtoColor.SATtoColorReduction` is graph-level, with the colouring witness `private`)
  provides. Core form: ZK for every `(L, R_L)` that Levin-reduces to 3COL
  (Thm-124.1 + Claim-124.d); the "every language in NP" form takes string-level Levin
  NP-hardness of 3COL as a hypothesis (Claim-124.b/124.c deferred).
* **DQ4 — commitment security parameter.** Def 126.3 infers `n` from `|v|`; Protocol 127.5
  commits to 2-bit colours. The formal `Com` takes `n` explicitly and the colour is padded to
  `n` bits (Deviation; see Prot-127.5).
* **DQ5 — sequential repetition.** The text proves ZK for *one* iteration and defers the
  `n`-fold / `n|E|`-fold protocols to §7.2.1 (Claim-123.c, outside Chapters 2–4). Core
  theorems are stated for the single-iteration protocols (soundness error `1/2` resp.
  `1 − 1/|E|`) *and* for the repeated protocols' completeness/soundness; the repeated
  protocols' ZK is stated with Claim-123.c as an explicit hypothesis or left sorried under a
  sketch (deferred).

## 1. Existing Lean the chapter builds on (verified by `lake env lean` on 2026-10-27)

| Declaration (fully qualified) | File | Use in Chapter 4 |
| --- | --- | --- |
| `TCSlib.Cryptography.uprob`, `uexp`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_eq_card_filter` | `TCSlib/Cryptography/Foundations/Probability.lean` | all probability statements |
| `TCSlib.Cryptography.abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `half_le_uprob_good` | same | hybrids in 112.2(ii), 126.a, 127.d, 129.d |
| `TCSlib.Cryptography.acceptProb`, `distAdv`, `predProb`, `acceptProb_comp_equiv`, `distAdv_le_statDist` | `Foundations/Experiments.lean` | ZK/hiding advantages; statistical ZK ⇒ computational |
| `TCSlib.Cryptography.Negligible`, `.add`, `.mul_pow`, `.const_mul`, `.mono`, `negligible_two_pow_neg`, `not_negligible_iff` | `Foundations/Negligible.lean` | every asymptotic statement |
| `TCSlib.Cryptography.uprob_eq_of_equiv`, `acceptProb_fst`, `acceptProb_snd`, `acceptProb_bind`, `acceptProb_update`, `pushSampler`, `sunglassRed`, `distAdv_sunglassRed`, `distAdv_comp`, `mixDist`, `distAdv_mixDist_eq`, `copies`, `multicopyRed`, `exists_multicopyRed_ge`, `distAdv_multicopyAvgRed` | `Pseudorandom/Indistinguishability.lean` | closure (Lem-71.5) and multi-copy hybrids (Claim-126.a, 127.d, 129.d) |
| `TCSlib.Cryptography.owpGen`, `owpGenNot`, `owpPair`, `owpPredictor`, `uprob_bool_prod`, `predProb_owpPredictor_false`, `predProb_owpPredictor_true`, `exists_owpPredictor` | `Pseudorandom/GeneratorFromPermutation.lean` | **exact** concrete content of commitment hiding (Claim-127.c) with `β := Unit` |
| `TCSlib.Cryptography.PushesUniform`, `pushesUniform_equiv`, `uprob_eq_one_of_forall`, `forall_of_uprob_eq_one`, `uprob_prod_and` | `HardcoreBit/Basic.lean` | uniform-permutation invariance (Lem-119.a), probability-1 completeness |
| `TCSlib.Cryptography.OneWay.uprob_pi_forall`, `uprob_eq_one_div_card`, `uprob_and_le_mul`, `uprob_congr` | `OneWayFunctions/Basic.lean` | counting lemmas Lem-119.c, Lem-127.g |
| `TCSlib.InformationTheory.statDist`, `statDist_triangle`, `FinDist.map`, `FinDist.uniform` | `TCSlib/InformationTheory/{StatisticalDistance,FinDist}.lean` | statistical ZK (Def-122.a, Thm-122.3.trunc, Claim-129.c) |
| `Schnorr.Transcript`, `honest`, `simulate`, `reindex`, `schnorr_completeness`, `schnorr_soundness`, `schnorr_hvzk` | `TCSlib/Cryptography/SchnorrProtocol.lean` | template (not reusable code): 3-move sigma protocol, HVZK by bijective reindexing = Thm-122.3.hv |
| `Complexity.NP`, `Complexity.mem_NP_iff_exists_length_le`, `Complexity.P_subset_NP` | `TCSlib/Complexity/ClassNP/NP.lean` | Def-191.11, Claim-117.c, Claim-118.b |
| `Complexity.P`, `Complexity.mem_P_iff`, `Complexity.DTIME` | `ClassP/{P,DTIME}.lean` | verifier predicates in `P` |
| `Complexity.PolyTimeReducible` (`≤ₚ`), `NPHard`, `NPComplete`, `mem_P_of_polyTimeReducible` | `ClassNP/Reductions.lean` | Karp reductions (Def-124.a extends to Levin) |
| `Complexity.PolyTimeComputable`, `.comp`, `.pairEncode`, `polyTimeComputable_ite`, `pairFstD`, `pairSndD`, `polyTimeComputable_lenEq` | `ClassNP/{PolyTime,PolyTimePairing}.lean` | machine-level PPT-ness of honest strategies (Inf-4.2) |
| `Complexity.SAT3`, `Complexity.SAT3_NPComplete` | `ClassNP/SAT.lean`, `CookLevin/Hardness.lean` | Claim-124.b |
| `Complexity.coNP` | `ClassNP/CoNP.lean` | Claim-118.c |
| `SATtoColor.Is3Colorable`, `ReductionGraph`, `SATtoColorReduction`, `SATtoColorCompleteness`, `Sat3` (`sat3Coloring` is `private`) | `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean` | Def-124.f, Claim-124.b/c |
| `Turing.FinTM`, `FinTM.ComputesInTime`, `ComputesFunInTime` | `TCSlib/Complexity/TuringMachine/Finite.lean` | machine layer |
| `Turing.pairEncode`, `pairDecode`, `pairDecode_pairEncode` | `TuringMachine/Encoding.lean` | encodings of views/messages (Inf-4.1) |
| `Turing.FinTM.DecidesWithAdviceInTime`, `DTIMEAdvice`, `PAdvicePoly` | `CircuitComplexity/Advice.lean` | nuPPT distinguishers (D4) |
| `Turing.FinTM.exists_loopFindTM`, `exists_loopTM`, `exists_emitLoopTM` | `TuringMachine/Build/Loop.lean` | truncated simulators as machines (Inf-4.3, via plan's `Randomized/Repetition.lean`) |
| Mathlib `SimpleGraph.Iso` (`≃g`), `SimpleGraph.Iso.map`, `SimpleGraph.map`, `map_map`, `map_id`, `map_symm`, `comap_symm`, `map_adj` | `Mathlib/Combinatorics/SimpleGraph/Maps.lean` | `σ(G)`, isomorphism (Def-117.e) |
| Mathlib `SimpleGraph.Coloring`, `Colorable`, `Coloring.mk`, `Coloring.valid`, `instance Fintype (Coloring G α)` | `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` | 3COL (Def-124.f) |
| Mathlib `SimpleGraph.edgeFinset`, `mem_edgeFinset`, `fintypeEdgeSet`, `instance Fintype (SimpleGraph V)` (Basic.lean:110) | `Mathlib/Combinatorics/SimpleGraph/{Finite,Basic}.lean` | random edge of `E`, finiteness of graphs |
| Mathlib `Equiv.Perm`, `Fintype (Perm α)` (`Equiv.instFintype`/`fintypePerm`), `Fintype.card_perm`, `Equiv.mulRight` | `Mathlib/Data/Fintype/Perm.lean`, `Mathlib/Algebra/Group/…` | uniform permutations, `S_3` pair lemma |
| Mathlib `Real.add_one_le_exp`, `Real.one_sub_div_pow_le_exp_neg` | `Mathlib/Analysis/Complex/Exponential.lean` | Claim-125.a |

Nothing in the repository formalizes interaction, views, simulators, commitments, graph
isomorphism as a language, or the `3COL` language; `TCSlib/Cryptography/MPC/BGW/Privacy.lean`
(`linear_perfectPrivacy`: a bijection of the dealer's coins fixing a coalition's view) is the
closest "perfect simulation by reindexing" precedent and is a model for Claim-123.b.

## 2. Inventory table

Columns: id · kind · title · scope · difficulty · proposed file (under
`TCSlib/Cryptography/ZeroKnowledge/` unless absolute) · existing Lean (short) · depends on.

| id | kind | title | scope | diff | file | existing Lean | depends on |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Def-111.1 | Definition | Zero-knowledge (private-key) encryption | core | 2 | Encryption.lean | `distAdv`, `acceptProb`, `Negligible` | Def-24.7, Def-23.4, Def-26.8, Def-27.2 |
| Def-111.a | Definition | Perfect zero-knowledge encryption | optional | 1 | Encryption.lean | `FinDist.map`, `statDist` | Def-111.1 |
| Def-111.b | Definition | Zero-knowledge public-key encryption | optional | 2 | Encryption.lean | `distAdv` | Def-102.1 |
| Thm-112.2 | Theorem | Secure ⇔ zero-knowledge (private key) | core | 2 | Encryption.lean | — | Thm-112.2.i, Thm-112.2.ii |
| Thm-112.2.i | Theorem | Security ⇒ zero-knowledge | core | 2 | Encryption.lean | `distAdv` (sampler equality), PPT closure | Def-91.1, Def-111.1, Def-24.6 |
| Thm-112.2.ii | Theorem | Zero-knowledge ⇒ security | core | 1 | Encryption.lean | `abs_sub_le`, `Negligible.const_mul` | Def-91.1, Def-111.1 |
| Claim-112.a | Claim | The equivalence for public-key encryption | optional | 2 | Encryption.lean | as 112.2 | Def-102.2, Def-111.b |
| Claim-112.b | Claim | Perfect ZK encryption ⇔ perfect secrecy | optional | 1 | Encryption.lean | `FinDist.map` | Def-111.a |
| Def-114.a | Definition | Interactive machine as a next-message strategy | core | 2 | Interaction.lean | — (new model) | Def-23.4 |
| Def-114.b | Definition | Protocol (pair of strategies, round order, round bound) | core | 1 | Interaction.lean | — | Def-114.a |
| Def-115.a | Definition | Execution `A_{r1}(x,z1) ↔ B_{r2}(x,z2)` | core | 2 | Interaction.lean | — | Def-114.b |
| Def-115.b | Definition | Views `view_A`, `view_B`, joint view | core | 1 | Interaction.lean | — | Def-115.a |
| Def-115.c | Definition | Transcript | core | 1 | Interaction.lean | — | Def-115.a |
| Def-115.d | Definition | Outputs `out_X(e)`, `out(v)` | core | 1 | Interaction.lean | — | Def-115.b |
| Def-116.a | Definition | Random executions (samplers from the coin product) | core | 1 | Interaction.lean | `uprob`, `uprob_prod`, `acceptProb` | Def-115.a |
| Def-116.b | Definition | Time complexity of an ITM; PPT strategies | core | 3 | Interaction.lean | plan `Randomized/PPT.lean`, `pairEncode`, `FinTM.ComputesInTime` | Def-23.5, Def-114.a |
| Def-116.1 | Definition | Interactive proof system | core | 2 | InteractiveProofs.lean | `uprob`, `Negligible` | Def-116.b, Def-115.d, Def-116.a |
| Def-117.a | Definition | Soundness error `s(n)`; constant-error proofs | core | 1 | InteractiveProofs.lean | — | Def-116.1 |
| Def-117.b | Definition | The class `IP` | optional | 1 | InteractiveProofs.lean | `Language Bool` | Def-116.1 |
| Claim-117.c | Claim | `NP ⊆ IP` (send the certificate) | optional | 3 | InteractiveProofs.lean | `Complexity.NP`, `mem_P_iff` | Def-116.1, Def-191.11, Inf-4.2 |
| Claim-117.d | Claim | `IP = PSPACE` (Shamir, cited) | deferred | 5 | — | — | Def-117.b |
| Def-117.e | Definition | Graphs on `Fin n`, `σ(G)`, isomorphism via permutations | core | 2 | GraphIsomorphism.lean | `SimpleGraph.map`, `Iso.map`, `map_map`, `map_id`, `map_symm`, `Equiv.Perm` | — |
| Def-118.a | Definition | `L_iso`, `L_niso`, witness relation `R_iso` | core | 2 | GraphIsomorphism.lean | `SimpleGraph.Iso` | Def-117.e, Inf-4.1 |
| Claim-118.b | Claim | `L_iso ∈ NP` (string level) | optional | 4 | GraphIsomorphism.lean | `Complexity.NP`, `mem_NP_iff_exists_length_le` | Def-118.a, Inf-4.1 |
| Claim-118.c | Claim | `L_niso ∈ coNP` | deferred | 4 | GraphIsomorphism.lean | `Complexity.coNP` | Claim-118.b |
| Prot-118.3 | Protocol | Graph non-isomorphism protocol (single and `n`-fold) | core | 2 | GraphIsomorphism.lean | `Equiv.Perm`, `Fintype (Perm α)` | Def-114.b, Def-117.e |
| Lem-119.a | Lemma | Uniformly permuted isomorphic graphs are identically distributed | core | 2 | GraphIsomorphism.lean | `uprob_comp_equiv`, `pushesUniform_equiv`, `Equiv.mulRight` | Def-117.e |
| Lem-119.b | Lemma | `n`-fold GNI soundness `≤ 2^{-n}` against adaptive provers | core | 3 | GraphIsomorphism.lean | `uprob_prod`, `uprob_eq_of_equiv` | Lem-119.a, Lem-119.c |
| Lem-119.c | Lemma | Adaptive guessing lemma `Pr[∀i, b_i = g_i(b_{<i}, w)] = 2^{-n}` | core | 2 | GraphIsomorphism.lean | `uprob_eq_one_div_card`, `uprob_prod` | — |
| Lem-119.d | Lemma | GNI completeness (unbounded prover, probability 1) | core | 2 | GraphIsomorphism.lean | `uprob_eq_one_of_forall` | Prot-118.3, Lem-120.b |
| Prop-118.4 | Proposition | Protocol 118.3 is an interactive proof for `L_niso` | core | 3 | GraphIsomorphism.lean | `negligible_two_pow_neg` | Lem-119.b, Lem-119.d, Def-116.1, Inf-4.2, Inf-4.4 |
| Def-119.5 | Definition | Interactive proof with efficient prover w.r.t. `R_L` | core | 2 | InteractiveProofs.lean | — | Def-116.1, Def-191.11 |
| Def-119.e | Definition | Interactive argument (nuPPT cheating provers) | optional | 2 | InteractiveProofs.lean | `DecidesWithAdviceInTime` (D4) | Def-116.1, Def-26.8 |
| Claim-119.f | Claim | Poly-time GNI prover would put `L_niso` in NP (informal) | deferred | 4 | — | — | Claim-118.c |
| Prot-120.6 | Protocol | Graph isomorphism protocol (single and `n`-fold) | core | 2 | GraphIsomorphism.lean | `Equiv.Perm`, `SimpleGraph.map` | Def-114.b, Def-118.a |
| Lem-120.a | Lemma | Completeness algebra `π(G0) = H`, `(π∘σ⁻¹)(G1) = H` | core | 1 | GraphIsomorphism.lean | `map_map`, `map_symm` | Def-117.e |
| Lem-120.b | Lemma | A graph is isomorphic to at most one of two non-isomorphic graphs | core | 1 | GraphIsomorphism.lean | `map_map` | Def-117.e |
| Lem-120.c | Lemma | Single-iteration GI soundness `≤ 1/2` | core | 2 | GraphIsomorphism.lean | `uprob_prod`, `uprob_bool_prod` | Lem-120.b |
| Lem-120.d | Lemma | `n`-fold GI soundness `≤ 2^{-n}` against adaptive provers | core | 3 | GraphIsomorphism.lean | `uprob_prod` | Lem-119.c, Lem-120.b |
| Prop-120.7 | Proposition | Protocol 120.6 is an interactive proof for `L_iso` with efficient prover | core | 3 | GraphIsomorphism.lean | `negligible_two_pow_neg` | Lem-120.a, Lem-120.d, Def-119.5, Inf-4.2, Inf-4.4 |
| Def-121.1 | Definition | Honest-verifier zero-knowledge | core | 2 | Defs.lean | `distAdv`, `Negligible` | Def-119.5, Def-115.b, Def-26.8 |
| Def-121.2 | Definition | Zero-knowledge (every PPT `V*`) | core | 2 | Defs.lean | `distAdv`, `Negligible` | Def-121.1, Def-116.b |
| Def-121.a | Definition | Expected polynomial time | deferred | 4 | — | `uexp` | Def-23.5 |
| Def-122.a | Definition | Perfect and statistical zero-knowledge | core | 2 | Defs.lean | `statDist`, `distAdv_le_statDist` | Def-121.2 |
| Claim-122.b | Claim | View-based ZK ⇔ output-based ZK (exercise) | optional | 3 | Defs.lean | `distAdv_sunglassRed` | Def-121.2, Lem-71.5 |
| Claim-122.c | Claim | ZK against PPT `V*` with auxiliary input covers nuPPT `V*` | deferred | 3 | — | — | Def-121.2, Def-26.8 |
| Thm-122.3 | Theorem | Protocol 120.6 is a (statistical, single-iteration) ZK proof for `L_iso` | core | 4 | GraphIsomorphismZK.lean | `distAdv_le_statDist`, `negligible_two_pow_neg` | Prop-120.7, Thm-122.3.trunc, Claim-123.d, Claim-123.c |
| Thm-122.3.hv | Theorem | Honest-verifier perfect ZK of one GI iteration by reindexing | core | 2 | GraphIsomorphismZK.lean | `Schnorr.schnorr_hvzk` (template), `acceptProb_comp_equiv` | Prot-120.6, Lem-120.a, Def-121.1 |
| Thm-122.3.trunc | Theorem | Truncated simulator: `Pr[⊥] = 2^{-n}`, `statDist ≤ 2^{-n}` | core | 4 | GraphIsomorphismZK.lean | `uprob_prod`, `statDist`, `distAdv_le_statDist` | Alg-123.4, Lem-123.5, Claim-123.b |
| Alg-123.4 | Algorithm | Simulator for GI (truncated at `n` attempts) | core | 3 | GraphIsomorphismZK.lean | `Fintype (Perm α)` | Prot-120.6, Def-114.a |
| Lem-123.5 | Lemma | `H ~ π(G0)` independent of `b'`; `Pr[b = b'] = 1/2` | core | 2 | GraphIsomorphismZK.lean | `uprob_bool_prod`, `uprob_prod`, `uprob_comp_equiv` | Lem-119.a, Alg-123.4 |
| Claim-123.a | Claim | Untruncated simulator has expected 2 trials | deferred | 3 | — | `uexp` | Def-121.a, Lem-123.5 |
| Claim-123.b | Claim | Perfect simulation conditioned on success | core | 4 | GraphIsomorphismZK.lean | `uprob_eq_of_equiv`, BGW `linear_perfectPrivacy` (precedent) | Lem-123.5, Lem-120.a |
| Claim-123.c | Claim | Sequential repetition preserves ZK (§7.2.1) | deferred | 5 | — | — | Def-121.2 |
| Claim-123.d | Claim | Truncated GI simulator is strict PPT | core | 4 | GraphIsomorphismZK.lean | `exists_loopFindTM` via `Randomized/Repetition` | Inf-4.3, Alg-123.4 |
| Thm-124.1 | Theorem | OWP ⇒ ZK proofs for NP (Levin-reducible form) | core | 4 | NP.lean | `Complexity.NP`, `PolyTimeReducible` | Thm-126.4, Prop-127.6, Claim-124.d, Def-124.a |
| Def-124.a | Definition | Levin (witness-preserving) reduction | core | 2 | NP.lean | `PolyTimeReducible`, `PolyTimeComputable` | Def-191.11 |
| Claim-124.b | Claim | 3COL is NP-complete at the string level | deferred | 5 | NP.lean | `SAT3_NPComplete`, `SATtoColorReduction` | Inf-4.1 |
| Claim-124.c | Claim | Witness transformation 3SAT → 3COL (`sat3Coloring`) | deferred | 4 | NP.lean | `SATtoColorCompleteness` (private `sat3Coloring`) | Claim-124.b |
| Claim-124.d | Claim | ZK proofs are preserved under Levin reductions | core | 3 | NP.lean | — | Def-124.a, Def-121.2, Def-119.5 |
| Claim-124.e | Claim | One-way functions suffice (cited) | deferred | 5 | — | — | Thm-124.1 |
| Def-124.f | Definition | The language 3COL and its witness relation (typed) | core | 1 | ThreeColoring.lean | `SimpleGraph.Colorable`, `Coloring`, `SATtoColor.Is3Colorable` | — |
| Claim-125.a | Claim | `(1 − 1/m)^{n·m} ≤ e^{-n}` (soundness after `n·|E|` rounds) | core | 1 | ThreeColoring.lean | `Real.one_sub_div_pow_le_exp_neg`, `Real.add_one_le_exp` | — |
| Def-126.3 | Definition | Commitment scheme (binding, hiding) | core | 2 | Commitment.lean | `distAdv`, `Negligible`, `PolyTimeComputable` | Def-26.8, Def-27.2 |
| Claim-126.a | Claim | Every commitment scheme is multi-value hiding | core | 3 | Commitment.lean | `exists_hybrid_gap`, `mixDist`, `exists_multicopyRed_ge` (generalize) | Def-126.3, Lem-71.6 |
| Thm-126.4 | Theorem | OWP (with hard-core predicate) ⇒ commitment schemes | core | 3 | Commitment.lean | `exists_owpPredictor` | Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d, Def-78.3, Thm-87.3 |
| Alg-127.a | Construction | `Com(b,r) = (f(r), b ⊕ h(r))`; bitwise `n`-bit scheme | core | 1 | Commitment.lean | `owpGen`, `owpGenNot` (`β := Unit`) | Def-27.3, Def-78.3 |
| Claim-127.b | Claim | Binding of Alg-127.a | core | 1 | Commitment.lean | `Equiv.injective` | Alg-127.a |
| Claim-127.c | Claim | Hiding of the single-bit scheme = predictor reduction | core | 2 | Commitment.lean | `predProb_owpPredictor_false/true`, `exists_owpPredictor` | Alg-127.a, Def-78.3, Lem-73.8 |
| Claim-127.d | Claim | Bitwise scheme hiding by hybrid ("show this!") | core | 3 | Commitment.lean | `exists_hybrid_gap`, `acceptProb_update`, `Negligible.mul_pow` | Claim-127.c, Lem-71.6 |
| Prot-127.5 | Protocol | ZK protocol for 3-colouring (single and `n·|E|`-fold) | core | 3 | ThreeColoring.lean | `edgeFinset`, `Fintype (Perm (Fin 3))` | Def-126.3, Def-124.f, Def-114.b |
| Claim-127.e | Claim | Completeness of Protocol 127.5 | core | 1 | ThreeColoring.lean | `Coloring.valid`, `uprob_eq_one_of_forall` | Prot-127.5 |
| Lem-127.f | Lemma | Committed colouring from binding; a bad edge exists | core | 2 | ThreeColoring.lean | — | Def-126.3, Def-124.f |
| Lem-127.g | Lemma | Adaptive sequential soundness with escape probability `1/m` | core | 3 | ThreeColoring.lean | `uprob_prod`, `uprob_and_le_mul` | Lem-119.c (model) |
| Claim-127.h | Claim | Soundness of Protocol 127.5: `≤ (1−1/|E|)^{n|E|} ≤ e^{-n}` | core | 3 | ThreeColoring.lean | — | Lem-127.f, Lem-127.g, Claim-125.a |
| Prop-127.6 | Proposition | Protocol 127.5 is a ZK proof for 3COL | core | 4 | ThreeColoring.lean | — | Claim-127.e, Claim-127.h, Prop-128.8, Inf-4.2, Inf-4.4, Claim-123.c |
| Alg-128.7 | Algorithm | Simulator for 3-colouring (truncated at `n·|E|` attempts) | core | 3 | ThreeColoring.lean | — | Prot-127.5, Def-114.a |
| Claim-128.a | Claim | The 3COL simulator is strict PPT | core | 4 | ThreeColoring.lean | `exists_loopFindTM` via `Randomized/Repetition` | Inf-4.3, Alg-128.7 |
| Prop-128.8 | Proposition | ZK of the 3COL simulator (computational) | core | 5 | ThreeColoring.lean | `abs_sub_le`, `distAdv_le_statDist`, `Negligible.add` | Claim-129.a, Claim-129.c, Claim-129.d |
| Claim-129.a | Claim | `S ≡ S'` (random distinct pair = permuted witness colours) | core | 2 | ThreeColoring.lean | `uprob_comp_equiv` | Lem-129.b, Alg-128.7 |
| Lem-129.b | Lemma | `π ↦ (π a, π b)` is a bijection `S_3 ≃ {(u,v) ∣ u ≠ v}` | core | 2 | ThreeColoring.lean | `Fintype.card_perm`, `decide` | — |
| Claim-129.c | Claim | `S''` fails w.p. `(1−1/|E|)^{n|E|}` and is perfect given success | core | 4 | ThreeColoring.lean | `uprob_prod`, `statDist` | Alg-128.7, Claim-123.b (model) |
| Claim-129.d | Claim | `S' ≈ S''` by hybrids over attempts and multi-value hiding | core | 5 | ThreeColoring.lean | `exists_hybrid_gap`, `distAdv_sunglassRed`, `mixDist`, `Negligible.mul_pow` | Claim-126.a, Lem-71.5, Lem-71.6 |
| Def-191.10 | Definition | `DP` (deterministic polynomial time) | optional | 1 | `TCSlib/Complexity/ClassP/P.lean` (exists) | `Complexity.P` | — |
| Def-191.11 | Definition | NP via witness relations, `R_L(x)` | core | 1 | InteractiveProofs.lean (typed) / `ClassNP/NP.lean` (exists) | `Complexity.NP`, `mem_NP_iff_exists_length_le` | — |
| Def-192.12 | Definition | `BPP` | optional | 2 | plan `Randomized/PPT.lean` | — | Def-23.4 |
| Inf-4.1 | Infrastructure | String encodings of graphs, permutations, colourings, messages, views | core | 4 | Encoding.lean (new) | `pairEncode`, `pairFstD`, `PolyTimeComputable.pairEncode` | — |
| Inf-4.2 | Infrastructure | Machine-level PPT-ness of honest parties; sampling (DQ1) | core | 5/3 | Encoding.lean + protocol files | `PolyTimeComputable.*`, `polyTimeComputable_ite` | Inf-4.1, Def-116.b |
| Inf-4.3 | Infrastructure | Restart loops with a bounded number of attempts as strict PPT | core | 4 | plan `TCSlib/Complexity/Randomized/Repetition.lean` | `exists_loopFindTM` | Def-116.b |
| Inf-4.4 | Infrastructure | `2^{-n(x)}`, `e^{-n(x)}` negligible in `|x|` when `n(x) ≥ √(|x|/C)` | core | 2 | Defs.lean | `negligible_two_pow_neg`, `Negligible.mono` | — |

## 3. Statements, reuse notes, text issues (one entry per item)

### §4.2 Zero-knowledge encryption — `ZeroKnowledge/Encryption.lean`

**Def-111.1 (ZK encryption).** A private-key scheme `(Gen, Enc, Dec)` [Def-24.7] is
zero-knowledge if ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `n` ∀ `m ∈ {0,1}^n`:
`|Pr[k ← Gen(1^n); c ← Enc_k(m) : D(c) = 1] − Pr[c ← S(1^n) : D(c) = 1]| ≤ ε(n)`.
Concrete layer at `n`: samplers `encS n m : ρ_G n × ρ_E n → C n`, `S n : ρ_S n → C n`,
bound `distAdv (encS n m) (S n) (D n) ≤ ε n`. *Reuse:* `distAdv` is exactly the
quantity; the asymptotic wrapper quantifies `S` over PPT samplers and `D` over nuPPT
distinguishers of the ensemble layer. *Note:* the message `m` is fixed per `n` (no
adversarial message ensemble beyond "∀ m"); `S` gets `1^n` only.

**Def-111.a (perfect ZK encryption).** As Def-111.1 with the two distributions identical:
`FinDist.map (encS n m) uniform = FinDist.map (S n) uniform` for all `n, m` (equivalently
`distAdv … D = 0` for every `D`, even unbounded).

**Def-111.b (ZK PKE).** `(Gen, Enc, Dec)` [Def-102.1] is ZK if ∃ PPT `S` ∀ nuPPT `D` ∃ negl
`ε` ∀ `n`, `m ∈ {0,1}^n`: `D` distinguishes `{(pk,sk) ← Gen(1^n) : (pk, Enc_pk(m))}` and
`{(pk,sk) ← Gen(1^n) : (pk, S(pk, 1^n))}` with advantage `≤ ε(n)`. Note the simulator is
given `pk` and the distinguisher sees `pk`.

**Thm-112.2.** Hypotheses: `Gen`, `Enc` PPT; a deterministic polynomial-time `M` with
`M(1^n) ∈ {0,1}^n` for every `n`. Conclusion: Def-91.1 ⇔ Def-111.1. Split:

* **Thm-112.2.i (secure ⇒ ZK).** Take `S(1^n) := Enc_k(M(1^n))` with `k ← Gen(1^n)`,
  coins `(g, e)`. For every `D`, `n`, `m`: the sampler of `S(1^n)` *is* the sampler of
  `Enc_k(M(1^n))`, so `distAdv (encS n m) (S n) D = distAdv (encS n m) (encS n (M n)) D ≤ ε_D(n)`
  by Def-91.1 with `m0 := m`, `m1 := M(1^n)`. Concrete content: definitional equality of
  samplers. Asymptotic bridge: `S` is PPT by closure (composition of `M`, `Gen`, `Enc`;
  plan `Randomized/Closure.lean`). *Text issue:* the proof by contradiction via "infinitely
  many `n`" is unnecessary; also `M(1^n)` must be deterministic for the sampler identity
  (a randomized `M` would still work via averaging over its coins).
* **Thm-112.2.ii (ZK ⇒ secure).** For all `D`, `n`, `m1`, `m2`:
  `distAdv (encS n m1) (encS n m2) D ≤ distAdv (encS n m1) (S n) D + distAdv (S n) (encS n m2) D ≤ 2 ε(n)`
  (triangle inequality `abs_sub_le`, then `Negligible.const_mul`). The text's "hybrid
  lemma with `1/(2p(n))`" is this two-step chain.

**Claim-112.a.** The same equivalence for PKE (Def-102.2 ⇔ Def-111.b) with
`S(pk, 1^n) := Enc_pk(M(1^n))`; identical proof (the point: encryption under `pk` is
publicly samplable). Optional.

**Claim-112.b.** Perfect ZK encryption ⇔ perfect secrecy (`Enc_k(m) ≡ Enc_k(m')` for all
`m, m'` at every `n`): `S := Enc_k(m_0)` for the fixed message `m_0 = M(1^n)`, both
directions are rewriting of distribution equalities. Perfect secrecy is a Chapter 1 notion;
state the concrete form only. Optional.

### §4.4 Interactive protocols — `ZeroKnowledge/Interaction.lean`

**Def-114.a (ITM as a strategy).** Concrete form, parametrized by a common-input type `X`,
auxiliary-input type `Z`, a finite coin type `ρ`, and a message type `Msg`:
`next : X → Z → ρ → List Msg → Msg` (the message sent after having *received* the listed
messages) and `out : X → Z → ρ → List Msg → Out`. String form: `X = Z = Msg = Out = List Bool`,
`ρ = Fin ℓ → Bool`. Deviation (D8): no tapes/states; "entering the idle state" is returning
from `next`; halting is handled by the protocol's round bound. The honest prover's witness
is its auxiliary input `z`.

**Def-114.b (protocol).** `Protocol A B := (A : Strategy …, B : Strategy …, first : Bool,
rounds : ℕ)`; in round `i` the active party is `A` iff `i` has the parity of `first`. All
protocols of the chapter have fixed round counts (GNI: 2 rounds per iteration, `V` first;
GI and 3COL: 3 rounds per iteration, `P` first).

**Def-115.a (execution).** For `x, z1, z2, r1, r2`, the pair
`((x, z1, r1, M_A), (x, z2, r2, M_B))` where `M_A` (resp. `M_B`) is the list of messages
received by `A` (resp. `B`), defined by structural recursion on the round index:
the sender's message in round `i` is its `next` applied to its received messages so far.
Notation `A_{r1}(x,z1) ↔ B_{r2}(x,z2)`. Lean: `exec P x z1 z2 r1 r2 : View × View`,
with `View := X × Z × ρ × List Msg` (typed per party).

**Def-115.b (views).** `viewA := (exec …).1`, `viewB := (exec …).2`; the execution itself is
the joint view.

**Def-115.c (transcript).** `(M_A, M_B)` of an execution (projection).

**Def-115.d (outputs).** `out_X(e) := X.out (view_X e)`; `out(v) := X.out v` for a view `v`
of `X`. For verifiers `Out = Bool` (accept).

**Def-116.a (random executions).** The distribution `A(x,z1) ↔ B(x,z2)` is the sampler
`(r1, r2) ↦ exec … r1 r2` on the uniform product `ρ_A × ρ_B`; `view`, `out` distributions
are its post-compositions. Plugs directly into `uprob`, `acceptProb`, `distAdv`
(`uprob_prod` for conditioning on one party's coins). No new content.

**Def-116.b (time complexity, PPT strategy).** `A` has time complexity `t` if for every
`B`, `x`, `z_a`, `z_b` and all coins, `A(x, z_a)` halts within `t(|x|)` steps in the
interaction. Formal: a strategy is PPT if there are `C, c, R` and a `FinTM Bool` computing
`next` (and `out`) on `pairEncode x (pairEncode z (pairEncode (enc r) (encodeList received)))`
within `C·(|x|+1)^c` steps *for every* `z`, `r`, `received` (bound in `|x|` only, as in the
text; the machine cannot read more than `C(|x|+1)^c` bits of `z`), coins of length
`C_r·(|x|+1)^{c_r}` (or a typed coin space per DQ1), and at most `R(|x|)` rounds. Deviation:
per-message bound instead of a total bound (total `≤ R·t`). Depends on the frozen
`Randomized/PPT.lean` signatures.

### §4.5 Interactive proofs — `ZeroKnowledge/InteractiveProofs.lean`, `GraphIsomorphism.lean`

**Def-116.1 (interactive proof).** `(P, V)` is an interactive proof system for `L` if `V` is
PPT (Def-116.b) and (1) completeness: ∀ `x ∈ L` ∃ `y` ∀ `z`:
`Pr_{r_P, r_V}[out_V[P_{r_P}(x,y) ↔ V_{r_V}(x,z)] = 1] = 1`; (2) soundness: ∃ negligible `ε`
∀ `x ∉ L` ∀ strategies `P*` (arbitrary function, arbitrary finite coin type, *no* auxiliary
input) ∀ `z`: `Pr[out_V[P*(x) ↔ V(x,z)] = 0] > 1 − ε(|x|)`. Formalized with
`Pr[out_V = 1] ≤ ε(|x|)` (equivalent up to the strictness of the inequality, immaterial for
negligible `ε`; `out_V : Bool`). The quantification over `P*` with an arbitrary coin type is
universe-polymorphic; use coin strings `Fin ℓ → Bool` for arbitrary `ℓ` (WLOG deterministic
`P*` by averaging — record as a lemma). *Text issue:* "`> 1 − e`" strict.

**Def-117.a (soundness error).** Same with `1 − ε(|x|)` replaced by `1 − s(|x|)` for a given
`s : ℕ → ℝ` (e.g. constant `1/2`). Used for the single-iteration protocols.

**Def-117.b (IP).** `IP := {L : Language Bool | ∃ (P V), IsInteractiveProof P V L}`.

**Claim-117.c (NP ⊆ IP).** For `L ∈ Complexity.NP` (certificate length `C(|x|+1)^c`,
verifier `V ∈ P` on `x ++ u`): the one-round protocol "P sends `u`; `V` accepts iff
`|u| = C(|x|+1)^c ∧ x ++ u ∈ V`" is an interactive proof with soundness error `0`.
Completeness: the witness `u`; soundness: for `x ∉ L` no `u` is accepted. Machine content:
package the `P`-decider (`mem_P_iff`) as a PPT strategy (time poly in `|x|` since `|u|` is
poly in `|x|`). Optional (the text states it as trivial).

**Claim-117.d (IP = PSPACE).** Cited (Shamir). Deferred; nothing downstream.

**Def-117.e (graphs, `σ(G)`, isomorphism).** Graphs on `n` vertices are
`SimpleGraph (Fin n)`; for `σ : Equiv.Perm (Fin n)`, `σ(G) := G.map σ.toEmbedding`
(edges `{σ u, σ v}`); `G1 ≅ G2 :⇔ ∃ σ, σ(G1) = G2`. Lemmas: `σ(τ(G)) = (σ * τ)(G)`
(`SimpleGraph.map_map`, note `Equiv.Perm` multiplication order), `1(G) = G`
(`map_id`), `σ(G) = H ↔ G = σ⁻¹(H)` (`map_symm`/`comap_symm`), injectivity of
`G ↦ σ(G)`, `≅` is an equivalence relation, and the bridge
`Nonempty (G1 ≃g G2) ↔ G1 ≅ G2` (`SimpleGraph.Iso.map σ G1 : G1 ≃g σ(G1)` one way;
`RelIso.toEquiv` and `map_adj` the other). Finiteness: `Fintype (SimpleGraph (Fin n))`
(Mathlib `Basic.lean:110`) and `Fintype (Perm (Fin n))`. Decidability of `G = H` and of
`G.Adj`: use classical decidability at the concrete layer; the machine layer works on the
adjacency-matrix encoding (Inf-4.1).

**Def-118.a (`L_iso`, `L_niso`, `R_iso`).** Typed: `L_iso n := {(G0, G1) | G0 ≅ G1}`,
`R_iso (G0,G1) σ :⇔ σ(G0) = G1`, `L_niso n := {(G0, G1) | ¬ G0 ≅ G1}` (same vertex count by
typing). String forms via Inf-4.1 (pairs of adjacency matrices; malformed strings decode to
a default pair and are *not* in `L_niso`). The text's "same number of vertices" condition is
the typing.

**Claim-118.b (`L_iso ∈ NP`).** String level: certificate = encoding of `σ` (length
`≤ C(|x|+1)^c`), verifier computes `σ(G0)` and compares with `G1` in polynomial time.
Optional; the typed `R_iso` is what Defs 119.5/121.x consume.

**Claim-118.c (`L_niso ∈ coNP`).** The complement (malformed, or isomorphic) is in NP by
Claim-118.b. Deferred.

**Prot-118.3 (GNI).** Common input `x = (G0, G1)`, `n` vertices each. One iteration:
`V` draws `b : Bool` and `σ ∈ S_n` uniformly, sends `H := σ(G_b)`; `P` replies `b'`; `V`
accepts iff `b' = b`. Honest (unbounded) prover: `b' := decide (H ≅ G0) ? 0 : 1`
(classical). `n`-fold: `n` sequential iterations with fresh `(b_i, σ_i)`; `V` accepts iff all
accept; modelled as a `2n`-round protocol with verifier coins `Fin n → Bool × Perm (Fin n)`.
The prover's reply is decoded as a bit (any message other than `[true]` counts as `0`).
*Text issue:* "Repeat the procedure `|G1|` times" means `n` times.

**Lem-119.a.** If `σ₀(G0) = G1` then for uniform `σ ∈ S_n` the samplers `σ ↦ σ(G0)` and
`σ ↦ σ(G1)` have the same distribution: `σ(G1) = (σ * σ₀)(G0)` and `σ ↦ σ * σ₀` is a
bijection (`Equiv.mulRight`, `uprob_comp_equiv`). Hence for uniform `(b, σ)`, the pair
`(b, σ(G_b))` has the distribution of `(b, σ(G0))` with `b` independent of the graph.

**Lem-119.c (adaptive guessing).** For every finite `W` and every family
`g : (i : Fin n) → (Fin i → Bool) → W → Bool`:
`uprob (fun (b, w) : (Fin n → Bool) × W => ∀ i, b i = g i (fun j => b (Fin.castLT j _)) w) = 2^{-n}`.
Proof: for each `w` exactly one `b` satisfies the constraint (recursion on `n`, `Fin.snoc`),
then `uprob_eq_one_div_card`/`uprob_prod`. This is the engine of all `2^{-n}` soundness
bounds against adaptive provers.

**Lem-119.b (GNI soundness).** If `G0 ≅ G1` (via `σ₀`) then for every `P*` (coins `r`) and
`z`: `Pr_{b, σ, r}[∀ i < n, b'_i = b_i] ≤ 2^{-n}` where `b'_i` is `P*`'s reply after seeing
`H_1, …, H_i`. Proof: change variables `σ'_i := if b_i then σ_i * σ₀ else σ_i` (bijection of
`(b, σ)`), so every `H_i = σ'_i(G0)` is a function of `σ'` alone; then `b'_i = g_i(σ', r)`
and Lem-119.c (with `W := (Fin n → Perm) × ρ_{P*}`) gives exactly `2^{-n}`.

**Lem-119.d (GNI completeness).** If `¬ G0 ≅ G1` then for all `b, σ`: `σ(G_b) ≅ G_b` and
`¬ σ(G_b) ≅ G_{1−b}` (Lem-120.b), so the honest prover's `b' = b`; the `n`-fold verifier
accepts with probability `1` (`uprob_eq_one_of_forall`).

**Prop-118.4.** Protocol 118.3 (`n`-fold) is an interactive proof for `L_niso`: completeness
Lem-119.d (witness `y` irrelevant), soundness `2^{-n(x)} ≤ ε(|x|)` negligible (Inf-4.4),
`V` PPT (Inf-4.2; `σ(G)` and the comparison `b' = b`). *Text issues:* the proof writes
`G1, G2` for `G0, G1`; "the Prover runs in exponential time" is modelled by an arbitrary
function; "each iteration is independent of all prior iterations" hides the adaptive-prover
argument (Lem-119.b).

**Def-119.5 (efficient prover).** `(P, V)` is an interactive proof for `L` with efficient
prover w.r.t. `R_L` if `P` is PPT (time poly in `|x|`, witness `y` as auxiliary input) and
completeness holds for **every** `y ∈ R_L(x)` (Def-116.1 asks for *some* `y`).

**Def-119.e (interactive argument).** Soundness quantified over nuPPT `P*` only (D4
machines with advice; `P*` may receive `z`). Optional.

**Claim-119.f.** "A polynomial-time prover would imply `L_niso ∈ NP`": informal, not a
precise theorem (a deterministic PPT prover together with the public-coin verifier gives an
NP witness only after de-randomization). Deferred, not formalized.

**Prot-120.6 (GI).** Common input `(G0, G1)`, prover witness `σ` with `σ(G0) = G1`. One
iteration: `P` draws `π ∈ S_n` uniformly, sends `H := π(G0)`; `V` sends uniform `b`; `P`
sends `γ := if b then π * σ⁻¹ else π` (as functions: `γ = π ∘ σ⁻¹` so that
`γ(G1) = π(σ⁻¹(G1)) = π(G0) = H`); `V` accepts iff `γ(G_b) = H`. `n`-fold: sequential with
fresh `π_i`, `b_i`. `V`'s message is decoded as a bit by `P`. *Text issue:* the composition
order of `π · σ^{-1}` must be fixed (right-to-left as functions).

**Lem-120.a.** `σ(G0) = G1 → π(G0) = H → (π * σ⁻¹)(G1) = H` (`map_map`, `map_symm`);
hence the honest prover is accepted with probability `1` in every iteration, for every
witness `σ` (Def-119.5's "every `y`").

**Lem-120.b.** `¬ G0 ≅ G1 → ¬ (H ≅ G0 ∧ H ≅ G1)` (symmetry and transitivity of `≅`).

**Lem-120.c (single-iteration soundness).** If `¬ G0 ≅ G1` then for every `P*` (coins `r`)
and `z`: `Pr_{b, r}[γ(G_b) = H] ≤ 1/2` where `H = H(r)` and `γ = γ(r, b)`: for fixed `r`,
by Lem-120.b at most one `b` admits a `γ` with `γ(G_b) = H`; `b` is uniform and independent
of `H` (`uprob_prod`, `uprob_bool_prod`).

**Lem-120.d (`n`-fold soundness).** `Pr[all n iterations accept] ≤ 2^{-n}` for every
`P*`: with `g_i(b_{<i}, r) :=` the unique good bit for `H_i` (or `false`), acceptance in
all rounds implies `∀ i, b_i = g_i(b_{<i}, r)`; apply `uprob_mono` and Lem-119.c. This also
formalizes the remark "the protocol can be repeated … to drive the error as low as desired".

**Prop-120.7.** Protocol 120.6 (`n`-fold) is an interactive proof for `L_iso` with efficient
prover w.r.t. `R_iso`: completeness Lem-120.a for every witness, soundness `2^{-n} ≤ ε(|x|)`
(Inf-4.4), `P` and `V` PPT (permutation composition/inversion, `σ(G)`, graph equality:
Inf-4.2). *Text errors:* stated "for `L_niso`" (it is `L_iso`); the proof's
"`π(H) = G1` and `σ(π(H)) = σ(G1) = G2`" has the maps reversed and uses `G1, G2` for
`G0, G1`; the proof only argues `1/2` per iteration.

### §4.6 Zero-knowledge — `ZeroKnowledge/Defs.lean`, `GraphIsomorphismZK.lean`

**Def-121.1 (HVZK).** `(P, V)` an interactive proof with efficient prover for `L` with
witness relation `R_L`. HVZK if ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `x ∈ L`,
`y ∈ R_L(x)`, `z`: `distAdv (viewV x y z) (S x z) D ≤ ε(|x|)` where
`viewV x y z : ρ_P × ρ_V → View_V` is the honest verifier's view sampler and
`S x z : ρ_S → View_V` (`S` outputs a *view*, i.e. `(x, z, r_V, messages received)`).
*Text issue:* `e(n)` with `n` undefined — read `n = |x|`.

**Def-121.2 (ZK).** ∀ PPT `V*` ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `x ∈ L`,
`y ∈ R_L(x)`, `z`: `distAdv (viewV* x y z) (S x z) D ≤ ε(|x|)`. Deviation (D8): `S` strict
PPT instead of expected PPT (stronger demand on `S`). `V*` is PPT with auxiliary input `z`
(the text's remark on non-uniformity, Claim-122.c).

**Def-121.a (expected PPT).** Expected running time over the machine's own coins polynomial.
Deferred (D8); would need a sampler with unbounded coin usage.

**Def-122.a (perfect / statistical ZK).** Perfect: the two distributions identical for all
`x, y, z` (then `distAdv = 0` for every `D`). Statistical (campaign addition, needed for
Thm-122.3): `statDist (view distribution) (S distribution) ≤ δ(|x|)` with `δ` negligible —
implies Def-121.2 for every `D` by `distAdv_le_statDist`, and `δ := 2^{-n}` is the GI case.
*Note:* the GMR definition lets a perfect simulator output `⊥` with probability `≤ 1/2`;
the text does not.

**Claim-122.b (view vs output).** Replacing `view_{V*}` by `out_{V*}` gives an equivalent
definition: (⇒) `out` is a PPT function of the view, so `S' := out_{V*} ∘ S` works by
closure (`distAdv_sunglassRed`, Lem-71.5); (⇐) apply the output-based definition to the
PPT `V*'` that outputs its own view. Optional.

**Claim-122.c.** ZK against PPT `V*` with auxiliary input already covers nuPPT `V*` (advice
as part of `z`, simulator receives the same advice). Deferred (needs a nuPPT verifier
notion; remark only).

**Thm-122.3.** Protocol 120.6 is a zero-knowledge interactive proof for `L_iso` with the
canonical witness relation `R_iso`. Formalized as: (a) Prop-120.7; (b) **single iteration**:
for every `V*` (any strategy with finite coins at the concrete layer; PPT at the asymptotic
layer) the truncated simulator `S_n` (Alg-123.4) satisfies
`statDist (viewV* x σ z) (S_n x z) ≤ 2^{-n}` for all `(G0,G1) ∈ L_iso`, `σ ∈ R_iso`, `z`
(Thm-122.3.trunc), hence statistical ZK with `ε = 2^{-n(x)}` (Inf-4.4) and `S_n` PPT
(Claim-123.d); (c) the `n`-fold protocol: ZK under the sequential-composition hypothesis
Claim-123.c (deferred). *Text issue:* "perfect" becomes statistical because of truncation
(D8); the text proves one iteration only.

**Thm-122.3.hv (HVZK, perfect, by reindexing).** Simulator: draw `b : Bool`, `γ ∈ S_n`
uniformly, output `(x, z, b, [γ(G_b), γ])`. For `σ(G0) = G1`, the honest view sampler
`(π, b) ↦ (x, z, b, [π(G0), if b then π * σ⁻¹ else π])` equals the simulator sampler
composed with the bijection `(π, b) ↦ (if b then π * σ⁻¹ else π, b)` (Lem-120.a), so the
two distributions are identical (`acceptProb_comp_equiv`). Same shape as
`Schnorr.schnorr_hvzk` (`reindex`), which is the template.

**Alg-123.4 (GI simulator, truncated).** `S_n(x, z)` with coins
`(b', π, r) : Fin n → Bool × Perm (Fin n) × ρ_{V*}`: for attempt `k = 0, …, n−1`: `H_k := π_k(G_{b'_k})`;
`b_k :=` bit decoded from `V*.next x z r_k [H_k]`; if `b_k = b'_k` output
`some (x, z, r_k, [H_k, π_k])` (the view of `V*`), else continue; after `n` failures output
`none` (`⊥`). Deviation: truncation (strict PPT) instead of restart until success.

**Lem-123.5.** For `(G0,G1) ∈ L_iso`, in one attempt: (i) the sampler
`(b', π) ↦ (b', π(G_{b'}))` has the distribution of `(b', π) ↦ (b', π(G0))`, so `H` is
independent of `b'` and distributed as `π(G0)` (Lem-119.a); (ii) for every function
`V*` and every `z`: `Pr_{b', π, r}[V*(x, z, r, [H]) = b'] = 1/2` (`b` depends on
`(H, r, z)` only; condition on `(H, r)` and use `uprob_bool_prod`).

**Claim-123.a.** Expected number of attempts of the untruncated simulator is `2`. Deferred
(Def-121.a).

**Claim-123.b (perfect simulation given success).** For every view `v`:
`Pr_{b', π, r}[attempt outputs v ∧ b = b'] = (1/2) · Pr_{π, r}[viewV*(x, σ, z)(π, r) = v]`.
Proof: for fixed `r` the real execution is `π ↦ (H = π(G0), b = V*(H, r), γ = if b then π * σ⁻¹ else π)`;
the successful attempts are `(b', π')` with `H = π'(G_{b'})`, `b = V*(H, r) = b'`, output
`π'`; the map `(b', π') ↦ π := if b' then π' * σ else π'` (so that `π(G0) = H` and
`γ = π'`) is a bijection from `{(b', π') | success}` onto `Perm` with `b' = b(π)`; hence the
two counts agree up to the factor `1/2` from the `b'` coordinate (`uprob_eq_of_equiv`,
`uprob_prod`). Model: `TCSlib.MPC.BGW.linear_perfectPrivacy` (perfect privacy by a coin
bijection).

**Thm-122.3.trunc.** `Pr[S_n = ⊥] = 2^{-n}` (attempts use disjoint coins; each fails with
probability exactly `1/2` by Lem-123.5(ii); `uprob_prod`/`OneWay.uprob_pi_forall`) and for
every `v`: `Pr[S_n = some v] = (1 − 2^{-n}) · Pr[view = v]` (sum over the first successful
attempt of `2^{-k} · (1/2) · Pr[view = v]`, Claim-123.b); therefore
`statDist (S_n) (some ∘ view) = 2^{-n}` and `distAdv (S_n x z) (some ∘ viewV* x σ z) D ≤ 2^{-n}`
for every `D` (`distAdv_le_statDist`).

**Claim-123.c.** Sequential repetition of a ZK protocol is ZK (§7.2.1). Deferred (outside
Chapters 2–4; needs the auxiliary-input hybrid over iterations). Stated as a hypothesis
where the `n`-fold theorems need it.

**Claim-123.d.** `S_n` is strict PPT when `V*` is: `n` attempts of (sample, `π(G)`, one call
of `V*` with fresh coins, compare) — plan `Randomized/Repetition.lean` on top of
`Turing.FinTM.exists_loopFindTM` (first accepting round's payload). Machine-level; the
load-bearing infrastructure item of the chapter together with Claim-128.a.

### §4.7 Zero-knowledge for NP — `ZeroKnowledge/NP.lean`

**Thm-124.1.** If one-way permutations exist then every language in NP has a ZK proof.
Formalized in three forms: **(A, core)** for every `(L, R_L)` and every Levin reduction
`(f, w)` from `(L, R_L)` to `(3COL, R_3COL)` (Def-124.a, string level through Inf-4.1), the
composed protocol — both parties compute `x' := f(x)`, the prover additionally `y' := w(x, y)`,
then run Protocol 127.5 — gives, under the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` (run-3 P11-1),
an interactive proof with efficient prover for `L` (the pulled-back repeated protocol), a ZK
single iteration (DQ5), and the single iteration's soundness error (`zk_proof_of_levinReduction`;
Claim-124.d applied to Prop-127.6, with the commitment scheme from Thm-126.4; gate 03g,
finding 6). **(B, optional/deferred)** "every
`L ∈ Complexity.NP`" follows from (A) given string-level Levin NP-hardness of 3COL
(Claim-124.b + Claim-124.c), stated as an explicit hypothesis. **(C, optional)** with an
*unbounded* honest prover a Karp reduction suffices (the prover finds a colouring of `f(x)`
classically) — but Def-121.2 requires an efficient prover, so (C) is only a remark.
*Text issues:* "Cook's reduction can be applied to the witness `y`" requires a Levin
reduction, never defined in the text; "execute protocol `(P, V)` on `x'`" should be
`(P', V')`; the theorem silently needs a hard-core predicate for the OWP (Thm-87.3).

**Def-124.a (Levin reduction).** `(f, w)` with `PolyTimeComputable f`, `w` polynomial-time
in `(x, y)` (two-argument via `pairEncode`), `∀ x, x ∈ L ↔ f x ∈ L'`, and
`∀ x y, R_L x y → R_{L'} (f x) (w x y)`, with `f` length-regular (`length_eq :
|f x| = p(|x|)`) for a length polynomial `p ≥ id` (`le_eval`). Extends
`Complexity.PolyTimeReducible` (Karp); gate 03g, finding 6.

**Claim-124.b (3COL NP-complete, string level).** `3COL := {x | (decodeGraph x).Colorable 3}`;
NP membership (colouring certificate) and NP-hardness via `SAT3 ≤ₚ 3COL`. The repository
has `Complexity.SAT3_NPComplete` and the graph-level `SATtoColor.SATtoColorReduction`
(on `SATtoColor.Sat3 V`, a different 3SAT syntax from `CNF.decode`); the poly-time string
reduction machine is missing — large machine-building task. Deferred.

**Claim-124.c (witness transformation 3SAT → 3COL).** The colouring built from a satisfying
assignment is `SATtoColor.sat3Coloring` (declared `private`; its validity is the content of
`SATtoColorCompleteness`). A Levin reduction needs it as a poly-time string function.
Deferred with Claim-124.b.

**Claim-124.d (ZK transfers along Levin reductions).** If `(P', V')` is a ZK proof with
efficient prover for `(L', R_{L'})` and `(f, w)` is a Levin reduction from `(L, R_L)`, then
`P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)` is a ZK proof with efficient prover for
`(L, R_L)`: completeness from `R_L x y → R_{L'} (f x) (w x y)` and `hLR : ∀ x ∈ L, ∃ y, R x y`
(the formal transfer needs it; gate 03g, finding 6); soundness: `x ∉ L → f x ∉ L'`
and a cheating `P*` for `x` is a cheating prover for `f x`; ZK: for `V*`, let
`V*'(x', (x, z)) := V*(x, z)` (recovers `x` from its auxiliary input, ignores `x'`), then
`viewV*[P(x,y) ↔ V*(x,z)] = viewV*'[P'(f x, w x y) ↔ V*'(f x, (x,z))]` up to relabelling,
and `S(x, z) := S'(f x, (x, z))`; PPT-ness of `P`, `V`, `V*'`, `S` by composition with `f`,
`w`. Negligibility: `ε'(|f x|)` with `|f x| ≤ poly(|x|)` and `|f x| ≥ …` — needs
`f` length-nondecreasing or a `Negligible.mono`-type lemma for polynomially related
parameters (record).

**Claim-124.e.** General one-way functions suffice (Naor commitments). Deferred.

**Def-124.f (3COL, `R_3COL`).** Typed: `3COL n := {G : SimpleGraph (Fin n) | G.Colorable 3}`
(`= Nonempty (G.Coloring (Fin 3))`, literally `SATtoColor.Is3Colorable G`); witness
relation `R_3COL G c :⇔ ∀ u v, G.Adj u v → c u ≠ c v` for `c : Fin n → Fin 3`
(`SimpleGraph.Coloring.mk`). Colours `{1,2,3}` are `Fin 3`.

**Claim-125.a.** For `m ≥ 1`: `(1 − 1/m)^{n·m} ≤ exp(−n) ≤ 2^{-n}`. From
`Real.one_sub_div_pow_le_exp_neg` (`(1 − t/N)^N ≤ exp(−t)` with `N = n·m`, `t = n`) or
`Real.add_one_le_exp`. Pure real analysis; the text writes `≈ e^{-n}`.

### §4.7.1 Commitments — `ZeroKnowledge/Commitment.lean`

**Def-126.3 (commitment scheme).** A deterministic polynomial-time `Com` and polynomial `ℓ`
with (1) binding: ∀ `n`, ∀ `v0 ≠ v1 ∈ {0,1}^n`, ∀ `r0, r1 ∈ {0,1}^{ℓ(n)}`:
`Com(v0, r0) ≠ Com(v1, r1)`; (2) hiding: ∀ nuPPT `D` ∃ negligible `ε` ∀ `n`,
`v0, v1 ∈ {0,1}^n`: `distAdv (fun r => Com n v0 r) (fun r => Com n v1 r) D ≤ ε(n)`.
Concrete: `Com n : (Fin n → Bool) → (Fin (ℓ n) → Bool) → C n`. Deviation (DQ4): `n` is an
explicit argument (the text infers it from `|v|`). *Text error:* binding as printed omits
`v0 ≠ v1` and is unsatisfiable (`v0 = v1`, `r0 = r1`).

**Claim-126.a (multi-value hiding).** For every commitment scheme, polynomial `q`, nuPPT `D`
∃ negligible `ε` ∀ `n`, `(v_i), (v'_i) ∈ ({0,1}^n)^{q(n)}`:
`distAdv ((r_i) ↦ (Com n v_i r_i)_i) ((r_i) ↦ (Com n v'_i r_i)_i) D ≤ ε(n)`. Proof: hybrids
`H_k` (coordinates `< k` from `v'`, `≥ k` from `v`), `exists_hybrid_gap`; the reduction for
index `k` gets a commitment to `v_k` or `v'_k`, samples the other coordinates' commitments
itself (`Com` is poly-time; `acceptProb_update` plants the challenge), so advantage
`≥ ε_D/q(n)`; non-uniform choice of `k` or the averaged `mixDist` reduction. Generalizes
`exists_multicopyRed_ge` (identical pair in all coordinates) — a per-coordinate version is
needed (new concrete lemma; propose it for `Indistinguishability`-style reuse but keep a
private copy here per the ownership rule). Needed by Claim-129.d.

**Thm-126.4.** If `f` is a one-way permutation (length-preserving bijection at every `n`,
Def-27.3) with hard-core predicate `h` (Def-78.3), then Alg-127.a is a commitment scheme:
`Com` poly-time (from `f`, `h` poly-time), binding (Claim-127.b), hiding (Claim-127.c for one
bit, Claim-127.d for `n` bits). Unconditional-from-OWP form: apply Goldreich–Levin
(Thm-87.3) to get `(g, ⟨·,·⟩)` with `g(x, r) = (f x, r)` a OWP — optional, depends on the
Chapter 3 asymptotic GL theorem. *Text issue:* OWP here is a single function (Thm 79.4's
usage), not the collection of Def 55.1; the existence of `h` is not mentioned.

**Alg-127.a (construction).** `Com₁ n b r := (f n r, b ⊕ h n r)` for `r ∈ {0,1}^n`
(`ℓ(n) = n`); `Com n v (r_1, …, r_n) := (Com₁ n (v i) (r i))_i` (`ℓ(n) = n²`). With the
Garg layer: `owpGen f B : α × Unit → α × Unit × Bool` is `Com₁(0, ·)` and `owpGenNot f B`
is `Com₁(1, ·)` up to the `Unit` coordinate.

**Claim-127.b (binding).** `f n` injective ⇒ `Com₁ n b0 r0 = Com₁ n b1 r1 → r0 = r1 → b0 = b1`;
for the `n`-bit scheme, `v0 ≠ v1` differ at some `i`, and coordinate `i` separates.

**Claim-127.c (single-bit hiding, concrete).** For every `D : C → ρ → Bool`:
`predProb (owpPair f) B (owpPredictor D flip) = 1/2 ± distAdv (Com₁ 0) (Com₁ 1) D / 2`
for the appropriate `flip`, i.e. a distinguisher with advantage `ε` yields a predictor of
`h(r)` from `f(r)` with success exactly `1/2 + ε/2` — this **is**
`predProb_owpPredictor_false`/`_true` with `β := Unit` (`acceptProb` is invariant under the
`Unit` coordinate, `acceptProb_fst`). Asymptotic: if `h` is hard-core then
`distAdv ≤ 2 ε_h(n)` with the predictor nuPPT (one extra coin, one call of `D`). "Identical
to the proof of Theorem 104.4" (prediction lemma Lem-73.8 + XOR trick).

**Claim-127.d (bitwise hybrid, "show this!").** Hiding of `Com₁` ⇒ hiding of `Com`:
hybrids over the `n` bits (`exists_hybrid_gap`), the reduction plants the challenge
commitment at bit `k` and samples the others (`acceptProb_update`); advantage `≥ ε/n`;
`Negligible.mul_pow`. Special case of Claim-126.a with `q = n`, values single bits.

### §4.7.2 Graph 3-colouring — `ZeroKnowledge/ThreeColoring.lean`

**Prot-127.5.** Common input `G : SimpleGraph (Fin n)` with `m := |E|` (`E := G.edgeFinset`);
prover witness `c : Fin n → Fin 3` with `R_3COL G c`. One iteration: `P` draws
`π ∈ Perm (Fin 3)` and `r_i ∈ {0,1}^{ℓ(n)}` (`i < n`) uniformly and sends
`com_i := Com n (pad (π (c i))) (r_i)`; `V` sends a uniform edge `e = {i, j} ∈ E`; `P` sends
the openings `(π (c i), r_i, π (c j), r_j)`; `V` accepts iff `e ∈ E`,
`Com n (pad c'_i) r_i = com_i`, `Com n (pad c'_j) r_j = com_j` and `c'_i ≠ c'_j`.
`n·m`-fold: sequential with fresh `π`, `r`. Deviations: the opening check (the text's
"`V` accepts iff `c'_i ≠ c'_j`" is unsound without it); colours padded to `n` bits
(DQ4, requires `n ≥ 2`); if `E = ∅` the verifier accepts outright (every edgeless graph is
3-colourable; the text's "random edge" is undefined). *Text errors:* witness listed as
`c0, …, cm` (should be `c1, …, cn`).

**Claim-127.e (completeness).** For `R_3COL G c`, any `π`, `r`: `π (c i) ≠ π (c j)` on every
edge (`Coloring.valid`, `π` injective) and the openings verify; `V` accepts with
probability `1` in every iteration (`uprob_eq_one_of_forall`).

**Lem-127.f (committed colouring).** From binding: for each commitment string `com`, there
is at most one `v ∈ {0,1}^n` with `∃ r, Com n v r = com`; let `c̃ k : Option (Fin 3)` be the
colour it decodes to (if any). An opening accepted by `V` on edge `{i, j}` forces
`c'_i = c̃ i`, `c'_j = c̃ j`. If `¬ G.Colorable 3` then for every `c̃` there is an edge
`{i, j} ∈ E` with `c̃ i = c̃ j` or one endpoint undefined (else `c̃` would be a proper
colouring, after sending `none` to any colour), on which no opening is accepted.

**Lem-127.g (adaptive sequential soundness, escape `1/m`).** For `k` rounds with uniform
challenges `e_i ∈ Fin m` (or `E`) and any `Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m)`
with `∀ i h w, (Bad i h w).Nonempty`:
`uprob (fun (e, w) => ∀ i, e i ∉ Bad i (e|_{<i}) w) ≤ (1 − 1/m)^k`. Proof by induction with
`uprob_prod`. Lem-119.c is the equality case `m = 2`, `|Bad| = 1`.

**Claim-127.h (soundness of 127.5).** If `¬ G.Colorable 3` (and `m ≥ 1`) then for every
`P*` (coins `r`) and `z`: `Pr[V accepts all n·m iterations] ≤ (1 − 1/m)^{n·m} ≤ e^{-n}`:
in iteration `i`, given the history, the committed colouring `c̃_i` has a bad edge
(Lem-127.f), the verifier's uniform edge hits it with probability `≥ 1/m` and then the
iteration rejects; Lem-127.g, Claim-125.a. *Text error:* "repeated `|E|²` times".

**Prop-127.6.** Protocol 127.5 is a ZK proof for 3COL: (a) interactive proof with efficient
prover w.r.t. `R_3COL`: Claim-127.e, Claim-127.h with `e^{-n(x)}` negligible in `|x|`
(Inf-4.4), `P`, `V` PPT (`Com` poly-time, edge sampling per DQ1, Inf-4.2); (b) ZK of the
single iteration: Prop-128.8 + Claim-128.a; (c) the `n·m`-fold protocol's ZK under
Claim-123.c (deferred).

**Alg-128.7 (3COL simulator, truncated).** `S(x, z)` with coins per attempt
`(e' = {i', j'} ∈ E, (a, b) ∈ {(u, v) : Fin 3 × Fin 3 | u ≠ v}, r : Fin n → {0,1}^{ℓ(n)}, r_{V*})`:
`c'_{i'} := a`, `c'_{j'} := b`, `c'_k := 0` otherwise; `com_k := Com n (pad c'_k) r_k`;
`e :=` edge decoded from `V*.next x z r_{V*} [com]`; if `e = e'` output
`some (x, z, r_{V*}, [com, (a, r_{i'}, b, r_{j'})])` else next attempt; after `n·m` attempts
output `none`. *Text issues:* "`k ∈ [m] \ {i', j'}`" should be `[n]`; `(i, j) = (i', j')`
is equality of unordered edges.

**Claim-128.a.** `S` is strict PPT when `V*` is (loop of `n·m` attempts, each with `n`
evaluations of `Com` and one call of `V*`): Inf-4.3.

**Prop-128.8.** ∀ PPT `V*` ∀ nuPPT `D` ∃ negligible `ε` ∀ `G ∈ 3COL`, `c ∈ R_3COL(G)`, `z`:
`distAdv (viewV* G c z) (S G z) D ≤ ε(|x|)`. Proof chain (all at the concrete layer, then
negligibility): `S ≡ S'` (Claim-129.a), `distAdv(S', S'') ≤ (n·m) · ε_Com` (Claim-129.d),
`statDist(S'', view) ≤ e^{-n}` (Claim-129.c); triangle inequality, `Negligible.add`,
`Negligible.mul_pow`. The hardest theorem of the chapter. *Text issues:* hybrid count
`2n|E|` (there are `n|E|` attempts); the sub-hybrid `S̃_e` over `6|E|` values of
`(i', j', π)` is unnecessary (the reduction samples them; non-uniformly one may fix the
best); typo "in `S̃_{e+1}` … whereas in `S̃_{e+1}`"; the last step uses multi-value hiding
(Claim-126.a) and closure (Lem-71.5).

**Claim-129.a (`S ≡ S'`).** `S'` receives the witness `c` and sets
`(c'_{i'}, c'_{j'}) := (π (c i'), π (c j'))` for uniform `π ∈ S_3` instead of a uniform
distinct pair; since `c i' ≠ c j'` on an edge, Lem-129.b makes the two samplers equal in
distribution; everything else is identical.

**Lem-129.b.** For `a ≠ b : Fin 3`, `π ↦ (π a, π b)` is a bijection
`Perm (Fin 3) ≃ {p : Fin 3 × Fin 3 // p.1 ≠ p.2}` (both sides have `6` elements,
`Fintype.card_perm`; injectivity since a permutation of `Fin 3` is determined by two values;
or `decide` after enumeration).

**Claim-129.c (`S''`).** `S''` commits to `pad (π (c k))` for **all** `k` (like the honest
prover) but still restarts unless `e = e'`: (i) `e'` is independent of `V*`'s reply (the
commitments do not depend on `e'`), so each attempt succeeds with probability exactly `1/m`
and `Pr[S'' = ⊥] = (1 − 1/m)^{n·m} ≤ e^{-n}` (`uprob_prod`, Claim-125.a); (ii) conditioned
on success the output is the honest view (commitments and openings with the prover's
distribution of `(π, r)`, edge `e` chosen by `V*`), as in Claim-123.b; hence
`statDist (S'') (some ∘ view) ≤ e^{-n}` and `distAdv ≤ e^{-n}` for every `D`.

**Claim-129.d (`S' ≈ S''`).** `S'` and `S''` differ only in the `n − 2` unopened commitments
of each attempt (`pad 0` versus `pad (π (c k))`). Hybrids `S_k` (attempts `< k` as `S''`,
`≥ k` as `S'`), `k = 0, …, n·m`; `exists_hybrid_gap` gives an adjacent pair with gap
`≥ δ/(n·m)`; the reduction for index `k` samples `(e', π, r_{V*})` of attempt `k` and all
other attempts itself, receives the commitment vector for the unopened positions from the
multi-value hiding challenger (Claim-126.a with `q = n`, values `pad 0` vs `pad (π (c ·))`,
the two opened positions committed by the reduction), simulates the restart logic, and runs
`D`; by `distAdv_sunglassRed`/`acceptProb_bind` its advantage equals the hybrid gap. It is
nuPPT by closure (Lem-71.5). Conclusion: `distAdv(S', S'') ≤ n·m · ε_Com(n)`, negligible.

### Appendix B

**Def-191.10 (DP).** Deterministic polynomial time = `Complexity.P` (exists). Alias only.

**Def-191.11 (NP via witness relations).** `L ∈ NP` iff ∃ `R_L ⊆ {0,1}* × {0,1}*`
poly-time recognizable and polynomial `p` with `x ∈ L ↔ ∃ y, |y| ≤ p(|x|) ∧ (x, y) ∈ R_L`;
`R_L(x) := {y | (x, y) ∈ R_L}`. Existing: `Complexity.mem_NP_iff_exists_length_le` is this
form with `p(N) = C(N+1)^c` and the pair `pairEncode x y` in a `P` language — the bridge is
a one-line unfolding. Chapter 4 consumes only the typed relation `R : X → Y → Prop` with
`L = {x | ∃ y, R x y}`. *Text error:* "`R_L(x) = {y : (x, y) ∈ L}`" should read `∈ R_L`.

**Def-192.12 (BPP).** Not used by Chapter 4; optional, trivial once `Randomized/PPT.lean`
is frozen.

### Infrastructure specific to Chapter 4

**Inf-4.1 (encodings).** `encGraph : SimpleGraph (Fin n) → List Bool` (adjacency matrix
`Fin n → Fin n → Bool`, row-major, prefixed by `n` in unary or binary via `pairEncode`),
`decGraph : List Bool → Σ n, SimpleGraph (Fin n)` total with default; same for
`Perm (Fin n)` (image list), `Fin 3`-colourings, message lists (`pairEncode`-folded) and
views. Length bounds `|encGraph G| ≤ C·(n+1)²`, decode-encode identities, and
`PolyTimeComputable` of the (de)coders. New file `ZeroKnowledge/Encoding.lean` (proposed
split; not in the plan's layout).

**Inf-4.2 (honest parties as machines; DQ1).** `PolyTimeComputable` facts for `σ(G)`,
`π * σ⁻¹`, `G = H`, `e ∈ E`, `Com` evaluation on encoded inputs, and the sampling of
`σ ∈ S_n`, `e ∈ E`, `π ∈ S_3` from coins (option A: near-uniform with error `2^{-n}`,
machine level, difficulty 5; option B: typed coin spaces, difficulty 3). Every `IsPPT`
side-condition of Props 118.4, 120.7, 127.6 lives here.

**Inf-4.3 (bounded restart loops).** The plan's `Randomized/Repetition.lean`: a PPT that
runs a PPT body up to `N(|x|)` times with fresh coins and returns the first accepted payload
(`exists_loopFindTM`). Consumed by Claim-123.d and Claim-128.a.

**Inf-4.4 (negligibility in `|x|`).** If `|encGraph G| ≥ n(G)²/C` (or `n ≥ Nat.sqrt (|x| / C)`)
then `fun N => (2:ℝ)⁻¹ ^ Nat.sqrt (N / C)` and `fun N => Real.exp (−Nat.sqrt (N / C))` are
negligible (`negligible_two_pow_neg` composed with the sub-polynomial growth of `sqrt`;
`Negligible.mono`). Converts the chapter's per-vertex bounds into Def-116.1's `ε(|x|)`.

## 4. Text errors and gaps found in Chapter 4 (for the plan's error list)

1. Proposition 120.7 says "interactive proof for `L_niso`"; it is for `L_iso` (already in the plan).
2. Definition 126.3, binding: the quantifier omits `v0 ≠ v1`; as printed the condition is unsatisfiable.
3. Proposition 127.6's proof: "repeated `|E|²` times" vs. the protocol's `n|E|` (already in the plan).
4. Protocol 127.5 lists the witness as `c0, c1, …, cm`; it is `c1, …, cn`. Simulator 128.7 writes "`k ∈ [m] \ {i', j'}`" for `[n]`.
5. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`": without checking that the openings match the commitments the protocol is unsound; also undefined for `E = ∅`; and `Com` applied to 2-bit colours has security parameter 2 under Definition 126.3 (the colour must be padded or `Com` given `1^n`).
6. Proof of Proposition 120.7: "`π(H) = G1` and `σ(π(H)) = σ(G1) = G2`" reverses the maps and renames the graphs; the correct identities are `π(G0) = H`, `(π∘σ⁻¹)(G1) = H`.
7. Theorem 122.3 claims (perfect) ZK for Protocol 120.6 with `n` iterations; the proof covers one iteration and relies on §7.2.1 (sequential composition), which is outside Chapters 2–4.
8. Definitions 121.1, 121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined (intended `n = |x|`).
9. Proof of Proposition 128.8: the hybrid count `2n|E|` does not match the `n|E|` attempts; "in `S̃_{e+1}` … whereas in `S̃_{e+1}`" (second should be `S̃_e`); the `6|E|`-step sub-hybrid is unnecessary.
10. §4.7, Step 2: "Cook's reduction can be applied to the witness" needs a Levin (witness-preserving) reduction, never defined; "execute protocol `(P, V)` on `x'`" should be `(P', V')`.
11. Theorem 126.4 uses a single one-way permutation `f` with a hard-core predicate `h`, whereas Definition 55.1 defines OWPs as collections and the existence of `h` (Theorem 87.3) is not invoked.
12. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
13. Proof of Proposition 118.4 uses `G1, G2` for `G0, G1`; "exponential time prover" is only an upper bound on what an unbounded prover needs.
14. The chapter never states that "choose a random permutation `σ ∈ S_n`" / "a random edge" cannot be done exactly by a PPT with a bounded coin string (DQ1).

## 5. Proposed file split (plan layout, with one addition)

```
TCSlib/Cryptography/ZeroKnowledge.lean                    facade (## Contents)
TCSlib/Cryptography/ZeroKnowledge/Encryption.lean         Def-111.1/a/b, Thm-112.2(.i,.ii), Claim-112.a/b
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean        Def-114.a … Def-116.b
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean  Def-116.1, 117.a/b, Claim-117.c, Def-119.5, 119.e, Def-191.11 (typed)
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean           Inf-4.1 (new; string encodings and their poly-time (de)coders)
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean   Def-117.e, 118.a, Claim-118.b, Prot-118.3, Lem-119.a–d, Prop-118.4, Prot-120.6, Lem-120.a–d, Prop-120.7
TCSlib/Cryptography/ZeroKnowledge/Defs.lean               Def-121.1, 121.2, 122.a, Claim-122.b, Inf-4.4
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean Thm-122.3(.hv,.trunc), Alg-123.4, Lem-123.5, Claim-123.b/d
TCSlib/Cryptography/ZeroKnowledge/Commitment.lean         Def-126.3, Claim-126.a, Alg-127.a, Claim-127.b/c/d, Thm-126.4
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean      Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e/h, Lem-127.f/g, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a/c/d, Lem-129.b
TCSlib/Cryptography/ZeroKnowledge/NP.lean                 Def-124.a, Thm-124.1, Claim-124.d (Claim-124.b/c as hypotheses)
```

`GraphIsomorphism.lean` and `ThreeColoring.lean` are at risk of exceeding 600 lines; split
`ThreeColoring.lean` into `ThreeColoring/Protocol.lean` (protocol, completeness,
soundness) and `ThreeColoring/Simulator.lean` (Alg-128.7 … Claim-129.d) if so.

## 6. Risk notes for the planners

* The chapter's hard core is three "perfect simulation by coin bijection" arguments
  (Claim-123.b, Claim-129.c) and one reduction with an internal restart loop (Claim-129.d);
  everything else is bookkeeping. Budget the fill accordingly.
* Both truncated simulators and the `n`-fold protocols need the Repetition infrastructure
  (Inf-4.3) and DQ1's answer before their PPT side-conditions can be stated.
* Thm-124.1's "every NP language" form is blocked on a string-level Levin reduction to 3COL
  (Claim-124.b/c); state it with the reduction as a hypothesis.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03g-pack.md =====

# Gate 03g ([PS10] ch. 2–4, 3-colouring zero knowledge): external statement audit pack

**Status: ready to dispatch once [Shilun-Allan-Li/tcslib#201](https://github.com/Shilun-Allan-Li/tcslib/pull/201) merges** (re-staged 2026-11-05 at that PR's head, the gate 03a + 03c repairs; first staged at `a3c5fa8b`; the evidence is under `evidence/g/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`0c348ff94cacf24d96d99078c9dd9e328530c8d2` (the head of #201; its Lean files are what the branch holds once #201 merges). This pack covers the graph 3-colouring language and its encodings, the commitment-based protocol of §4.7 and its parties, the soundness and efficiency of the repeated protocol, the simulator and its analysis, and the headline zero-knowledge theorem for 3COL behind Thm 124.1.
- **This pack gates fills.** Its files hold **3 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03g-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.7 (book pp. 124–129).

## Changes since the first staging (repairs of the interface packs; check them, do not re-find them)

The pin moved from `a3c5fa8b` to the head of the gate 03a + 03c repair PR. Changes in or near this pack's files:
- **G3-3** (gate 03e major 1, merged in #199): proof systems carry ch. 6's efficiency convention.
  - `InteractiveProof`'s completeness takes a message bound `B` (`Protocol.ProverBounded`, now in `Interaction.lean`), and `EfficientProverProof` has the field `boundedP`.
  - `Protocol.lean` adds `length_multiCom_le`, `colProver_length_le` and `colProtocol_proverBounded`: the honest provers' messages are polynomially bounded in `|x|`.
  - `ProtocolProofs.lean` uses `colProtocol_proverBounded` for the bound.
  - The docstrings that called the parties "PPT strategies" now say "efficient (D8)".
- **G3-4** (#199): `PerfectZKAbort.statZK` and tied Thm 124.1 forms (pack 03e). Three new `sorryAx` dependencies reach this pack's stubs through those forms.
- **Gate 03l, major 1:** the axiom attestation below prints every public theorem and lemma of this pack's files, not only `Checks.lean`'s headlines.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a malicious verifier that asks an edge outside the graph;
- a graph encoding with no edges, or an ill-formed instance;
- a simulator that is efficient only because the number of repetitions is bounded by the advice.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/{Language, Machines, Parties, Protocol, ProtocolProofs, Simulator, SimulatorLemmas, SimulatorMachine, SimulatorNumeric}.lean` and the facade `ZeroKnowledge/ThreeColoring.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | pack 03e's files (interaction, ZK definitions, commitments, NP); `ZeroKnowledge/NP.lean` |
| Design record | `briefs/pass-shelat/DESIGN.md` (§2.15 the frozen ch. 4 signatures, with D8; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Thm-124.1, Def-124.a, Claim-124.b–e, Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; graph isomorphism (pack 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (evidence under `evidence/g/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 115 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   21 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 258 prints of every public theorem and lemma in this pack's files:
   252 use only the standard axioms, and 6 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 3 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 20 findings in 10 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes at its head (`evidence-repairs/03ac/replay.log`); each line of
`replay.log` is the newest check of its module. The closure is smaller than at the first staging
because 03a's repair narrowed facade imports (`Randomized` → its three files).

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of every public theorem and lemma of this pack's files;
- admissions: the 3 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **The language and relation** (`R3COL_witnessRelation`, sorried). Is the relation the
   source's: valid encodings, a proper colouring, a polynomially bounded witness? Is its
   polynomial-time verifier claim true?
2. **The protocol (Prot 127.5) and its repetition** (`colRep_efficientProverProof`, sorried).
   - Is the soundness error `(1 − 1/|E|)^{n|E|} ≤ e^{−n}` stated at the right number of
     repetitions?
   - Is the prover's efficiency stated given the witness?
3. **The simulator (Alg 128.7) and `col_zk`** (sorried).
   - Is ZK stated against every n.u.p.p.t. verifier with auxiliary input?
   - Is the truncation (D8's strict simulators) declared?
   - Does the error bound `|x| ε_B(√|x|) + e^{−n}` reduce to the commitment's hiding as the
     sketch claims?
4. **Run-3a's blocker P11-1** (3COL) was repaired. Check the repair.
5. **Thm 124.1** (form (A): ZK for every `(L, R_L)` with an explicit Levin reduction to 3COL).
   Is the headline's dependence on these three `sorry`s, and on the hypotheses of form (A),
   correctly declared?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
