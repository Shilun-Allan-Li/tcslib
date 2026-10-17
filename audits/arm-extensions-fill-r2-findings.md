# ARM-extensions fill gate — round 2 findings

**Verdict: OPEN — 0 blockers, 2 majors, 6 minors.**

The pair inventory and the published arithmetic reproduce. The classified scope is **not complete or correctly classified**: an excluded run-composition argument puts `Machines/ARMReach.lean` back above one fifth under the pack’s whole-declaration code-line measure. Further smaller omissions and two false-positive overrides need correction. The user’s acknowledgement is valid for the scope actually presented; it does not accept material explicitly excluded as incidental.

The proposed H7–H13 contracts and the first-use exception substantially answer the architectural question. Registration in the designated canonical document remains unfinished: the supplied `machine-library-design.md` §14 has no H7–H13 and still prescribes the superseded H1/H4 routes.

**Audit date:** 2026-10-14. **Requested destination:** `audits/arm-extensions-fill-r2-findings.md`.

## Scope and evidence boundary

| Item | Scope |
|---|---|
| Governing documents | Round-2 pack, round-1 findings and pack, `audits/TEMPLATE.md`, `policy.md`, `workflow.md`, response, backlog, design and plan |
| Source baseline | All 100 bundled `TCSlib/` files: 73 additions and 27 library files, supplied at `e831b5b0` |
| Evidence | Round-2 inputs, scripts, tables and logs; PR #87 and PR #93 diffs |
| Current-tree qualification | PR #93 was applied to scratch copies of the 32 supplied added files it changes; the existing `ClassPSPACE.lean` facade was checked from the diff. PR #92’s changed source is not supplied. Counts and source locations below remain at `e831b5b0`. |
| Excluded claims | No new Lean elaboration, axiom probe, Git-history verification or certification of the complete current dependency tree |

The bundle SHA-256 is exactly `59c8f436cdbf16f1a155d4f9d0c648e8bbd43e8292f4168d7c5e3e23c494b490`. It has 170 distinct path sections. All four round-2 input-manifest hashes match.

This is the requested repair audit, not a repetition of round 1’s entire mathematical-interface audit. Proof bodies were inspected to identify repeated arguments and check sketch fidelity, not to review tactic correctness. No new false Lean interface was identified.

**Evidence limitation:** the original screen population has 214 files. Of these, 99 are supplied here: 97 match the original manifest byte-for-byte; `PolyTimeBlockLoop` and `Build/CfgRecord` reflect the disclosed subsequent changes. The remaining 115 population files are absent. Twenty-five pair rows have an absent library-side source; all 25 are classified N. Their pair identities can be verified from the supplied screen, but their source-side spans and semantic exclusions cannot be independently certified from this bundle.

For brevity, source paths beginning `Machines/`, `Codec/`, `Logspace/`, `ExpBFS/` or `SavitchARM/` are relative to `TCSlib/Complexity/SpaceComplexity/`. `ClassPSPACE/`, `ClassNP/` and `CircuitComplexity/` are relative to `TCSlib/Complexity/`. `r2/` denotes `audits/evidence/arm-fill/r2/`. Pair identifiers and classes retain the pack’s meanings.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **major** | `r2/scripts/classify.py`; `Machines/ARMReach.lean:197–231` · `arm_reach`; `Codec/Engine.lean:348–402` · `halvCount_loop` | The N exclusions omit genuine library arguments. The corrected scope changes a file’s one-fifth status. | L066 contains the guarded-run concatenation argument of `DblLang.Rch.trans:116–124`, including the endpoint equation, the time split and the translated second segment. It is the same reachability composition already accepted for `MReach.trans`, now inlined. Counting this one pair changes `ARMReach` from zero counted material to 34/158 = **21.52%** whole-declaration code lines. L049 also reproduces the actual `access_width_half` lemma inside `halvCount_loop`, rather than an induction prelude. | Reclassify the genuine composition pairs and L049; assign run composition to ARM-2(a) and explicitly add the halving-width helper to a named payback. Regenerate the declaration/per-file/class/group tables and threshold lists. **Human acknowledgement required for the changed scope**, or remove those copies and remeasure before closure. Retain the distinction between whole-declaration and shared-text amounts. |
| R2-2 | **major** | `machine-library-design.md` §14; `r2/registry-rows.md` | The canonical host registration required by decision 3 and round-1 finding 5 has not landed in the supplied records. | The draft expressly says the maintainer must land its rows. The canonical registry starts at line 3058 and contains only 0 and H1–H6. H1 still says no machine walker was built and points to MIG-22; H4 still says not built and points to MIG-19. The valid exception and future-use gate are in the pack/draft, not incorporated into that registry. | Install H7–H13 with their contracts, consumers, resource clauses, accepted-exception status and gate-before-further-consumer rule in §14; reconcile H1/H3/H4/H6 and the pure kit there. Preserve the already authorized exception. No immediate machine rewrite or new first-use approval is required. |
| R2-3 | minor | Manual ledger; K1, K2, K18; `TQBFARM/Machine`, `SavitchARM/Machine`, `Machines/MARM`, `PathHardRegs` | The size cutoffs omit additional members of acknowledged families. | Both machines define identical parameterized `sbI` and `hvI` blocks: normalized bodies of 57 and 58 characters, below the 60-character screen floor. `MReach.single:203–206` and `MReach.mono:230–232` repeat `AReach.single:91–94` and `AReach.mono:114–116` below that floor. S072–S074 repeat the preimage-oracle answer argument in `orc_init/orc_acc/orc_step`; the 91-character smaller body misses the 100-character G cutoff. | Add the block and reachability members manually, and classify the three oracle pairs as K2/G with a parameterized preimage-answer lemma. State the copy-side convention and rerun totals. These are accounting corrections inside K1/K2/K18; the files are already in the acknowledged over-threshold population. |
| R2-4 | minor | `classify.py` · overrides I082, I083 | Two G overrides identify an input-bit proof that is absent. | `ARMWidthExample.searchLang_mem_PSPACE:281–319` proves an input-**length** oracle fact for the bank `[inputLenLang, P]`. `SavitchARM/Correct.NSPACE_poly_subset_PSPACE:98–129` likewise proves a length fact; its other slots are configuration languages. Neither proves `PathHardRegs.orc_bit`. The 64-character overlaps are indicator/identifier fragments. | Change I082 and I083 to N/X and correct K2’s counts/explanation. Keep the actual length-oracle pairs, including I012/I013/I057/I084/I085. These declarations remain counted through genuine pairs, so removing these two edges does not itself change their present whole-body or maximum-overlap totals. |
| R2-5 | minor | K9/I032; K20/I040, I064 · factoring descriptions | “Cite” is underspecified in two cases and mathematically wrong if interpreted as identifying the two arbitrary-oracle relations. | `Radius` imports `Bridge`, so `Bridge.mem_iff_codeChain` cannot import `Radius.inWin_runWith_of_decides`. `Layout` imports `Parse`, so `Parse.bitsVal_le_of_width` cannot import `Layout.two_pow_bits_le`. I064’s `ExpBFS.stp` reads oracle slot 2 and returns Bool; `SavitchARM.Rel` asserts slot 3 is true. For an oracle true exactly at slot 2, they disagree. | Specify the lower-level homes: move the window lemma to `Bridge` or below, and the bit-length bound to `Parse` or below. For I064, factor the encoded query and parameterize the slot/result view, or supply explicit bank-permutation/specification bridges. Retain G for the repeated query construction, not equality of arbitrary oracles. These repairs preserve feasible ARM-2 factorings. |
| R2-6 | minor | `r2/corrections.md`; plan B2/fills-6; backlog MIG-19/MIG-22; design §12.8/§16b | Several record corrections are still proposals, although the pack says the record texts have landed. | B2 still locates the three theorems in `ConfigGraph` and describes the old route; MIG-19 and MIG-22 remain active language-first tasks. The listed S1b/design and historical-provenance annotations are not incorporated into their named records. ARM-1’s **45-declaration count and acknowledgement are already corrected**. | Apply the remaining named edits, preserving historical decisions and probe files. Add dated annotations for the old probes and the Bonnet design context, and point current probes to `ExpTime`. Rebase the §16b/#92 wording on its merged status; do not present an instruction to regenerate an already merged PR as current work. |
| R2-7 | minor | Copy-screen tooling; `ledger2.py`; accounting descriptions | Round-1 finding 9 is only partly repaired; the character denominator also needs an exact label. | Flattening fixes this run, but the persistent full-path key and review of older collision-prone screens remain deferred. `ledger2.py` adds a declaration’s body characters to its denominator only when its body has at least 60 characters. Thus 421,911 is not all normalized body text in the 73 files: the same parser gives another 17,116 below-floor characters. A4+ nevertheless includes manually selected below-floor numerators. | Finish the full-path-key repair and assess earlier affected screens. Either retain the historical denominator with an explicit “screen-eligible body characters” label, or additionally report the all-body denominator 439,027 and regenerate affected percentages. Do not silently change the acknowledged convention or call the 15.3% figure a literal fraction of all received source code. |
| R2-8 | minor | PR #93 scope/status; round-1 finding 11 | The blanket statement that finding 11 is fixed overstates the diff. | The 42 long lines, 15 headings and two named quantifier-block sketches in added files are fixed. The two `SpaceComplexity.lean` facade lines are not in the diff and remain explicitly deferred in ARM-1. The pack also says “33 of the 73 added files”; the diff actually changes **32 added files plus the existing ClassPSPACE facade**. | Correct the pack’s scope and partial-resolution wording. Repair the two facade lines in the named payback, or record their explicit deferral in finding 11’s disposition. Keep the separately listed residual sketches and misplaced `predB_iff` Main-results entry tracked; they were not repaired by #93. |

R2-1 is a major under TEMPLATE failure mode 5 because it changes the acknowledged threshold population. R2-3 through R2-5 are corrections within acknowledged families, with workable resolutions, and are minors under the same rule. I have not elevated them merely because the refactor has not yet happened. ARM-2’s user-approved coordination-before-brief arrangement is accepted as given; this audit does not invent a new deadline.

## Reproduction of the inventory and measures

I reran the supplied `pairs.py`. Because absent library sources prevent a complete span reconstruction, its scratch source tree contained byte copies of available files and empty placeholders for missing library files. Those placeholders were used only by the span reader. They were not supplied to Lean or used to certify source contents.

Independently comparing unordered keys of the form “repository path plus declaration name” gives exactly the supplied pair set:

| Category | Directed hits | Unordered pairs |
|---|---:|---:|
| Added ↔ library | 169 | 120 |
| Added ↔ added, different files | 144 | 103 |
| Within one added file | 199 | 130 |
| **Total** | **512** | **353** |

All screen hits with an added side are represented. No same-file hits are discarded. For 328 pairs both source sides are supplied and the reconstructed rows agree exactly. The other 25 have absent library sources; their missing span metadata also changes four ordering-based IDs in the scratch output. Classification was therefore rerun using the supplied stable pair IDs, not those reordered scratch IDs.

The unmodified added-only screen, run on all 73 supplied additions under flattened filenames, reproduces the recorded output **byte-for-byte**: 772 declarations, 343 directed hits, 86,671 reproduced characters. `dupnames.py` reports zero same-file same-name groups at its floor; an additional all-size scan also found none.

I also recomputed the screen’s greedy text tiling directly from both supplied sources for all 328 available pairs: all 485 recorded directed shares and source-body denominators match. The other 27 directed hits belong to the 25 pairs with absent library counterparts.

The supplied `classify.py` and `manualtile.py` reproduce `classify.tsv` and `manual.tsv` byte-for-byte. `ledger2.py` reproduces `ledger2-decls.tsv` byte-for-byte and all published aggregate totals. These are reproduction results for the **submitted classifications**, not approval of them.

| Accounting | Declarations | Whole-declaration code lines | Whole-body characters | Maximum shared characters | Prorated shared code lines |
|---|---:|---:|---:|---:|---:|
| A1 | 151 | 3,731 | 108,250 | 42,676 | 1,554 |
| A2 | 242 | 5,642 | 163,343 | 73,896 | 2,707 |
| A3 | 93 | 2,416 | 72,338 | 37,089 | 1,310 |
| A4 | 149 | 3,972 | 117,468 | 64,109 | 2,280 |
| A4+ | 163 | 4,009 | 118,313 | 64,482 | 2,297 |

The per-file over-one-fifth counts also follow from the supplied classification:

| Accounting | Whole-body characters | Whole-declaration code lines | Shared characters | Prorated shared code lines |
|---|---:|---:|---:|---:|
| A1 | 32 | 28 | 14 | 13 |
| A2 | 47 | 44 | 28 | 23 |
| A3 | 21 | 15 | 13 | 11 |
| A4+ | 34 | 29 | 20 | 18 |

The pack’s A4-vs-A1 transition lists agree with its per-file table. The older `ledger.py` totals reproduce; its entire source-span output cannot be independently reproduced with the omitted library sources.

**Measure ruling.** A classified ledger excluding actual incidental matches is the proper policy basis, with A2 retained as the candidate inventory. Neither “at least 200 shared characters” nor a 90% match is a semantic decision by itself. Whole-declaration accounting intentionally includes unrepeated material; maximum-single-pair overlap can miss disjoint repeated fragments; prorated lines are a proxy, not matched physical lines. The “net” import-order original remains an accounting convention. These distinctions must remain explicit.

### The threshold-changing counterexample

The relevant tail of `arm_reach` is:

```lean
refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
rcases Nat.lt_or_ge t T₁ with h' | h'
· exact m1 t h'
· obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
  rw [rrun_add, e1]; exact m2 t' (by omega)
```

This is the complete composition step in `DblLang.Rch.trans`, with a renamed local hypothesis. It combines two finite runs, preserves their endpoint equation, and preserves a predicate strictly before the combined endpoint. A generic guarded-segment transitivity theorem over an iterated step function removes this repeat. The guard may be the register-head bound in `Rch` or the larger `Inv` predicate in `arm_reach`.

The rule must treat this consistently with the acknowledged `MReach.trans` family. L065’s shorter overlap with `Call.runFrom_forall_append` need not become genuine merely because L066 does: the latter is the concrete complete-argument evidence.

Changing **only L066** from N/X to G/A2a and rerunning the ledger gives:

1. `arm_reach` becomes one counted declaration: 34 code lines, 698 whole-body characters, 148 maximum shared characters.
2. `ARMReach.lean` has 158 code lines and 3,971 screen-eligible body characters.
3. Whole-declaration lines: 34/158 = **21.52%**.
4. Whole-body characters: 698/3,971 = **17.58%**; shared characters: 148/3,971 = **3.73%**.
5. A4+ becomes 164 declarations, 4,043 whole-declaration lines, 119,011 whole-body characters and 64,630 shared characters; the whole-line over-threshold count becomes 30.

This is a controlled one-pair sensitivity calculation, **not a final corrected ledger**. Other corrections must still be incorporated. The 34-line numerator follows the approved whole-declaration convention; the demonstrated textual overlap is 148 normalized characters. The pack specifically removed this file from the classified over-threshold list, so the acknowledgement of A4+ cannot be read as accepting its earlier A1 candidate status.

For L049, the embedded statement is exactly
`(Nat.bits (n / 2)).length + 1 = (Nat.bits n).length`.
`halvCount_loop` proves it from `0 < n`; `InputAccess.access_width_half` proves it from `n ≠ 0`. The positive hypothesis supplies the nonzero hypothesis. Promoting the latter and citing it removes the repeated argument. Its small size does not make it an incidental fragment.

## Classification and factoring review

### All 26 named overrides

| Overrides | Ruling |
|---|---|
| S017 | Retain N. `pt_vlen/pt_vwid_lin` compose already available polynomial-time operations for different expressions. The matched closure syntax is not itself a repeated algorithm proof. |
| S047 | Retain N. The two runs instantiate an existing common scan lemma; count the existing abstraction as reuse. |
| I020, I080 | Retain N. Per-machine label case splits discharge distinct `PreS` obligations. Their common finite-case/simplification scaffold does not identify the same transition system. |
| I072–I074 | Retain N for these pairs. The matches are chains of already shared `NSem` step combinators in different control flows. The genuinely repeated guess-loop argument is separately accounted in K12. |
| I009–I013, I042, I043, I056, I057, I071, I084, I085 | Retain G. These restate the input-length oracle answer, including inline copies. The extra bounded-index premise in some consumers is harmless: the unrestricted answer lemma specializes to it. Bank position must remain a parameter. |
| I016, I017 | Retain G. `mvI/dmI` are the same instruction blocks with register count, oracle count and label embedding changed. |
| I023, I081 | Retain G. These are run specifications for the same doubled-move and shift blocks. |
| I082, I083 | Change to N: R2-4. |
| I064 | Retain G for query construction, but repair the claimed factoring: R2-5. |

This accounts for all seven N overrides and all nineteen G overrides. Sixteen G overrides stand as described, two are false positives, and one needs a different contract description.

The 18 library copy-side declarations designated wholly incidental do **not** all pass review. `arm_reach` and `halvCount_loop` fail as above. The available counterparts for the simple polynomial-time closures, prefix induction preludes, `slide_ok_iff`, `cellOf_congr`, and supplied run-equality fragments support incidental treatment. The absent counterparts include all candidates for `lbStep_iterate`, `pt_orB`, `mcompileTM_init`, `marm_run`, `last_tape_run`, `ndtm_runWith_eq_runFrom`, `rawEdge_adjWordE`, and some for `pt_vwid/mrunFrom_eq`. I do not certify those exclusions solely from their table labels.

For a fully source-backed closure submission, supply those 25 pair counterparts or a precise source excerpt for each candidate argument. This is an evidence boundary, not evidence that all 25 are additional debt.

### The twelve undisclosed substantive copies

All twelve named copy-side declarations have supplied counterparts. Their stated largest overlaps reproduce; source inspection supports genuine reused material.

| Copy | Shared characters | Contract / group ruling |
|---|---:|---|
| `ARMWidth.arm_decides_space` | 1,681 | Bank setup, precondition conversion and decision bridge; A2b |
| `MARMTime.marm_dtime` | 1,652 | Same common bridge, retaining the separate counted-time conclusion; A2b |
| `NARMProof.narm_decides` | 646 | Nondeterministic instance through `detPart`; A2a |
| `NARMProof.npre_of_npreS` | 642 | Public syntactic-to-semantic bank-precondition lemma; A2b |
| `NARMProof.narm_decides_space` | 583 | Same bank/precondition core with nondeterministic conclusions; A2b |
| `Codec/Engine.decChain` | 423 | Parameterized chain/stride work with D7; P1 |
| `MARMTime.runFrom_count_eq` | 314 | Extract the windowed tape-code injectivity subargument of `coreCode_inj`; A2a |
| `NARMProof.narm_decides_poly` | 270 | Shared width-reduction argument; A2a |
| `NARMCompile.spaceUsedWith_le_of_ranges` | 240 | Bound the visited-position ranges, with deterministic/choice-run instances; A2a |
| `MARM.MReach.halt` | 233 | Generic guarded reachability/halt composition; A2a |
| `TQBFHardParams.length_lbStep` | 207 | Shared pair-step length helper; P1 |
| `MARM.MReach.trans` | 200 | Generic guarded reachability composition; A2a |

The 314-character entry is a reused subargument, not a claim that the whole configuration-count theorem is copied. A shared bridge must preserve the different deterministic, all-branch nondeterministic, and time conclusions; “one core” is feasible as common lemmas plus typed instances, not identification of those conclusions.

The original twelve have now received a named payback and acknowledgement. R2-1 is about genuine arguments wrongly excluded from the purported complete scope.

### D1–D7, P1+, manual entries and groups

The disclosed D1–D7 resolutions are coherent. D1 replaces equivalent predicates whose conjunctions are grouped differently; it changes public statements, so the already required full gate is appropriate. The 48 `InWin` code occurrences in seven supplied files reproduce. D2/D2h/D3/D5 can be promoted at the common configuration layer; D4 needs its stated colleague coordination.

D6’s range contains **45 private declarations**: 13 definitions, 29 theorems, two abbreviations and one structure, across 712 lines. No use outside that range was found in `TQBF` or elsewhere in the supplied sources. Whole-repository absence remains the log’s attestation. Keeping the public TQBFARM twins and deleting the obsolete private appendix is a real resolution. After #92, the ConfigGraph deletions must be remeasured at the payback base; its eleven-remaining-private-declarations claim cannot be checked against the pre-#92 source as though it were current.

The 15 P1+ pairs represent 13 copy-side declarations and have plausible promotion/move/citation repairs. They cover the input-oracle, canonical-word, pair-index, output-summary, prefix-congruence, repetition, virtual-word and Tseitin helpers described in §3 of the ledger tables. Private source helpers in `QueryReshape`, `Mult`, CookLevin, `InputAccess` and `DAGCircuitSat` must be exposed at their owning/common layer before consumers cite them. The recorded coordination applies; the audit does not grant ownership clearance. M2 is an ordinary Bool specialization of the public polymorphic list lemma and belongs in the accepted payback.

All fourteen supplied manual rows are real: three disclosed below-floor rows, ten M1 rows and M2. M1’s banks differ in order and, for PATH hardness, through `dropIdx`; the right abstraction parameterizes bank assembly/permutation and preimage handling. They are not literal equal constants. R2-3 identifies additional manual members.

The existing P1/P1+/A2a/A2b split follows the user’s decisions. The maximum-class and first-group attribution conventions explain why per-pair and per-declaration counts differ. No second acknowledgement is required merely because already accepted P1+ rows still carry a “proposed” label in builder-era prose.

### All 21 internal/same-file families

| Family | Source-level factoring assessment |
|---|---|
| K1 register kit | Feasible: parameterized instruction blocks and register-record extensionality/tactic support. Include `sbI/hvI`. |
| K2 banks/oracle answers | Feasible with bank-slot/permutation and preimage parameters. Correct I082/I083 and include S072–S074. |
| K3 bridge plumbing | Feasible common bank/precondition core; preserve each bridge’s distinct hypotheses and conclusion. |
| K4 overridden-state compiler bridge | Feasible common `detPart` simulation lemma parameterized by the override behavior. |
| K5 one-step NHalts | Feasible common one-step/continuation lemma; retain the universal branch condition. |
| K6 code languages/deciders | Feasible common decoding and predicate layer. The step language has two code fields, so a mode/arity parameter or shared sublemmas is required. |
| K7 layout runs | Feasible shared layout phase with different field positions and continuations as parameters. |
| K8 parse phases | Feasible extraction of repeated parsing phases with distinct continuation contracts. |
| K9 missing citations | `word_split/validChk_iff` supports citation; the window lemma must move downward first, as R2-5 specifies. |
| K10 MARM loops/steps | Feasible counted-loop, clearing and step lemmas, preserving memory state and count invariants. |
| K11 transfer loops | Feasible source/destination/stride parameters. `ARMWidthExample.d1_loop/d2_loop` should join the existing `ARMLoops` abstraction. |
| K12 IS guess loops | Feasible common bounded guess loop parameterized by target registers and continuation. |
| K13 PATH endpoint phases | Feasible common endpoint-field comparison, selecting source or target field. |
| K14 Savitch tails/push-pop | Feasible common stack/tail transformations with the chosen branch/registers parameterized. |
| K15 register extensionality | Feasible common record-extensionality lemma. |
| K16 TQBF walk block | Feasible common labelled instruction block with continuation parameters. |
| K17 TQBF hardness | Feasible common bound and quantifier-block lemmas, parameterized by universal versus existential quantification. |
| K18 reachability kit | Feasible generic step/guard segment kit; add the small single/mono instances and R2-1’s inlined composition. |
| K19 padding key | Feasible common padding invariant lemma. |
| K20 citations | Feasible after the lower home for the bit bound and the slot-aware query abstraction in R2-5. |
| K21 chains | Feasible as the explicitly accepted D7 stride/chain generalization in P1. |

The supplied family generator reproduces its output, including 45 internal components, 61 same-file components and coverage of every classified S/G edge. A graph component is not itself a semantic family; the table above assesses the proposed shared contracts. This is a source-level feasibility ruling, not a claim that those refactors have been elaborated.

## Host registry review

The following are mathematical restatements of the principal contracts, checked against the supplied definitions and theorem statements.

| Row | Contract and resource check | Consumer / qualification |
|---|---|---|
| H7 ARM | `compile_correct_from` simulates a finite register-program run from an arbitrary seam, assuming the register envelope and real call contracts, and preserves the compiled head envelope. It gives an existential duration, no time bound. The space bridge uses `m*(W+2) + kD*(2*B+1)`. General-width membership requires `1 ≤ S` and an explicit uniform oracle-space bound over all possible virtual lengths. | TQBF, codec, Savitch and PATH-hardness uses are consistent. H8/H9 serve the ND/time customers. The generic form must preserve the oracle hypothesis, not replace it with logspace without the specialized theorem’s assumptions. |
| H8 NARM | For each input there is a common finite abstract branch budget; all choices halt within it and some branch accepts exactly when the answer predicate holds. Compilation supplies one per-input finite compiled budget and the advertised cell bound. | PATH and inductive counting are actual consumers. “Uniform N” means uniform across branches for that input; it is not a single N for all input lengths. |
| H9 MARM | A fixed compiled machine has the stated exponential-in-width/logspace factor times `(P+1)^2`. The memory-count argument concerns one run with true-only writes on the last tape and the stated head bounds. | ExpBFS is the time customer. Equal-cardinality arbitrary memories cannot substitute for nested memories along this run. H3’s different window clock should remain distinct until a contract gate reconciles them. |
| H10 codec | Bounded configurations receive bounded numeric codes; equality recovers the bounded `coreSum` quotient, not arbitrary unbounded tapes. The four languages have logspace deciders. The chain theorem assumes a window covering the input’s space bound and bounds chain length by `configBound`. | All listed customer groups are supported. The classical decoder is a logical witness, not an executable decoding primitive. D1’s retirement of `InWin` is accurately identified. |
| H11 indexed input | The language indicators answer an indexed input-bit query or a length comparison. Bounded decoding and preimage compilation have the stated interfaces. | Direct imports and uses through banks/preimages should be distinguished. `PathHardRegs` reaches the preimage host through its imports. The `vword_whole₁` declaration starts at line 93, not the draft’s 90. |
| H12 growing-window reachability | Reachable-code counts are monotone with radius; equality at adjacent radii supplies closure. For `logSpace ≤ S`, the MARM search yields the stated exponential-time inclusion. | `ExpTime` uses the main result; inductive counting uses the radius/stop machinery. `ISCountGenCorrect` is a transitive user, not a direct importer of an ExpBFS module. |
| H13 customers | Savitch gives the polynomial-space specialization, not the still-sorried general theorem. Inductive counting works with `logSpace ≤ S`; PATH uses bounded walks; TQBF membership validates syntax and walks assignments; hardness places Tseitin existentials after the original prefix. | The draft correctly names second uses inside the delivery. Consequently “one consumer each” and “each with one consumer” should be qualified or removed. The generic reusable pieces belong with the shared rows. |

The “Consumers today are direct importers” blanket label should be weakened to “direct importers and named transitive users,” with those cases marked. These are small precision repairs to the rows to be installed under R2-2, not new architectural blockers.

The H1/H3/H4/H6 reconciliations are substantively right: the received route serves the frozen customer theorems; it does not finish the general evaluator, arbitrary row-graph search, or all future machine-to-formula infrastructure. MIG-19/MIG-22 can be retired as overtaken for their named targets without declaring those general hosts complete. The H3 reconciliation must update “PR #92 open” to the maintainer’s merged status.

**Gate ruling:** the explicit first-use exception and the rule “contract gate before any further consumer is briefed” meet the policy disposition requested in finding 5. No claim of a retroactive pre-consumer gate is needed. What prevents closure of finding 5 is the missing canonical installation/reconciliation, not a requirement to implement every generic form now.

## PR #93 and record corrections

The diff has 33 files: 32 of the 73 additions and the existing `TCSlib/Complexity/ClassPSPACE.lean` facade. Applying all hunks to the 32 supplied files succeeds with exact context. Removing comments and whitespace gives unchanged code in every one. The facade diff adds the five TQBFARM and seven TQBFHard child imports.

Across the 73 additions with this overlay, the listed long-line count falls from 42 to zero; all fifteen missing Main definitions/Main results headings are present. The two quantifier-block proof sketches are added. Besides the two facade lines, ARM-1 explicitly retains sketches for `numVars_le_length_serialize`, `reflTransGen_stepRel` and `nz_run`, and the `TQBFHardVerifier` Main-results entry naming `predB_iff`, which is declared in `TQBFHardBridge`. The claimed “74 of 74” replay remains maintainer execution evidence; this audit did not rerun it.

For finding 6, the new sketch correctly uses `2^(x.length+1)`. It distinguishes the syntax scan from the formula walk: the scan has stack 1 and input-bounded pointer; the walk bounds the stack and its copy by the quantifier length, and input-driven registers by input length. In the original five-bit counterexample, the pointer can reach 5 while the common bound is 64. The invalid bound 2 is no longer asserted. The exact PR text is more detailed than the proposed text in `corrections.md`, but their bounds are compatible.

Finding 7’s replacements are correct: odd length is not a malformedness criterion; the specific malformed words use the true fallback, while the five-bit empty-clause formula is valid and false. The NARM example now names a genuine start-label self-loop. Equal destinations at a different returning label would halt.

Finding 13’s corrected general/specialized width distinction and the nested two-code step-language encoding agree with the source.

For finding 14, the supplied PR #87 diff has the stated SHA-256
`7d9dfcf2ac891da013cd182c80c4cdf14853111a8337cb4b2a08171bd468d3bd`
and ten Lean paths. Its two relevant dependency hunks replace the named sorries with proofs. Reconstructing its five newly added files from the diff reproduces their listed sizes and SHA-256 hashes. The revised statement accurately limits the replay/probe to `733c22b7`, the received code over C1, from the stated existing olean snapshot. Historical commit/blob identity and the complete source/artifact/toolchain correspondence remain attested, not independently reconstructed here.

## Adversarial checks

These checks are source-level arguments and mechanical calculations, not newly elaborated Lean tests.

| # | Challenge | Result |
|---|---|---|
| 1 | Treat an inlined transitivity proof as incidental because its host theorem is much larger. | Fails: L066 contains the complete guarded concatenation argument; R2-1. |
| 2 | Treat a repeated lemma with a changed positivity hypothesis as a harmless prelude. | Fails: L049’s positive hypothesis implies the source’s nonzero premise; promotion/citation removes it. |
| 3 | Cite an unrestricted input-length lemma at a consumer restricted to indices at most the input length. | Works: restriction is specialization. The G overrides for length answers remain justified. |
| 4 | Identify the two step-query relations for an arbitrary oracle. | Fails: choose an oracle true exactly at slot 2; ExpBFS’s answer is true and Savitch’s slot-3 relation is false. |
| 5 | Repair a missing citation by importing the current location. | Fails for I032 and I040 because the proposed source already imports the consumer. Move the helper downward first. |
| 6 | Remove an instruction block by shortening it below the screen floor. | The subtraction/halving blocks remain the same programs at 57/58 characters; manual scope is necessary. |
| 7 | Switch the unit used for a one-fifth decision. | `ARMReach` is 21.52% by whole-declaration lines but 17.58% by whole-body characters and 3.73% by shared characters. The measures cannot be interchanged. |
| 8 | Replace D1’s predicate without considering public statements. | Equivalent conjunctions are not the same term; the pack’s full-gate requirement is appropriate. |
| 9 | Reuse the original zero-quantifier/five-bit formula against the new sketch. | Pointer 5 fits `2^(5+1)=64`; finding 6 is repaired. |
| 10 | Interpret H8’s branch-uniform bound as input-uniform, or H9’s count as a count of arbitrary memories. | Both interpretations exceed the statements. The registry must retain the per-input and per-run qualifications. |
| 11 | Treat a named consumer as proof of a direct import. | `ISCountGenCorrect` supplies a counterexample to the draft’s blanket wording; it uses the stop machinery transitively. |
| 12 | Delete only the seven D6 twins rather than the obsolete appendix. | The actual deletion scope is 45 private declarations; the source/count and updated ARM-1 agree. |

## Ruling on every round-1 finding

The user made the completeness/correctness ruling on the classified scope a condition for closing findings 1–4. That joint condition has not passed. Their original acknowledgements and resolutions are credited below; I count **one** new scope major, R2-1, rather than four duplicate majors for the same failed condition.

| Round-1 # | Ruling | Reason |
|---|---|---|
| 1 | **Still open — joint scope condition** | The disclosed D1–D7 debt now has genuine user acknowledgement and workable named resolutions, including D6/D7. That part is answered. Final closure is held by the incorrect purported complete ledger, R2-1. |
| 2 | **Still open** | The original twelve are now accounted and acknowledged, but `arm_reach` and `halvCount_loop` show that genuine library arguments remain excluded. R2-1 requires corrected scope and acknowledgement or removal. |
| 3 | **Still open** | All 103 internal pairs are enumerated and the major families have accepted ARM-2 resolutions. The common scope condition fails; R2-3–R2-5 also require the internal classification/manual/factoring corrections. Those latter corrections are minors within accepted families. |
| 4 | **Still open** | The original omission of 199 directed/130 unordered same-file pairs is fixed. Final closure awaits the corrected classified ledger, including the same-file oracle members in R2-3 and the joint scope condition. |
| 5 | **Still open — major** | The draft contracts and exception/gate rule are adequate in substance, but the required canonical registration and reconciliations are absent; R2-2. |
| 6 | **Closed** | PR #93’s input-length bound and separate scan/walk explanation fix the false sketch. |
| 7 | **Closed** | The superseding malformed-input and genuine self-loop candidates are accurate. The immutable old pack need not be rewritten. |
| 8 | **Still open — minor** | The corrective text is substantially accurate and the 45-count is fixed, but the named active-record/historical annotations remain unapplied; R2-6. |
| 9 | **Still open — minor** | Labels and this round’s workaround are repaired. Persistent key repair and older-screen review remain outstanding; the denominator clarification is also needed; R2-7. |
| 10 | **Closed** | PR #93 adds all twelve required direct imports. This is a diff/source ruling, not a new elaboration claim. |
| 11 | **Still open — minor** | The added-file repairs are verified; the two facade lines remain deferred. Correct the complete-fix claim and track the remainder; R2-8. |
| 12 | **Closed by explicit disposition** | Decisions 6–7 place M2 in payback and the other helper/namespace moves in ARM-2. This closes the audit disposition, not the implementation work. |
| 13 | **Closed** | The replacement descriptions correctly separate the general and specialized space bridges and show the step language’s extra code field. |
| 14 | **Closed as a provenance-claim repair** | The C1 diff and precise replay qualification are supplied and consistent. No exact-received-tree execution certification is claimed. |

Round-1 rows 15–25 were notes, not unresolved findings. Their original qualifications remain; this repair audit does not convert them into a fresh blanket certification.

## Source counterparts absent from this bundle

These are the 25 N rows whose library-side argument could not be checked. Paths in this table are relative to `TCSlib/Complexity/`.

| Pair IDs | Missing library source |
|---|---|
| L013 | `TuringMachine/Build/Catalog.lean` |
| L014, L096 | `TuringMachine/Build/Loop.lean` |
| L036 | `ClassNP/PolyTimeBlockTests.lean` |
| L037 | `ClassNP/PolyTimePairing.lean` |
| L063 | `CircuitComplexity/PSubsetPPolyConfig.lean` |
| L088, L089, L105 | `ClassNP/SAT.lean` |
| L094 | `SpaceComplexity/Machines/Clean.lean` |
| L095 | `TuringMachine/Build/Embed.lean` |
| L097 | `TuringMachine/Encoding.lean` |
| L098, L106, L108, L112 | `TuringMachine/Robustness/ObliviousSchedule.lean` |
| L099 | `TuringMachine/Robustness/SingleTape.lean` |
| L100, L107, L109, L113 | `TuringMachine/Universal.lean` |
| L101, L102 | `SpaceComplexity/Machines/CallReturn.lean` |
| L103 | `CircuitComplexity/CircuitEvalRun.lean` |
| L104 | `CircuitComplexity/CircuitSatReductionMachine.lean` |

In particular, the claimed Catalog 6255→6235 and Embed 743→750 line drift remains a log claim here; neither source is supplied. It does not affect the verified enumeration of their pair identities.

## Required changes for closure

1. Correct the N/G decisions and manual scope, repair the factoring descriptions, and regenerate the ledger. In particular, retain `ARMReach` in the whole-code-line threshold population unless the copy is removed. Record the user’s acknowledgement of the material scope change and its named payback, or present source changes that remove it. Supply the missing N-pair counterparts if seeking a complete source-backed exclusion ruling.
2. Land the already prepared H7–H13 rows and reconciliations in `machine-library-design.md` §14, with the first-use exception and mandatory contract gate before any further consumer is briefed.
3. Correct or explicitly carry the six minor findings with the concrete dispositions above. Keep the claimed baseline, PR #93 overlay, and later #92 changes distinct.

**Final verdict: OPEN.** The reproduced arithmetic does not validate the semantic exclusions, and a draft registry does not complete the required canonical registration.

