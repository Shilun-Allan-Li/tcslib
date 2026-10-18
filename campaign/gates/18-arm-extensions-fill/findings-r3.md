# ARM extensions fill gate — round 3 findings

**Verdict: PASS — 0 blockers, 0 majors, 2 minors. The round-3 gate may close with L066 recorded as acknowledged debt. This review also discharges the payback's own statement gate, post-merge.**

Audit date: 2026-10-15. Scope: the received round-3 bundle, the 27-file payback attributed to PR #101, its public API delta, the duplication ledger, and the outstanding round-2 findings. This is a source and evidence audit; I did not run Lean. The two minor record corrections below remain follow-up work. They do not change an approved debt family's scope, a threshold population, or a mathematical contract.

## 1. Findings

Paths use the pack's abbreviations: `r3/` means `audits/evidence/arm-fill/r3/`; `payback/` means `r3/payback/`. Lean paths beginning `Codec/`, `ExpBFS/`, `Logspace/`, `Machines/` or `SavitchARM/` are relative to `TCSlib/Complexity/SpaceComplexity/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | minor | `machine-library-design.md` §14, H10/H11 (lines 3085–3086); `backlog.md` ARM-1 (line 756) | Current records still describe parts of the merged payback as future work and retain an obsolete size figure. | H10 names the removed `InWin` and says it “retires” in the payback; H11 calls D7 decided/future and still identifies Engine as a D7 copy. The supplied source now uses `Cfg.InWindow`, `arm_chain`, and `boundedDecodeStride_loop`, with the old customers as instances. ARM-1 says net −938 lines; the 27 patches and `r3/patch-stats.txt` give net **−1,010**. The pack itself alerts the auditor to the two stale registry rows. | Refresh the current H10/H11 and ARM-1 status to the landed #101 state, names and size. Retain the separate “received, ungated; accepted exception” status for the larger host contracts. Preserve immutable historical packs and landing notes. |
| R3-2 | minor | `payback/ledger-map.md` L002/L057; `r3/ledger-r3-tables.md` §2; `payback/scripts/ledger.py:76,131` | Two disposition rows substitute a sibling for the original declaration identified by their pair ID. | Both `pairs3-base.tsv` and `pairs3-landed.tsv` identify L002/L057 as `orc_len` ~ **`QueryReshape.drop_bit`**. The map's original-side column instead says `drop_len`, selected by `ORIG_FOR`; the generated table then labels that substituted pair present at both trees. The actual `orc_len` ~ `drop_len` pairs are new **L3-002/L3-004**. The parenthetical “length sibling” explains the edit, but does not preserve the pair identity. | Keep `drop_bit` and its actual spans in the original-side fields for L002/L057. Describe the additional `drop_len` edit separately, and cross-reference L3-002/L3-004. Correct the generator and regenerated disposition table. Keep the existing N classifications and numeric ledger totals: these are unaffected. |

## 2. Integrity and inventory

The received `arm-extensions-fill-r3-bundle.md` is **5,002,327 bytes**. Its independently computed SHA-256 is:

`b0e9f8f23937abd5e1747b88add2ea58e0cda19b0034eb6a6e10be47607af834`

There are **243 section headers, 243 distinct paths**, and no duplicate section paths. The inventory comprises 100 Lean files, 27 patches, 22 Markdown files, and 94 other evidence/script/log files. The Lean inventory is the promised 73 added files plus 27 library files. I began with the pack, then the supplied standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`) and round-1/2 records.

I extracted section bodies without their bundle fences, reversed all 27 patches with zero fuzz to reconstruct the supplied base files, and replayed the patches forward. The result equals the bundled landed files byte for byte. Of 86 entries in `payback/SHA256SUMS`, **85 are available and match**, including the 27 `tree/` entries checked against their bundled Lean counterparts. The remaining entry, `logs/land.out`, is not supplied. The referenced `BUNDLE-FILES.txt` is also not a bundle section; the section inventory above was counted directly.

The two supplied copies of `copy-text-screen-v3.py` match SHA-256 `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`. These checks establish internal byte consistency. Commit identity, merge ancestry, and equality with the actual Git objects for base `ff4cab18`, PR #101 and tip `3648415c` remain supplied provenance attestations; the bundle is not a Git checkout.

## 3. Ruling on L066 and closure

**Question 1: yes.** The user's confirmation on **2026-10-15** supplies the acknowledgement that the proposed pack still awaited. It supersedes the older round-2 resolution's instruction to remove this particular copy before closure. Under the debt rule, the audit obligation can close by acknowledgement with a named resolution; implementation of the resolution remains outstanding.

The confirmed block is recorded verbatim here:

> **L066, `arm_reach` ~ `DblLang.Rch.trans`, is recorded as acknowledged debt:** class G, family
> K18, group ARM-2 (a); counted in this ledger (34 code lines, 698 body characters, 148 shared;
> `ARMReach.lean` at 21.5% by whole-body code lines). It stays until ARM-2 (a)'s generic
> guarded-run composition lemma, designed with Hydroxyi, lands; `arm_reach` and `Rch.trans` then
> cite it.
>
> *Entered by the builder from the maintainer's round-3 instructions (the user's decision of
> 2026-10-14, backlog §1 ARM-1: "`arm_reach` waits for Hydroxyi"). The backlog row reads "until he
> decides, or until the user acknowledges it in the meantime"; the user confirms this wording before
> dispatch.*

The operative record also retains the pack's named payback: **ARM-2(a), K18**, owned by the user, with the generic guarded-run composition interface designed with Hydroxyi before a brief, followed by a PR and its gate. No calendar date has been scheduled; this review does not invent one. The explicitly accepted dependency and named work item are the resolution plan for this closure.

L066 remains **G / K18 / A2a**, not N, removed, or paid back. Its 34 code lines, 698 body characters and 148 shared characters remain in all three ledgers. In `ARMReach.lean`, 34/158 = **21.52%** by whole-declaration code lines; acknowledgement does not move the file below one fifth. The future change must make both `arm_reach` and `DblLang.Rch.trans` cite the shared composition lemma; the remaining `MReach`/`AReach` work stays in the named reachability-kit family.

L049, the other R2-1 copy, is actually paid back: `access_width_half` is public and `halvCount_loop` cites it. Thus **R2-1 closes as an audit finding**, by implementation for L049 and explicit acknowledgement for L066.

## 4. Payback statement gate

**Question 3: this round discharges the payback's gate. No unfaithful restatement was found.** This is the post-merge gate authorized by the user, not a claim that a gate occurred before merge. It does not discharge the separate contract gates still required for the larger received H7–H13 hosts before further consumers.

### D1: the predicate rewrite

The old `Codec.InWin N s c` requires, for each work tape, a head within radius `s` and every nonblank cell within that radius. `Cfg.InWindow s c` requires all heads within the radius and all cells strictly outside it blank. In mathematical terms the cell clauses are equivalent:

`tape(z) ≠ none → |z| ≤ s` if and only if `s < |z| → tape(z) = none`.

This follows by contraposition and the total order on integer positions; distributing `∀ i` over conjunction gives the head clause in the new form. Here `c` is a configuration, `s` the window radius, `i` a work-tape index and `z` an integer cell position. The conversion neither assumes positive radius nor positive tape count, and adds no restriction on input or output tapes. `Cfg.InWindow.core_bounds` exposes the old hypothesis shape for the existing core-code interface. This is logical/extensional equivalence, not an assertion that the two predicate expressions are definitionally equal.

I independently compared declaration inventories and public types in the reconstructed before/after files, including namespace context. The **28** existing-public D1 changes comprise **23 theorem signatures and five definition bodies**:

| File | Theorem signatures | Definition bodies |
|---|---:|---|
| `Codec/Word` | 3 | `decodeCfg` |
| `Codec/Valid` | 3 | — |
| `Codec/Step` | 4 | — |
| `Codec/Langs` | 3 | `validLang`, `acceptLang`, `stepLang` |
| `Codec/Checks` | 3 | — |
| `ExpBFS/Radius` | 7 | `WinRun` |
| **Total** | **23** | **5** |

All are precisely the stated predicate substitution, modulo whitespace. The two ConfigGraph lemmas promoted while restated are counted among additions, not again among these 28. The API JSON's `public_restated` and `d1_bodies` fields must not simply be summed: they also include promoted declarations and proof-body edits.

The five definition contracts, read from their terms, are:

| Definition | Mathematical meaning and fidelity check |
|---|---|
| `decodeCfg` | Return a chosen configuration within the window whose code is the given code, when one exists; otherwise return `none`. Replacing the window predicate preserves the candidate set and decoder contract. No new assertion of unique raw configurations is introduced. |
| `validLang` | The encoded parameters and code have a witnessing configuration within the specified window. The witness, encoding and parameter order are unchanged. |
| `acceptLang` | Such a configuration is halting and has output summary exactly `[true]`. Neither the halting test nor acceptance output is weakened. |
| `stepLang` | The encoded source and target configurations are both within the window and satisfy the same machine step with the supplied choice bit. Pair nesting, step relation and both window obligations are retained. |
| `WinRun` | Every configuration reached by a prefix of the choice list, including the empty and complete prefixes, lies within the window. The range of prefixes is unchanged. |

No other surviving public statement changes beyond this D1 substitution. The supplied delta introduces no new `sorry`d statement; the 21 existing `sorry`s in touched `TQBF.lean` are unchanged. I have not reopened their earlier correctness gates.

### Additions and removals

The public-name delta is exactly **20 additions and seven removals**. Nine additions are visibility promotions: six ConfigGraph lemmas, `access_width_half`, and the two `DAGCircuitSat` lemmas. The other eleven are new shared interfaces or moved interfaces.

| Public additions | Contract reviewed |
|---|---|
| ConfigGraph: `NDTM.take_succ_action`, `abs_lt_card_visitedWith`, `mem_visitedWith_of_ne_none`, `visitedWith_take_subset` | Preserve the existing prefix-run, visited-position and cardinality facts; only visibility changes. |
| ConfigGraph: `NDTM.runWith_take_inWindow`, `inWindow_of_coreSum_eq` | Preserve the windowed-prefix and core-equality transfer facts under the equivalent predicate. The orientation of the core equality is handled at callers. |
| ConfigGraph: `Cfg.InWindow.core_bounds`, `FinNDTM.DecidesInSpace.mem_of_acceptsWithin`, `outSummary_eq_empty_iff` | The old window shape follows from the new one; an accepting branch of any length implies language membership under the decision contract; the empty output-summary characterization moves unchanged. The arbitrary-time acceptance lemma retains the decision hypothesis needed to handle early/late accepting times. |
| InputAccess: `LogProg.access_width_half`, `arm_chain`, `boundedDecodeStride_loop`, `drop_canon` | Halving width requires a nonzero value; the chain is parameterized by increment/decrement with the respective bounds; the decoder retains positive stride, distinct registers, remaining-length/value bounds and oracle assumptions; the canonical-tail criterion moves unchanged. |
| InputAccess: `indicator_inputBitLang`, `indicator_inputLenLang`, `pairEncode_getD_snd` | Expose the actual bit/length oracle answers and indexing into the second component of the pair encoding. Default values outside the input/component are retained. |
| PolyTimeBlockLoop: `length_pairEncode_drop_le` | Dropping prefixes from decoded components and re-encoding has length at most `max s.length 2`. The `2` covers malformed/default decoding. |
| QBF: `prefixTruth_congr_agree` | Leaf predicates agreeing on assignments with the fixed initial segment give the same quantified-prefix truth. The agreement hypothesis is retained; the old unrestricted congruence lemma becomes a corollary. |
| DAGCircuitSat: `eval_tseitinGates_values`, `values_getD_eq_of_eval_tseitinGates` | Preserve the existing gate-value/Tseitin facts, their circuit conditions and assignment quantification. These are exactly the two cleared visibility edits in `CircuitComplexity/*`. |

The seven removed public names have these replacements:

| Removed name | Shared replacement |
|---|---|
| `Complexity.Codec.InWin` | `Turing.Cfg.InWindow` |
| `Complexity.Codec.outSummary_eq_empty_iff` | `Turing.outSummary_eq_empty_iff` |
| `Complexity.Codec.inWin_runWith_take` | `Turing.NDTM.runWith_take_inWindow` |
| `Complexity.Codec.mem_of_acceptsWithin` | `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin` |
| `Complexity.ExpBFS.inWin_of_coreSum_eq` | `Turing.NDTM.inWindow_of_coreSum_eq` |
| `Complexity.TQBFHard.values_getD_eq_of_eval_tseitinGates` | `BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates` |
| `Complexity.TQBFHard.prefixTruth_congr_agree` | `Complexity.QBF.prefixTruth_congr_agree` |

The patches repoint the supplied users; the name-check log reports no stale use in the complete landed tree. The diff also deletes 64 private declarations, including the 45-declaration `b4m*` appendix, the 11 `s1b_*` declarations and the duplicate `codec_core_window`. `TQBFARM/Semantics` remains the single home for the seven D6 twins. The two `CircuitComplexity` promotions are the only changes in that directory, matching the supplied clearance.

## 5. Ledger and disposition review

I reran classification, manual-row measurement and ledger generation on the reconstructed source states. The resulting classification tables, manual measurements and declaration ledgers match the supplied files byte for byte. I also regenerated the transitions/dispositions and checked the base-to-round-2 and landed-to-tip comparisons. Agreement with the disposition output does not excuse its two identity errors in R3-2.

The normalized screen logs agree with the pair TSVs: **512 directed hits / 353 unordered pairs** at base and **457 / 314** at landed and tip. Base comprises 120 library, 103 internal and 130 same-file pairs; landed comprises 94, 93 and 127. There are **48 removed pairs, nine new pairs and 305 common pairs**.

I independently recomputed source-body sizes, spans and greedy overlaps for **349/353 base pairs** and **310/314 landed pairs**—508/512 and 453/457 directed hits respectively. These include the 26 supplied original-side excerpts: the 25 previously absent N counterparts and L033. All checked measurements agree. The four missing original-side sources are explicitly listed in §8.

| Accounting | Base declarations | Landed declarations | Base whole code lines | Landed whole code lines | Base whole body characters | Landed whole body characters | Base shared characters | Landed shared characters |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| C: all screen candidates | 242 | 218 | 5,657 | 5,241 | 163,343 | 152,089 | 73,896 | 65,685 |
| K: classified, N excluded | 152 | 128 | 4,081 | 3,641 | 119,740 | 108,433 | 64,477 | 56,180 |
| K+: K plus manual rows | 170 | 142 | 4,135 | 3,682 | 120,796 | 109,249 | 65,061 | 56,650 |

The denominators are base **17,268 code lines / 421,911 eligible body characters / 439,027 all body characters**, and landed **17,017 / 414,200 / 431,349**. “Eligible” means declaration bodies of at least 60 normalized characters. K+ at landed is 21.64% of code lines, 26.38% of eligible body characters and 25.33% of all body characters by whole-declaration counting; shared characters are 13.68% and 13.13% of the respective character denominators. Shared-line proration gives about 2,010 lines, 11.81%.

Landed K+ splits into **A2a: 13 declarations, 301 lines, 8,050 body/2,498 shared characters; A2w: 1, 10, 179/66; A2b: 128, 3,371, 101,020/54,086**. No P1/P1+ debt remains in this accounting. A2w is the explicitly deferred G-rep row, not paid-back material.

| K+ one-fifth measure | Base files | Landed files |
|---|---:|---:|
| Whole body / eligible characters | 33 | 28 |
| Whole body / all characters | 31 | 28 |
| Whole code lines / code lines | 30 | 26 |
| Shared characters / eligible characters | 21 | 17 |
| Shared characters / all characters | 20 | 16 |
| Prorated shared lines / code lines | 16 | 12 |

No newly over-threshold file appears between these corrected base and landed ledgers. The tip comparison preserves the same 314 pair identities/hits/classifications and 142 K+ declaration rows, apart from line movement where applicable in library counterparts. This is an independently checked comparison of supplied evidence, not a fresh screen of the unbundled tip files.

The 39 payback-map dispositions agree with the source changes, subject to R3-2's original-side labels:

- **27 pairs disappear:** S030; L003–L006; L009–L012; L016–L017; L024–L025; L038–L043; L045–L047; L049–L050; L052; L054–L055.
- **Five survive as N:** L001/L002/L056/L057 now share citation scaffolding, not a second oracle-answer derivation; L048 shares the stride-decoder application and arguments. The generic arguments have one home.
- **Three retain the user's dispositions:** L033 remains G/G-rep/A2w; L119/L120 remain N/X. The supplied excerpts support L033's substantive repeated argument and the 25 specified N exclusions.
- **Four manual rows:** `InWin` and the duplicate `inWin_of_coreSum_eq` disappear; `synOK` remains while its `b4mValid` twin is deleted; `VWord.getD_drop` cites `List.getD_drop`.

All seven landed overrides are appropriate. In particular, retaining I005/I008 as G is consistent with dropping the four oracle library pairs: I005/I008 compare complete, identical per-machine wrappers for the same bank, so they remain conservatively counted inside the acknowledged family even after their underlying answer proofs are shared.

The nine new library pairs are accounted for. **L3-001–L3-004** are N citation scaffolding. **L3-005–L3-009** are genuine K2/A2b length-oracle arguments exposed against the new shared home; their repeated arguments already existed inline and are not unfulfilled P1/P1+ edits. The available source and new-pair review reveal no new unacknowledged debt family.

These remain heuristic accounting measures. Whole-declaration counting includes nonduplicated surrounding work; the maximum single overlap can miss disjoint repeated portions; prorated shared lines are an estimate, not a physical count of copied lines. No result here proves absence of semantic duplication below the screen's thresholds.

## 6. Round-2 rulings

| Finding | Round-3 disposition |
|---|---|
| R2-1 | **Closed as an audit finding.** L049 is removed; L066 is correctly counted and explicitly acknowledged by the user on 2026-10-15, with the named ARM-2(a)/K18 resolution. Its implementation debt remains. |
| R2-2 | **Closed.** H7–H13 are installed in the canonical §14 registry, with contracts, users, resource clauses, the accepted first-use exception and the gate-before-further-consumer rule. H1/H3/H4/H6 and the pure-kit account are reconciled. H8's bound is per input and H9's count per run; H13's internal second uses are identified. R3-1 concerns post-payback status wording, not a missing registry or new exception. |
| R2-3 | **Closed.** `sbI`/`hvI`, `MReach.single`/`mono` enter the manual accounting; S072–S074 are G/K2/A2b. The added members stay inside the acknowledged families and do not create a new approval scope. |
| R2-4 | **Closed.** I082/I083 are N/X. Their shared text does not establish an input-bit argument; genuine length-oracle pairs continue to count the relevant declarations. |
| R2-5 | **Closed at the factoring-plan level.** The lower homes below are importable on the supplied graph and preserve the distinct contracts. The actual ARM-2 factorings remain future work. |
| R2-6 | **Closed.** B2/fills-6 and the ARM plan row are corrected; MIG-19/MIG-22 are retired for their overtaken targets; §12.8/§16b and Bonnet provenance are annotated; historical probe files are preserved with the current-import correction recorded. The separate new size/status drift is R3-1. |
| R2-7 | **Closed on the supplied repair evidence, with replay limits in §8.** v3 uses full paths plus source occurrence for identity, fixes same-name self-pair suppression, and the supplied older-screen assessment addresses affected populations. Both character denominators are correctly labelled and recomputed. |
| R2-8 | **Closed.** The #93 scope is correctly stated as 32 added files plus the existing ClassPSPACE facade. The payback wraps the two SpaceComplexity facade lines, supplies the three named sketches, and corrects the misplaced `predB_iff` entry. |

For R2-5, ConfigGraph is a valid lower home for I032's window result: Bridge already reaches it through its codec dependencies, while Radius imports Bridge. Parse is a valid lower home for I040's length bound because Layout imports Parse. InputAccess is below the users for I064's common encoded query. The factoring must parameterize the oracle slot and result view: ExpBFS uses slot 2 and a Boolean result, Savitch uses slot 3 and a proposition asserting truth, and PathHard has its nested slot-4 host query. An oracle true exactly at slot 2 still separates the first two relations. The proposed shared query does not identify those arbitrary-oracle relations.

## 7. Adversarial checks

The following are concrete source/statement checks, not claimed Lean executions.

| Check | Result |
|---|---|
| Zero tapes and radius zero in D1 | With zero tapes both predicates are vacuous in the same way. At radius zero both constrain heads/nonblank cells to position zero. Strict outside versus non-strict inside has the correct boundary. |
| `WinRun` with the empty choice list | The sole prefix still requires the initial configuration within the window. The rewrite does not turn the condition into an empty universal. |
| `arm_chain` with zero steps, and decrement at its bound | Zero steps uses reflexive reachability. Decrement retains `k ≤ v r`, preventing truncated subtraction from concealing underflow; increment retains the endpoint bound. Other registers are framed. |
| Decoder with zero remaining length; stride one; zero stride | At zero length the loop exits without an out-of-range bit query. Stride one is the former bounded decoder's specialization. Zero stride is excluded explicitly by positivity; register-distinctness and value/width bounds remain present. |
| Half-width lemma at 0 and 1 | Zero is excluded by the nonzero hypothesis. At one, the result reduces to the width of zero plus one, matching the width of one. L049 now invokes this shared lemma. |
| Oracle answers at empty input and at the exact end | The bit answer uses its false default outside the list; the length answer is false at index equal to length, including index zero on empty input. Sharing the answer theorem preserves these cases. |
| Pair indexing and malformed decoding | Second-component indexing retains offset `2 * u.length + 2` and the default beyond the component. For an empty/malformed encoded input, the length lemma's `max length 2` covers the default re-encoded empty pair; replacing it with plain input length would fail. |
| Prefix congruence at index zero and with no quantifiers | At zero the agreement requirement covers all assignments. With no quantifiers the claim is the leaf agreement at the current assignment. Updates beyond the fixed prefix preserve the required agreement. |
| Copy surviving after a rename or promotion | Reversed/forward patches, declaration inventories, new pairs and manual rows were checked together. The core-window conversion is centralized and `codec_core_window` deleted; the D6 public twins remain but their private appendix disappears. No additional surviving copy was found in that inspected scope. |
| Citation override concealing an argument | L001/L002/L056/L057 and L048 contain shared applications, whereas I005/I008 retain full matching wrappers. The differing classifications do not hide a new general proof. |
| Denominator-dependent threshold | At base, TQBFARM/Machine and TQBFHardSemantics cross one fifth by whole-body eligible characters but not all-body characters. At landed, SavitchARM/Machine still crosses the shared-character threshold only with the eligible denominator. Both lists preserve the distinction. |
| Ownership and import-cycle trap | The only CircuitComplexity edits are the two expressly cleared promotions. The lower-home choices avoid the forbidden Bridge→Radius and Parse→Layout imports; I064 retains slot/result distinctions. |

## 8. Evidence checked and limits

**Executed independently:** SHA-256 and section enumeration; patch reconstruction/replay; available payback manifest checks; public declaration/type comparison; source/excerpt overlap and span recomputation; classification/manual/ledger regeneration; transition and tip-equality checks. I also ran the supplied, unmodified v3 screen over all **73 added files**, sequentially, on both source states. It returned **772 declarations / 343 directed hits / 86,671 shared characters** at base and **757 / 325 / 84,230** at landed. After path-label normalization, those internal/same-file hit multisets equal the supplied evidence.

**Reviewed supplied evidence:** the 13 round-3 logs and relevant generators; the screenfix and v3 notes; the payback's patches, API JSON, landing notes, replay order and 11 listed logs. The v3 source identifies declarations by normalized path and source offset, disambiguates repeated names, and excludes only a true self-pair. The notes report regression/mutation controls and the older-population review; those historical executions were not repeated here. In particular, the CfgRecord anonymous-instance pair is explicitly treated as an accepted idiom, rather than silently omitted.

**Lean was not available:** no `lean`, `lake` or `elan` executable, complete source checkout or replay snapshot was supplied in this environment. I did not elaborate the patches or run an axiom probe. `payback/logs/verify.log` reports **60/60**, including successful cuts for 27 touched modules and four consumers, unchanged `sorry` counts, 990 printed declarations with no new axiom dependency, negative controls, name checks and the authorized API freeze. These are supplied evidence, not my kernel verification. The expanded 38-module facade cut fails with the same 76 `Mem` errors before and after; it is an artifact control, not positive compilation evidence. The 119/119 replay is recorded in the backlog; its full raw replay output and snapshot are not bundled.

**Source coverage limits:** only **99 of the 218 screen-population files** are supplied in full; the hundredth bundled Lean file is outside that population. I therefore could not independently discover all library-side hits or rerun the entire three-tree screen. Four carried N pairs still lack their original source bodies in this bundle: **L058 `clGroups_index`, L090 `clLeft_until`, L091 `clCmp_forward`, L092 `clA5Stop_clean`**, all in `CookLevin/Hardness.lean`. Their measurements/classifications rely on the supplied tables and prior round's source review. The 25 requested N counterparts and L033 are supplied as excerpts and were checked. Several original pipeline dependencies, including the earlier B6 cutter and MIG-1 declaration scanner, are also absent; running the complete landing harness here was not possible.

These limits do not reveal an unresolved blocker or major in the submitted delta. They limit the verdict to the stated fill/statement audit and the supplied provenance and execution evidence; they do not certify a fresh build, every unbundled module, or all chapter-3/4 theorem contracts.
