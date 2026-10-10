**Retrofit epoch R1 — round-2 external audit findings**

**Verdict: gate remains open — 0 blockers, 2 majors, 1 minor, 8 notes.** R1-1 is closed. R1-2 is not closed: the new ledger has inconsistent arithmetic and omits demonstrable copies. R1-3 and R1-4 are closed by the recorded errata, independently confirmed below. No Lean statement defect or unauthorized public change was found.

Target: the packet’s `fb721402` snapshot, relative to its recorded base `5588628c`. Evidence: this supplied bundle only, including its 16 attachments. Independently computed bundle SHA-256: `6902983404d5563980943e2795d21fb786acc563b5dcec31cf3e4c96ddd0b819`.

I reconstructed every intermediate target-file state, replayed all 46 hunks in both directions without offsets or fuzzy matching, recomputed the Git blob hashes, and compared the complete public declarations and their attached documentation. I also enumerated declarations with comments excluded, checked the dead sets against references from surviving declarations, reconstructed inventory membership, and compared the omitted duplicate families directly. Kernel checking is the commissioned premise; I did not rerun Lean or independently authenticate repository commits or merge events.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **major** | `audits/duplication-ledger.md:10–18, 30–34` · counting convention and Catalog partition; R1-2 | The cumulative ledger still has no consistent, independently verifiable Catalog total. | The printed summands total **261**, not 249. Its Primitives partition accounts for only `143 + 3 + 1 = 147` of the historical 150 counterparts, omitting the three strengthened split-closure counterparts. Conversely, the Loop count includes its two strengthened counterparts despite the stated byte-level rule. Keeping all historical correspondence members gives a **conditional** total of 264, not 249; strict normalized twins give a different total. Catalog and Wrappers sources, the full pair manifest, and the cited A2/F2A reports are absent. Thus 423, the dead/sole-owner labels, the Wrappers denominator, and the Catalog line estimate cannot be independently reconstructed. | Define one inclusion rule; enumerate each distinct member and counterpart, including strengthened, deleted-original, and internal pairs; regenerate totals and fractions. Supply the pinned Catalog/Wrappers sources or an auditable complete correspondence with the necessary source evidence. Do not repair this by changing 249 to 261 alone. Existing D-R2 acknowledgment remains credited. |
| R2-2 | **major — debt / incomplete accounting** | Ledger `:19–24, 30–35, 44–48` · relocation family and Loop H3 | The excluded relocation “reimplementations” include exact copies, and the Loop row omits known internal copies. The packet does not establish a cleanup owner/window for the full relocation family. | After only the four corresponding identifier substitutions, **all four complete relocation declarations, including docstrings, are byte-identical** across Loop, Primitives, and Hardness; the exact map is below. This directly refutes “not byte-level copies,” Primitives’ zero copy-side count, and Hardness’s zero cross-file count. Separately, 13 H3 declarations equal their Loop originals after renaming and comment/whitespace normalization; the fourteenth has one extra simp entry. D-R3 acknowledges H3, but acknowledgment does not remove its members from the current ledger. D-R1 commissions prerequisite exports; D-R2 explicitly leaves Hardness outside 12.2c. Neither supplies an explicit cleanup assignment/window for all three copies of this relocation family. | Include these families and count each declaration once per file. Carry forward D-R2/D-R3 without renewed approval. For the omitted relocation debt, provide an existing acknowledgment that covers the exact family and names its cleanup owner/window; otherwise **human acknowledgment required**, with that owner/window. Do not label exact copies as non-copy design harvest. |
| R2-3 | **minor** | Ledger `:37–42` · epoch delta | The phrase “twelve dead originals deleted” is false. | The twelve removed historical-map members are eight dead Loop declarations, three dead Primitives split orphans, and the **live** `catalogPair_inverse`, removed after replacing its uses. The count `245 − 12 = 233` is correct. | Say **eleven dead originals plus one original eliminated by replacement**. Retain the independently verified epoch-wide distinction, 76 dead + 7 replaced. |
| R2-4 | note — no findings | Three complete finals and patch series · R1-1 reconstruction | The source-reconstruction part of R1-1 is fully repaired. | All 46 hunks reverse-apply exactly; forward replay recovers the attached finals byte-for-byte. Every old/new patch-index hash matches recomputation, including the full RB2 hashes. All eight Loop and five Hardness complete public declarations are unchanged. Primitives is 18/18 unchanged before E1 and 17/18 afterward. | Close this part of R1-1. |
| R2-5 | note — no findings | `catalogPair_inverse` / `Turing.eq_pairEncode_of_pairDecode` · R1-1 E1 comparison | The universally quantified statements are identical up to bound-variable renaming and binder presentation. | The common type is displayed below. Namespace inspection finds the same `Turing.pairDecode` and `Turing.pairEncode`, with no extra section variables, typeclass requirements, or assumptions. E1 changes exactly the one invocation in `computesFunInTime_stripLast`; its statement and documentation are unchanged. | Close the remaining part of R1-1. No additional E1 approval is needed. |
| R2-6 | note — no findings | Plan §4d decision log · R1-3/R1-4 | Both recorded errata are correct. | Independently counted: 83 removed privates and 1,639 removed lines; `catalogPair_length` occurs once among the removals. The public inventory is 8 + 18 + 5 = 31. All 31 statements/docstrings and 30 complete declaration texts are unchanged; the exception is precisely E1. The later decision-log entry qualifies the historical 18/18 attestation. | Close R1-3 and R1-4; preserve the historical pack with its explicit correction. |
| R2-7 | note — no findings | Three batches · R1-5/R1-6 | Ownership, deletion boundaries, and retained pending-consumer material remain compliant. | No declaration is added. All 83 removed declarations are private. For the first-patch dead sets, no surviving declaration references any of the 8/62/6 removed names after comment stripping. The seven further removals have their consumers redirected. The live `emCall`, H3, compare/erase/relocation, and Hardness reader/wipe families remain. Only `Build.Seam` is added to imports. | Carry R1-5/R1-6 as no findings. |
| R2-8 | note — no findings | Loop H4 · R1-7 | The forwarding replacement remains a strict simplification. | The two local lockstep lemmas disappear; the retained caller cites `leftCfg_run` and `Turing.emit_run` with local padding/configuration glue. This patch removes 35 net lines. `emLoopForwardCfg` remains used by the caller’s statement and the commutation fact. | Carry R1-7 as no findings. |
| R2-9 | note — no findings | Hardness `clFresh*` and strict swaps · R1-8/R1-9 | The seam preserves the displaced stream head, and the reported replacement sites are exact. | `clFreshTM.tm` is the stated `seamCompTM`; the `run_ofCfg` call passes the wipe endpoint and first-return cut directly to the reader at the retained cursor. `clFresh_idle` and `clFresh_first` are byte-identical. The replacement patch has exactly 2 composition citations, 1 buffer-append citation, and 10 `clNative_fill true` citations. | Carry R1-8/R1-9 as no findings. |
| R2-10 | note — no findings | E1 trail; D-R2/D-R3 · R1-10 | The recorded E1 approval and existing debt acknowledgments remain valid evidence at the packet’s stated level. | The flagged `7224d118` diff joins the agent’s `406229db` state exactly; the plan explicitly associates its approval with the user’s PR #9 merge. D-R2 names the historical Catalog/Primitives/Loop/Wrappers debt and promotes 12.2c to the next window after the retrofit. D-R3 commissions Z5 for H3. | Carry these acknowledgments forward. R2-2 concerns omitted accounting and the additional family’s cleanup disposition, not renewed approval of these decisions. |
| R2-11 | note — no findings | Evidence boundaries · R1-11/R1-12 | Historical kernel/artifact attestations are carried at their original evidentiary level. | The reconstructed Hardness baseline independently contains 553 privates. The artifact-location correction and the clean 31-entry axiom audit remain recorded in the inventories/prior findings; the underlying artifact modules and axiom logs are not attached here. No patch touches or references an environment shim. | Carry R1-11/R1-12 without claiming a new kernel/log replay. |

**Reconstruction and freeze evidence.**

The following are independently recomputed Git blob hashes, abbreviated here to the lengths used in the patch headers. The association with the named repository commits remains packet metadata.

| File | Recomputed blob sequence | Line counts at those states | Private counts at those states |
|---|---|---|---|
| Loop | `c33e04c1 → 3e99b317 → dbb41eae` | `5713 → 5550 → 5515` | `214 → 206 → 204` |
| Primitives | `3d969bdf → c1f48adb → 406229db → bf6244f1` | `7636 → 6414 → 6398 → 6374` | `318 → 256 → 255 → 254` |
| Hardness | `a27121c6 → 262e84fc → 830e1c3c → c63b4e7c` | `8904 → 8780 → 8748 → 8725` | `553 → 547 → 544 → 544` |

The independently verified epoch arithmetic is:

```text
Lines:    (5713 − 5515) + (7636 − 6374) + (8904 − 8725)
        = 198 + 1262 + 179 = 1639.
Privates: (214 − 204) + (318 − 254) + (553 − 544)
        = 10 + 64 + 9 = 83.
Dead:     8 + 62 + 6 = 76.
Replaced: 2 + 2 + 3 = 7.
```

The complete declaration comparison includes attached docstrings and intervening closure comments. The sole changed public line is:

```diff
-          rw [catalogPair_inverse x u v hd]
+          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
```

**Literal E1 statement comparison.**

The deleted private lies in `namespace Turing.FinTM`; the public theorem lies in `namespace Turing`. Expanding their explicit/curried binders and renaming the public theorem’s `z, a, b` to `x, a, v` yields the same type:

```lean
∀ (x a v : List Bool),
  Turing.pairDecode x = some (a, v) → x = Turing.pairEncode a v
```

This is equality of the quantified proposition, not merely evidence that a particular rewrite succeeds. The source spellings and proofs need not be byte-identical.

**Independent ledger recomputation.**

I enumerated the 95 Loop core members from the inventory’s F1–F15 member lists and checked their presence in both reconstructed states. For Primitives, F01–F10 contribute 80; F13–F22 contribute 69; `catalogPair_inverse` contributes 1, giving 150. All 150 names exist in the reconstructed baseline. Intersecting these historical maps with the final declarations gives:

| Historical map | Baseline members | Removed members | Surviving originals | Final file declarations | Fraction |
|---|---:|---|---:|---:|---:|
| Loop → Catalog | 95 | Six standalone debit declarations, `loop_silent_prefix`, `loopBody_capture` | `95 − 8 = 87` | `204 + 8 = 212` | `100 × 87 / 212 = 41.0377%` |
| Primitives → Catalog | 150 | `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first`, `catalogPair_inverse` | `150 − 4 = 146` | `254 + 18 = 272` | `100 × 146 / 272 = 53.6765%` |

Thus 87, 146, their rounded 41%/54%, and `245 → 233` are correct **for the expanded historical maps**. They are not complete cumulative per-file totals and are not strict byte-twin totals. The inventories explicitly exclude from exact matching two Loop counterparts (`loopHost_prepare`, `loopHost_contracts`) and three Primitives counterparts (`splitSolve_of_body`, `splitSolve_source`, `splitSolve_closed`). Strict normalized surviving-original counts would instead be 85 and 143.

The Catalog arithmetic exposes the inconsistency step by step:

```text
Printed partition: 143 + 3 + 1 + 87 + 8 + 17 + 2 = 261.
Printed numerator: 249 = 143 + 87 + 17 + 2.
Difference:        261 − 249 = 12.
```

The omitted 12 are precisely the printed `3 + 1 + 8` historical-copy categories. Additionally, the Primitives partition should contain all 150 historical members under the expanded convention, whereas its `143 + 3 + 1` contains only 147.

Assuming the packet’s remaining source counts and disjointness claims, the two consistent alternatives would be:

```text
Expanded historical correspondences:
  150 + 95 + 17 + 2 = 264; 100 × 264 / 423 = 62.4113%.
Strict normalized historical twins:
  147 + 93 + 17 + 2 = 259; 100 × 259 / 423 = 61.2293%.
```

These are **conditional reconciliations, not certified Catalog totals**: the Catalog/Wrappers sources and the complete internal/copy-side maps are missing. The source evidence is also insufficient to decide whether the three orphan counterparts are live sole owners or dead, or whether the inverse counterpart is dead. Those labels require the Catalog reference graph. Wrappers’ “small” supplies neither a denominator nor a reproducible fraction. The approximately 6,000/450 line claims likewise remain attestations.

For the attached original-side blocks, an explicit span count—attached docstring and intervening closure note through the last code line, excluding separating blank/module-note blocks—gives **2,009 lines for the 87 Loop members** and **3,162 for the 146 Primitives members**. Different block-attribution conventions can change these counts; the ledger should state the rule that produces its approximate 2,350/3,300 figures.

**Omitted families verified from the full sources.**

Every row of this map is identical across its three files after replacing the four family identifiers consistently. Even whitespace and docstrings then match.

| Loop declaration | Primitives declaration | Hardness declaration |
|---|---|---|
| `emCallAction` | `emitterP2Action` | `clSlotAction` |
| `emCallCfg` | `emitterP2Cfg` | `clSlotCfg` |
| `emCall_apply` | `emitterP2_apply` | `clSlot_apply` |
| `emCall_relocate_run` | `emitterP2_relocate_run` | `clSlot_run` |

The blocks occupy Loop lines 3520–3595, Primitives 4699–4774, and Hardness 1803–1878: **73 declaration/docstring lines per file**, excluding the three inter-declaration blank lines. This is one four-declaration family with two later copies, not three unrelated reimplementations.

H3’s exact normalized copies have suffixes `fuel_capture`, `input_rewind`, `fuel_rewind`, `fuel_copy`, `fuel_return`, `fuel_setup`, `prepare`, `release`, `borrow_step`, `borrow_run`, `borrow_rewind`, `borrow`, and `reject`, mapping `loopHost_*` to `emLoopHost_*`. The `init` pair differs only by the added `loopHost` simp entry. The H3 originals already belong to the 87-member core map and must not be counted again; the copied declarations are additional members.

Keeping the ledger’s expanded-map convention and adding **only** the omitted exact families verified above gives these lower bounds:

| File | Distinct members after these corrections | Fraction |
|---|---:|---:|
| Loop | `87 + 4 + 13 = 104` | `100 × 104 / 212 = 49.0566%` |
| Primitives | `146 + 4 = 150` | `100 × 150 / 272 = 55.1471%` |
| Hardness | At least 4 | `100 × 4 / 549 = 0.7286%` |

The alternative strict-normalized counts would start at 102/212 and 147/272 for Loop and Primitives. Neither version counts the near-copy H3 `init`, other semantic reimplementations, or unseen counterpart material. These lower bounds demonstrate why the current ledger cannot be accepted as complete.

D-R2’s scheduled Catalog deduplication and D-R3’s H3 acknowledgment are substantive and remain accepted. The repair needed is accurate current accounting plus a documented cleanup disposition for the omitted relocation family. No source changes, renewed E1 permission, or renewed approval of already accepted Catalog/H3 debt are required by this report.

Glossary: In the common Lean type, `x` is the encoded Boolean list, and `a` and `v` are its decoded components. Other identifiers are existing source declarations or recorded audit labels.
