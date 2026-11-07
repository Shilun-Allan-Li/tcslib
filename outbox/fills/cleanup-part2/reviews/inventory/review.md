# Post-S2 cleanup J/N: bounded read-only inventory

The named historical and later evidence inputs are now source-key reconciled. This is a source/records inventory for root's brief preparation, not a fresh native cleanup attestation, an issued fill, or a comprehensive library rule-10 audit. No user ruling is needed for this reconciliation.

## Pins and source status

- Post-S2 library: `1aa5506f58f77c215e56d24311ec33bd931cacf1`, TCSlib tree `6ea8b3246478524165b3226c935b12a73853f47b`. Records advanced to `9f054ddda8257376de0a8ce39641b59b4b1b9c82` during review, with this exact library tree. All 1,069 live library sources match their pinned Git blobs; path/bytes/SHA-256/blob identities are recorded.
- Accepted S2: `d8c4cfed793f04062e7e79b78344e5b593ff3ddc`. All five post-S2 owned files are byte-identical to this accepted source. The only library delta from Gate06's checked base `eee107e92a7db11f1f8c98a5c2867304f57ddc54` is those five files.
- Historical inventory source: `3436321ba28042549bead976dc654aab3d661f10` (Gate07 round 2; round 3 changed docstrings only). Gate06's final evidence is pinned separately to `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, which is not incorporated into post-S2 main. The dispatched Gate06 audits do not turn that branch's new readers/repairs into current-main APIs.

## Exact units and dispositions

| Input | Original unit | Current source reconciliation |
|---|---:|---|
| Historical `cleanup-b.tsv` | 764 observations: 265 seal, 446 unfold-list, 53 equation-term | Every row resolved; 754 exact raw blocks, 9 observations in changed blocks, 1 deleted duplicate declaration |
| Historical companion | 468 spelling keys | 424 file + source-qualified declaration keys; 44 alternate-spelling duplicates; zero unresolved or suffix joins |
| Historical keys at current owners | 424 old owner keys | 423 current owner keys, because the removed PublicKeyLemmas copy maps to the surviving Sampling home |
| Gate06 final seals | 110 blocks / 138 diagnostics | All 110 complete recorded raw blocks occur exactly once in post-S2 source; 62 historical keys and 48 additional keys |
| S2 final seals | 5 blocks / 7 diagnostics | All five exact post-S2 blocks; all five historical; no overlap with Gate06's 110 |
| Gate08/S1 conservative observations | 17 blocks | All 17 exact post-S2 blocks; 15 historical and two additional (`IterateFind.polyTimeComputable_find`, `Primality.exists_samplePrime_nuppt`) |
| Gate06 C1 | 142 raw + 10 selected-open supplement | Retain 134 TCS items (131 debt + 3 exact notation exceptions) and 18 Core/Mathlib items; all 152 owner blocks and item lines reanchored by exact raw block equality |
| Gate06 C2 | 10 show observations | All ten remain recorded in existing seal work keys, with exact current line mapping |
| Gate06 C3 | 3 generated-equation pairs | Retain all three actual refs/parents/homes, including the private BlockEncryptor root; no post-S2 term census claimed |
| J core supplement | 4 explicit Function.comp items | All four exact source sites remain; three also occur in Gate06 C1 Core, and one adds MultiMessageLemmas ownership |

The current historical source-row dispositions exhaust all 764 rows:

- **754** retain the complete raw block and are `INSPECT_BEFORE_EDIT`; source equality is not a claim that a fresh sealed diagnostic recurs.
- **1** duplicate source declaration is retired: row 546, PublicKeyLemmas.abs_uexp_sub_le; the surviving public Sampling theorem is at 210–220.
- **7** observations are reader-repair/recheck candidates, rather than newly commissioned rewrites: rows 217, 547, 560, 562, 648, 746, 750.
- **2** observations in a changed proof remain active or unmeasured: row 561 still explicitly names foreign distAdv, and row 745 is its recorded generated distAdv equation reference (not remeasured post-S2).
- **0** rows have a fresh post-S2 native retirement attestation from this review. There is no unresolved source-identity row, but retirement and current elaboration still need root's checks.

| Historical rows | Current owner and range | Disposition |
|---|---|---|
| 217 | Interaction.Strategy.pairFstD_encodeMsgs 143–148 | Old zero-case rfl replaced by public equations; recheck seal, do not rewrite automatically |
| 546, 547 | Sampling.abs_uexp_sub_le 210–220 | Former PublicKeyLemmas duplicate removed; former Sampling private proof public and uses uexp_def |
| 560, 746 | Experiments.abs_sum_sub_le_statDist 152–164 | statDist replaced by statDist_eq; explicit observation addressed in source, old C3 needs reconciliation |
| 561, 562, 745 | Experiments.distAdv_le_statDist 173–184 | uexp items replaced by uexp_def, but explicit distAdv remains; retain its old equation-term observation |
| 648, 750 | Interaction.Protocol.exists_proverCoins_le 534–547 | uexp replaced by uexp_def; explicit repair candidate plus old C3 recheck |

S2 retired **64 private loop declarations** (15 DiscreteLog, 15 ElGamal, 18 RSA, 16 Rabin), verified by exact old/current source keys. None matches a historical 764 observation key. These copy retirements are a separate unit and subtract **zero** rows from the historical inventory. The five S2 inherited failures remain at Concrete.primesPairEquiv_apply_val 340–344; DiscreteLog.ExpGroupGen.FullLength.exists_fullLengthExcept 440–445; RSA.rsaTrapdoor_oneWay 2028–2029; Rabin.rabinCollection_index 1216–1219; Rabin.rabinBlumTrapdoor_index 2942–2946. Existing public interfaces include negligible_iff, Collection.index_eq and TrapdoorCollection.oneWay_iff. The Concrete proof still explicitly names the Mathlib definition Equiv.subtypeProdEquivProd: Core/Mathlib explicit lists must be included in the new review, even when the historical text scanner did not see them.

## Work ownership and deduplication method

Schedule by **current source owner path + source-qualified declaration**, not diagnostic line, unqualified suffix, or the raw TSV count. Each work unit retains every original observation ID, channel, target/ref and original revision; current complete block range and SHA-256 are attached once. Private C3 actual Names stay verbatim, with the exact module/numeric-private prefix joined to the unique private source declaration. This is a source identity join, not reconstruction of Lean Names for elaboration.

The bounded observation union is:

`423 historical current owners + 48 Gate06-only seal owners + 2 Gate08-only owners + 24 further TCS C1 owners + 11 further Core/Mathlib C1 owners + 1 further J-core owner = 509 declaration work keys / 72 files.`

C2, C3, and S2 add zero keys after these unions. All three notation observations stay in the records, and their owners also have other debt; no file or failing block is excluded. The 509 is an inspection/scheduling count, not 509 independent failures or proof fills. The four owner units containing only the retirement/repair candidates must be reviewed before editing.

`final-canonical-work-units.json` is the observation-preserving key table. `ownership-union.tsv` supplies all 509 refreshed declaration ranges; `final-ownership-files.json` groups the 72 files. `combined-ownership-files.json` adds the named deferred design endpoints and flags all **18** paths also modified by pending Gate06 PR #232. Give each path one owner; compare/reconcile that pending branch before any shared-home API addition or later merge. A library freeze/rebase is a maintainer coordination matter; no new dependency on Gate06 closure or user ruling is inferred.

## Deferred N groups: existing work and source gaps

`N-deferred-groups.json` gives each named declaration's exact current file, range, visibility and block hash, and separates consumers from providers, optional items and already-resolved aliases. It names 20 consumer files; seven extend the 72-file observation union (79 potential consumer files). Including every optional/provider role gives 83 named files. These are candidate ownership sets, not a final issue-time edit scope; the proposed shared StateLoop owner is an additional existing file, and a chosen new lower home can extend it.

| Group | Concrete post-S2 work / constraint |
|---|---|
| G7 | Language.statClose_sampleEdgeIdx still has local h2 at 430. Repoint via Sampling.two_pow_size_le_two_mul (407). Permutations.two_pow_permBits_le (452) and the HardCoreGL/Encoding +1 pair persist; keep public statements and make one +1 form a corollary. |
| G10 | Three public castLE proofs, DiscreteLogHardcore.dlb_cut/dlb_guess_pushesUniform and MultiMessage.pushesUniform_comp_injective remain. Generic HardcoreBit.pushesUniform_restrict (219) requires Nonempty O. The older Fin(q+1) theorem has a valid empty-O branch at 239–244; preserve it and do not add Nonempty O to its public header. |
| G13 / DL-9 | Concrete's blockPos/injectivity/window family and the named ColZK/ColRep/Factoring/OneWay/Primality/Ensembles/MultiMessage window copies remain. S2 did not retire these. Merge their ownership with item A/DL-9 and design the existing low shared home/readers before replacing private definitions. |
| G14 | Table index lt/inj remain; the finProdFinEquiv route is optional and must preserve index order j+k*i. Do not turn it into an automatic mandatory proof fill. |
| G18 | No uexp_le_of_statClose exists. Rabin.rabin_uexp_le (1641), RSA.rsa_uprob_pi_eval (1893) and rsa_step_ii (1906) persist. This needs an honest shared average contract/proof, not a name-only replacement; preserve quantitative and empty-type behavior. |
| G22 | DiscreteLogHardcore.dlb_stateIterate_poly (1114) and public HardCoreLoops.polyTimeComputable_stateIterate (70) persist. Move/reuse the existing generic contract at Complexity/Randomized/Build/StateLoop, checking its dependency closure; no private traversal host. |
| G23 | dlb_count_ofFn (1946) and HardCoreGL.count_true_ofFn (75) persist. Existing List.count_ofFn in Programs/Util/List (396) may avoid a new proof or low-home copy; check its exact specialization/imports first. |
| G25 | **Citation direction in the draft is cyclic:** ColZKMachine imports SimulatorMachine at 7, so reply_poly cannot import/cite upward to ColZKMachine.polyTimeComputable_next. Choose a lower shared lemma home or a valid reverse derivation. field_encodeMsgs at 142–144 is already a term alias to ColMachines.getD_eq_pairFstD_iterate; no copied-proof fill remains there. The design still leaves distAdv_seed_to_coins pending sunglassRed's missing public equation. |
| G12 | Both differently stated public four-move lemmas remain; centralization is optional, not a duplicate-deletion obligation. |

A bounded extra source observation arose in the G25 provider review: Indistinguishability.distAdv_sunglassRed explicitly unfolds foreign distAdv at 133; its published distAdv_def reader exists in Experiments at 102. This site lies outside the prior Gate06 54-file scan and outside the 509-key input union. It is recorded separately in `source-gap-observations.json`; it is not silently added to old counts or presented as a full scan of that file.

## Exact method and remaining verification

Read-only Git operations used were `git rev-parse HEAD`, `git rev-parse <rev>:TCSlib`, `git ls-tree -rz <post-S2> -- TCSlib`, `git show <rev>:<path>`, and `git diff --name-only <base> <Gate06> -- TCSlib`. Own standard-library Python ran as:

```text
python3 -I .lake/ps-maintainer/cleanup-part2-prep/review-inventory/source_inventory.py
python3 -I .lake/ps-maintainer/cleanup-part2-prep/review-inventory/reconcile_inventory.py
```

These are completed own data-only passes, not suggested native commands. Their output guards use exclusive creation; rerunning them in this populated directory intentionally refuses overwrites. The saved tools are hashed in the delivery manifest. No received code was imported or executed. The first local lexical table missed nine declarations with same-line @[simp] attributes; retained early artifacts are superseded by the complete v2 joins and `final-*` outputs, which are the authoritative inputs to this report. No failed Lean run is involved.

The parser masks nested comments/strings while retaining offsets, recognizes source namespace/section scopes, root qualifiers, modifiers and same-line attributes, and joins only an exact declaration spelling or exact canonical source name. All historical joins resolve; 110 Gate06 + five S2 recorded raw SHA-256 blocks and all 17 Gate08 blocks were independently located at current owners. Every C1/C2 line is transported only after exact owner-block equality. All 1,069 live source blobs were fingerprinted and verified against the post-S2 Git tree. The parser is not Lean's AST and does not certify generated/public/private elaborated Name identity outside the separately retained actual C3 metadata.

Before issue, root should pin the final ownership/base after coordinating the 18 Gate06 overlaps; retain every row and make retire/inspect/repoint statuses explicit; record order and base admissions; include all newly touched shared owners and downstream consumers. Only root's serial native process can establish current failures/retirements with a fresh collector, full import-closure seals/EOF checks and controls, C3 term supplement, and hardened explicit-list review including Core/Mathlib and explicit abbrevs. Native replay/axioms/style/header checks must match that final source. Existing examples and same-source bytes are evidence inputs, not a substitute for these checks. This report does not prepare or dispatch the Claude job, alter the inherited inventory, or assert gate closure.

**Not yet clear to merge — cleanup is inventory/preparation only; the user-dispatched fill and its verification remain.**
