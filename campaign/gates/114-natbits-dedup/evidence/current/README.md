# Gate 114 executed evidence

Lean head: `a02d0531898764d363474fe4d65ccbeff0e7ea5e`. Baseline: `680760723d72826469d0fc294e4d7ee2ecac3e6c`. Both are pinned by Git; the baseline is the complete native `oleans-mac0` tree (894 modules, zero failures). Later maintainer records commits change no Lean files. The replay snapshots are independent copies of that complete baseline, never a composition of PR snapshots.

## Executed checks

- Twenty-two-file source census **2,366 → 2,360**: public source declarations **448 → 449**, private **1,918 → 1,911**. All surviving statements, visibility and order are unchanged. Approved moves/removals and the six authorized public body changes are recorded in the freeze.
- Standalone NatBits plus seven boundary examples pass. The imported seven-example probe and the exact shared Frag cell step under a bufferTape seal pass against the completed PR snapshot.
- The new module has **ten public source theorems, zero private source declarations, and sixteen compiled constants**: the ten theorems plus six internal proof auxiliaries moved from Bin. The complete module axiom walk covers all sixteen; each axiom set is contained in the standard three. The six changed consumer bodies also print only those standard axioms.
- Unfiltered non-private constants across all changed modules: **2,377 → 2,374**. There are four new full source names (the approved namespace move plus three new facts), three removed source names, and four removed internal proof auxiliaries (two from the deleted Codec lemma, two from UniformSample's shortened proof). Twelve constants move modules: six preserved-name source theorems plus their six preserved internal proof auxiliaries. **No new compiler auxiliary is added.** Exact names/kinds/owners are in `axioms/constant-delta.json` and both raw censuses.
- NatBits imports Mathlib only, so it has no foreign TCSlib definition to seal. Its moved theorem names remain visible through Encoding and Bin. The changed Frag step is checked separately; this is not a global seal of legacy consumer code.
- The complete 22-file head / 21-file base screen reports 926 → 923 pairs. The one new in-file near-pair and four removed pairs are dispositioned in `screen/classification.md` under the ledger's convention.
- Independent replay: **344 modules, zero failures and zero static mismatches**. All **68** admitted declarations in that closure match the baseline; none is added or removed.

## Source checks and inputs

The base/head Git exports pass both blueprint checks. Every campaign subtree lint reports zero FAIL; raw warnings and their baseline comparisons are retained. The common-file policy findings are unchanged in count and kind (118 at each revision); NatBits' new module has zero findings. Size alone is not a split/delay driver. Full baseline sources are under `base-source/`; unchanged screen population files have identical baseline/head blobs. Both changed blueprint versions are included as pinned `.tex.txt` evidence, so the mixed bundle does not substitute the campaign's older blueprint.

`landing/`, `freeze/`, `lint/`, `search/`, `screen/`, `seal/`, `axioms/` and `merged-tree/` retain the exact inputs and unmodified outputs. Per-run receipts pin input checksums, source head and snapshot. Historical failed/incomplete attempts are explicitly labeled; they are not successful attestations. Searches enumerate candidates across open campaign PRs, prepared landings and delivery refs, with semantic inspection and classifications; they do not prove exhaustiveness or acknowledge new debt.

The user's updated Mac-wide cap is five; this campaign budgets three slots while the other chat uses two. The temporary replay suspension preserved elaboration state and is documented in the setup receipts. After any Lean merge, reassess validity or replay the combined tree before clearing another PR. These results do not close the external gate.

**Ready to dispatch** once its verified bundle is published. **Not yet clear to merge:** the external audit has not closed.
