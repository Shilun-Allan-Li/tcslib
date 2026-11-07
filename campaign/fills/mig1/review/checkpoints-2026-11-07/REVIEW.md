# MIG-1 cp01/cp02 incoming checkpoint review

2026-11-07. Internal review by Codex. **Not yet clear to merge.** Both are explicitly
partial, cumulative checkpoints from the still-running fill. Receipt and static freeze pass;
F-A is proof-filled in cp02, but its rule-10/API boundary remains unresolved. This review
does not accept the fill, close a gate, or certify any elaboration.

## Independent receipt and source checks

Pinned Lean base: `83ac315ed9e7089466bd16a32f3b71fbadc556d2`, read from dispatch.json and
verified locally with `git rev-parse` / `git cat-file -e`. Original ZIPs and reports are
preserved verbatim. [receipt.json](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoints-2026-11-07/receipt.json)
and the two inventories record archive sizes, hashes, safe names, lengths, and extraction.

| Check | cp01 | cp02 |
| --- | --- | --- |
| ZIP bytes | 601,718 | 908,155 |
| Regular payloads, including manifest | 213 | 429 |
| Supplied checksums independently verified | 212/212 | 428/428 |
| Changed owned source files | 2 | 5 |
| Changed public proof bodies | 11 | 22 |
| Public declarations in all eleven files | 357 | 357 |
| Remaining source admissions | 16 | 11 |

No duplicate normalized paths, unsafe paths, symlinks, output collisions, CRC failures, or
uncovered payload files were found. Every extracted `.lean` filename has an added `.txt`
suffix; no actual `.lean` file exists in this review folder. Payload scripts, Git bundles,
and patches were never executed or imported. All Python ran with `python3 -I`.

Independent comment-aware, delimiter-depth comparison of all eleven owned files found no
surviving public header/name/visibility/home/order changes and no public definition-body
changes. Witness tables therefore remain unchanged. This checks complete headers, including
binders containing `(input := x)`. The only import change is cp02's already approved
`Mathlib.Algebra.BigOperators.Fin` in Simulation. WordSize and the other five unaffected files
remain byte-identical to base. Results and exact source diffs are in
`source-comparison.json`, `cp01-source.diff`, and `cp02-source.diff`.

Each textual patch series was reconstructed independently in memory from the pinned base,
checking every hunk/context exactly. The result equals every supplied source snapshot;
only owned paths are patched. cp02 preserves the first commit's patch contents; its
`[PATCH]` to `[PATCH 1/2]` subject wrapping is the sole first-patch difference. cp01 to cp02
changes only Simulation, Wrappers, and TimeConstructible. Bundle headers agree with the
pinned prerequisite and delivered HEAD metadata; pack objects were not imported or checked
as Git objects. See `patch-consistency.json`.

## Findings requiring follow-up

1. **Confirmed: configuration readers are missing, as disclosed by E1.** Composition
   [734](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoints-2026-11-07/cp02/fill-mig1-mega-cp02/source/TCSlib/Complexity/TuringMachine/Composition.lean.txt:734)
   and 741 explicitly unfold `rightCfg`. Wrappers explicitly unfolds these foreign
   definitions at lines 761, 782–783, 816–818, and 834; its
   [791](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoints-2026-11-07/cp02/fill-mig1-mega-cp02/source/TCSlib/Complexity/TuringMachine/Build/Wrappers.lean.txt:791)
   `rfl` and direct output-proof conversions also read their fields implicitly. The
   report's “Composition 1, Wrappers 6” counts distinct argument-inventory entries, not
   all source occurrences or the complete definitional closure. The existing public
   apply/step/run contracts do not expose the needed fields. Obtain Seyoon's ruling on
   same-home public readers, then replace explicit and implicit reads and rerun complete
   seals. The separate [API-REVIEW.md](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoints-2026-11-07/API-REVIEW.md)
   proposes the complete ten-field family without import/global-simp changes. It is a
   proposal, not approved API.

2. **Confirmed: `branchTM` needs a separate shape/operational resolution.** It is an
   ordinary definition in Simulation
   [315](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoints-2026-11-07/cp02/fill-mig1-mega-cp02/source/TCSlib/Complexity/TuringMachine/Simulation.lean.txt:315).
   Composition's `condTM` wires the false-tag branch table, while its new proof at
   [725–726](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoints-2026-11-07/cp02/fill-mig1-mega-cp02/source/TCSlib/Complexity/TuringMachine/Composition.lean.txt:725)
   passes `(fun _ _ _ => rfl)` to compare that controller with the branch selected by
   `p x`. This reads transition-table independence, beyond the tape-count/state-type
   conversions. cp02 REPORT lines 65–68 says no equation can replace type reads; that
   does not justify excluding an ordinary foreign definition from rule 10. Shape
   readers alone also do not publish the operational fact. Precise replacement contracts,
   explicit dependent transport, and a sealed consumer proof remain unprobed follow-up
   work. Keep this decision distinct from E1; do not acknowledge new debt or imply that
   the configuration-reader proposal resolves it.

The reports label the checkpoints partial and disclose these seal exclusions; the problem
is an unresolved acceptance prerequisite, not a concealed claim of final completion.
Worker can continue independent F-C/F-B under the frozen scope while these questions go to
Seyoon. No other new design decision was identified in this bounded changed-source review;
this is not a forecast about later checkpoints.

## Supplied validation evidence and its limits

Independently parsed the delivered evidence as data, without running its tools:

- All 35 changed/new declaration regions appear in individual sealed sections: Composition
  9, Encoding 2, Simulation 8, Wrappers 10, TimeConstructible 6. Removing only seal wrappers
  restores submitted source code. Each supplied final seal output records `exit=0`.
  Composition/Wrappers exclude `branchTM`, `leftCfg`, and `rightCfg`; Encoding and
  TimeConstructible do seal those three. Passing the partial lists does not establish
  complete rule-10 conformance.
- The supplied paired controls have 38 examples for 19 definitions: unsealed log has zero
  errors and exit 0; sealed log has exactly one expected `rfl` failure per example, no
  stray errors, and exit 1. Independent parsing rejects duplicate-diagnostic,
  missing-diagnostic, and zero-exit negative logs. These controls do not cover the three
  excluded definitions. Results: `evidence-check.json`.
- The supplied cp02 axiom output covers exactly all 22 changed public proofs and lists
  only `propext`, `Classical.choice`, and `Quot.sound`. These are worker-produced output
  claims, not a fresh axiom walk. The unfiltered compiled census, including generated
  auxiliaries/module ownership, is explicitly NOT RUN.
- Worker reports edited-chain/bootstrap elaborations passing. cp02's bootstrap log records
  all 51 modules with zero failures; later working-tree F-C edits are explicitly excluded
  from the checkpoint. Worker discloses a roughly three-second two-Lean overlap in cp01
  despite its one-process brief, and a locking remedy; the process history was not
  independently reconstructed. Preserve that disclosure.
- Copy-text screens, the 641-module final sweep, policy lint, and maintainer elaborations
  remain unrun. Early-checkpoint rules permit these deferrals; none should be recorded as
  complete. No Lean, Lake, screens, source edits outside this records folder, Git mutations,
  or external messages were performed by this review.

The nine F-A target declarations have no source `sorry` in cp02. Eight target admissions
remain (five F-C, three F-B), alongside the three frozen RAM admissions. The three allowed
F-B public additions and F-D's six removals are still pending. New proofs use the published
`Fin.sum_univ_add`, head-envelope, input-symbol, action/configuration, and computation-reader
APIs rather than adding generic copies. The moved Catalog proof copies remain pending the
explicitly deferred F-D retirement. I read every changed/new declaration body and the full
reports; the large unchanged source bodies were compared mechanically, not reread in full.
