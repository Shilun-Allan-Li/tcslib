# Phase 0 foundation gate

The review instructions are `audits/lwe-sis-phase0-pack.md`. Mathematical source is
frozen at `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`, with per-path hashes in
`evidence/source-freeze.json`. The user dispatched Codex at exchange
`09d1456efacded71850c84497db5c8d1f65ab0a0`; its report passed the statement gate with
counts 0/0/0/3. See `audits/lwe-sis-phase0-{findings,resolutions}.md` and `status.json`.
The following evidence describes the immutable statement-stage freeze, including its
14 admissions. Current filled proofs have separate evidence under `fills/00-encodings/`.

## Evidence

* `initial-dependency-sweep/` and its JSON: fresh serial 55-module scope before the
  final predicate naming change. The JSON retains original local log paths; the copied
  logs with those basenames are supplied beside it.
* `*-named-assumptions.log` and `renamed-assumption-checks.json`: four successful checks
  after naming, covering both changed modules and both facades.
* `Checks.lean`, `axiom-check-result.json`, `axioms-and-constants.log`: final checked
  probe on all 61 source declarations, plus an environment walk yielding 164 constants.
* `source-declarations.json`, `declarations-and-axioms.json`, `admissions.json`,
  `elaborated-constants.json`: exact inventories; no generated constant is counted as a
  handwritten public declaration.
* `style-*.log`: zero FAIL and two documented reader-name heuristic WARNs across ten
  mathematical modules. Both named predicates have actual `_iff` readers.
* `source-package-pins.json`, `selected-cache-hashes.json`,
  `official-archive-provenance.json`: own package source revisions and selected official
  archive hashes. This does not claim a new network cache download or raw PDF archive.
* `summary.json`: accounting summary, checked by `prepare_inventory.py`.

The new modules have 14 admissions. Seventeen warnings belong to unchanged dependencies.
No whole-library root sweep, construction proof or external gate closure is claimed.
The 103 non-source constants consist of 100 structure-generated names and three compiler
auxiliaries. There are no private-type derived instances or unexplained extra constants.

## Reproduction

Use a separate checkout and scratch olean tree, the exact Lean/Mathlib pins and only the
required package roots. Coordinate native/cache resources first. Do not use another
chat's package or scratch objects, run `lake build` or run an unfiltered cache get.

From that checkout, with the required pinned package archives installed in its own tree:

```sh
export TCSLIB_OLEANS="$PWD/.lake/lwe-sis-review-oleans"
while IFS= read -r module; do
  bash scripts/lean_check_tree.sh "$module" || exit 1
done < briefs/lwe-sis-constructions/gates/00-foundations/evidence/module-order.txt
bash scripts/lean_check_tree.sh briefs/lwe-sis-constructions/gates/00-foundations/evidence/Checks
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encoding
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/LWE
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/SIS
python3 -I briefs/lwe-sis-constructions/gates/00-foundations/prepare_inventory.py
```

`prepare_inventory.py` summarizes the supplied logs; it does not replace them with new
execution claims. It expects the historical frozen source, not the later filled
checkout. Use `fills/00-encodings/verify_freeze.py` for the filled source. Statement
review has passed; proof review and later construction gates remain separate.

## Delivery

The uploadable bundle and portable Git objects are generated under this worktree's
ignored `.lake/crypto-dispatch/` directory. Bundles are not committed. Its delivery
README identifies source/records commits, SHA-256 checksums, section count and kickoff.
The user published the statement inputs at exchange commit
`09d1456efacded71850c84497db5c8d1f65ab0a0`, dispatched Codex, and returned its Markdown
findings in chat/inbox. The historical publisher script and receipt are retained.
The next proof review uses `lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/`
and the fill's separate publication command. Both routes use only the dedicated
namespace in the independent sparse publisher clone; the shared exchange stays untouched.

Exact primary PDF archival and ingestion remain open, as the pack states. An auditor
must report source fidelity unverified if the primary definitions cannot be checked.

**Not yet clear to merge — the statement gate passed; proof review, source archival
and user-controlled integration remain open.**
