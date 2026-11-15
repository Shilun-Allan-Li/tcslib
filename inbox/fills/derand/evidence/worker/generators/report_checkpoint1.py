import json
from pathlib import Path
import re
import runpy
import subprocess

payload = Path('/private/tmp/derand-worker/payloads/checkpoint1/derand')
record = json.loads((payload.parent / 'build-record.json').read_text())
proof = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
base, tip = record['base'], record['tip']
sizes = []
for path in record['source_files']:
    old = subprocess.check_output(['git', 'show', f'{base}:{path}'], cwd=proof)
    new = (payload / 'src' / path).read_bytes()
    sizes.append(f'| `{path}` | {len(old.splitlines())} | {len(new.splitlines())} |')
census = payload / 'evidence/verification/logs/checkpoint1-final-axioms/evidence_axioms_checkpoint1-final_Census.log'
types = {}
for line in census.read_text().splitlines():
    if line.startswith('DERAND-AXIOMS '):
        row = json.loads(line.split(' ', 1)[1])
        types[row['name']] = row['type']
symbols = ['Complexity.IterateFind.computesFunInTime_find', 'Complexity.mem_DTIME_iff',
           'Turing.FinTM.decidesInTime_iff', 'Randomized.inBPP_iff']
signatures = '\n\n'.join('### `' + name + '`\n\n```lean\n' + name + ' :\n' +
    types[name] + '\n```' for name in symbols)
scope = payload / 'evidence/worker/scope-request'
answer = (scope / 'SR-01/answer.txt').read_text()
standing = (scope / 'standing-discretion.txt').read_text()
sr02 = (scope / 'SR-02/request.md').read_text()
rejection = (scope / 'SR-02/automatic-review-rejection.txt').read_text()
text = f'''# derand · checkpoint 1

Issue: issued-r2, replacing `outbox/fills/derand/` r1. Worker: Codex, the worker
called “Claude” by the brief. The verified host addendum takes precedence where stated.

## Status

Source base: `{base}`. Checkpoint tip: `{tip}` on the local-only `fill/derand` branch.
The delivery contains the generic-fuel harvest E1, the two pre-approved readers E2/E3,
the specifically approved SR-01 reader, and the DTIME corollary proved from H17.

| Target at this checkpoint | Status |
|---|---|
| `Complexity.exists_seedMajorityTM` | original admission retained |
| `Complexity.seedMajority_mem_DTIME` | proved modulo `exists_seedMajorityTM` |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | original admission retained |

The full issued 377-module replay passed with zero errors. Its sorry list is exactly
the issued baseline minus `seedMajority_mem_DTIME`: 25 declarations in 12 modules.
The source branch stays local. Later consumer/host work is outside this checkpoint patch.

## Rule 10 finding and exception disclosure

**Rule 10 status: HOLD.** All four full-closure harvest variants report 20 diagnostics:
11 belong to the byte-unchanged original `polyTimeComputable_find`, and 9 belong to E1.
Eight new diagnostics concern the hidden tape/state carrier fields of the imported
`ModuleHost.hostTM` and `IterateFind.copyTM`; the last concerns the final opaque
function-computation transport. The raw logs and source line maps are delivered at
`evidence/verification/seals/checkpoint1-harvest-final/`.

The other edited files pass their four focused seals. All paired controls pass
unsealed and their sealed negative fails exactly once; the controls are retained in
the final delivery, with checkpoint-compatible DTIME imports. The explicit-unfold
scan found no added foreign-definition selector sites. A seal finding is reported
as a finding; the native and axiom checks are separate evidence.

SR-02 proposes typed interface views in two additional frozen providers. Automatic
approval review refused application; neither provider was edited. Seyoon delegated
judgment over exceptions while away. The worker continues the authorized mathematics
and records the uncleared interface finding rather than expanding provider scope.
This checkpoint requires maintainer review of that exception. The exact proposal,
failed/successful diagnostic prototypes, rejection, and pending status are included.

## Source files and sketches

| File | Base lines | Checkpoint lines |
|---|---:|---:|
{chr(10).join(sizes)}

The corollary's status/sketch now describes its reader-based witness proof. E1 has
its formula and generalized assembly sketch. Existing target headers, definition
bodies, declaration order, and all frozen proofs remain unchanged; the header check
reports zero differences over 93 base declarations. Its one-character negative
control reports exactly one changed header.

## New declarations and full final signatures

E1 permits an arbitrary numerical fuel `R`, computed in binary by the supplied
machine `F`; it retains the total length guard and arbitrary initial word. Its
explicit polynomial per-round budget is `A * (2*n+2+P.eval n+5)^D`. The time is
`c*(T n+1)*(R n+2)`. No use of `final_bound` is made for exponential fuel.

{signatures}

## Overlap and reuse

* E1 deliberately repeats the generalized assembly of the existing
  `IterateFind.polyTimeComputable_find`, as the brief expressly requires. It reuses
  the existing private `Inv`, `inv_*`, `verdictWord`, `stepWord`, `outWord`, and
  their lemmas in place. It does not copy their definitions, introduce a competing
  loop engine, or change `polyTimeComputable_find` or `final_bound`.
* Its machine implementation uses the published proved `exists_loopFindTM`,
  `ModuleHost.clean_install`, `clean_emit`, `host_call`, `host_clean`, `guard_add`,
  and request budgets. It does not consume admitted loop-host/conditional specs.
* E2/E3 and SR-01 expose existing definitions by `Iff.rfl`, with no attributes.
  The whole-base namespace-resolved scan found no collision in 1,274 Lean files.
* The corollary uses only the host contract and `mem_DTIME_iff`; it does not unfold
  `DTIME`, `DecidesInTime`, or `DecidesInTimeVia`.
* The SR-02 prototypes are feasibility experiments, not accepted home-file reader
  proofs. Their operational transition tables are not copied into the patch.

## Scope requests

### SR-01 · approved

The exact session question and answer follow verbatim:

```text
{answer.rstrip()}
```

### Standing exception instruction

```text
{standing.rstrip()}
```

### SR-02 · not applied; specific human answer pending

```text
{sr02.rstrip()}
```

```text
{rejection.rstrip()}
```

No additional frozen-file mutation was made. The typed-view patch remains a proposal.

## Promotion and reader requests

E2/E3 are the issued pre-approvals and SR-01 is specifically approved. SR-02 is the
only further provider-reader proposal. No other promotion is included in this patch.

## Validation and evidence

* Both issued packs passed `shasum -a 256 -c`; their exact contents, checksums and
  logs are delivered under `evidence/verification/inputs/issued/` and `logs/`.
* Base and checkpoint each passed the complete 377-module supplied order. Every
  call checked one module via `scripts/lean_check_tree.sh`. No `lake build` ran.
* Base sorry audit: 26/12. Checkpoint audit: 25/12, with precisely the corollary removed.
* E1, E2, E3, SR-01, the original `polyTimeComputable_find`, and its consumer
  `polyTimeComputable_iterateFind` have only `propext`, `Classical.choice`, `Quot.sound`.
  All stored constants of the changed files were censused. The admitted targets'
  `sorryAx` behavior at this checkpoint is expected and stated above.
* Whole-file seals use actual full-import-closure Lean Names, both PolyExpr modes
  and strict/coe variants; raw catalogs, installation/EOF records, sources, line maps,
  and diagnostics are included. Invalid early harness attempts are retained separately.
* Header check and negative control pass. Whole-base clash scan: four additions,
  zero collisions. Explicit-unfold scan: zero added sites.
* Lint line-set diff: Cryptography remains 92 FAIL / 101 WARN; Complexity changes
  from 25 FAIL / 391 WARN to 25 FAIL / 390 WARN. There are no added FAIL lines.
  E3 removes the `DecidesInTime` reader warning. SR-01 removes `InBPP` from its
  missing-reader list; the inherited size warning changes 1403→1415 under the
  explicitly approved exception. Both changed WARN lines and all removals are listed.

## Host resources and execution exception EX-01

The host-wide cap is **at most three Lean processes total**, shared with other jobs.
Every Lean/Lake/check-tree command used the issued wrapper, `LEAN_SLOT_TAG=derand`,
and the default `~/.lean-slots`; cache commands used `-k 3`. Only narrowed roots were
fetched. The pinned Lean is 4.25.0 on arm64 macOS. Python ran as `python3 -I`.

The worker used its own proof and verification git worktrees and a separate delivery
worktree. Its physically owned pinned package tree is in the verification checkout;
the proof checkout links that same job-owned tree read-only. It shares no other
worker's package tree or TCSlib oleans. Each checkout has its own single-writer olean
tree. This execution arrangement is disclosed as EX-01 under the standing instruction.
The first evidence symlink was replaced with a physical evidence tree to satisfy
Lean's root-containment check; failed probe logs are retained.

The macOS preflights met the 4 GiB headroom and 12 GiB disk floors. No shortage,
exit 137/139, or jetsam event occurred. Long active modules and slot waits were
normal execution, not E-RES. Shared `~/.elan` and Mathlib archive-store provenance,
exact package pins, absent documentation-only packages, cache validation, and all
derand slot lines are recorded. Peer scheduling paused only the worker's Python
dispatchers at module boundaries; no native Lean or other worker was signaled.

## Commit reproduction and delivery

`patches/COMMITS.tsv` records author, committer, both dates and the signing column.
All commits use the configured checkout identity, with `commit.gpgsign=false`;
signing is `none`. Applying the complete patch series at the issue base in a separate
scratch clone reproduced every hash, ending at `{tip}`. Raw reproduction commands,
metadata, expected hashes and actual hashes are in `evidence/reproduction/`.

The source branch is not pushed. This payload is delivered only under
`inbox/fills/derand/` from the worker's own delivery worktree; the delivery pulls with
rebase before its ordinary push. The exact delivered file set is checked against
the top-level `SHA256SUMS`, and the evidence has its own complete `SHA256SUMS`.
No other delivery path is edited. Maintainer review and Seyoon's PR approval remain
the landing process.
'''
(payload / 'REPORT.md').write_text(text)
print(payload / 'REPORT.md')
