"""Write checkpoint-2/final reports from completed, immutable payload evidence."""
import json
from pathlib import Path
import runpy
import subprocess
import sys

phase = sys.argv[1]
assert phase in ['checkpoint2', 'final']
payload = Path('/private/tmp/derand-worker/payloads') / phase / 'derand'
record = json.loads((payload.parent / 'build-record.json').read_text())
worker = payload / 'evidence/worker'
verification = payload / 'evidence/verification'
base, tip = record['base'], record['tip']
validation = json.loads((verification / 'logs/final-validation.json').read_text())
assert validation['tip'] == tip and validation['modules'] == 387
assert validation['standard_axioms_only']
assert 'POST-REPLAY PASS' in (verification / 'logs/post-replay.log').read_text()
audit = json.loads((worker / 'source-audit/results.json').read_text())
assert audit['tip'] == tip
sizes = '\n'.join(f'| `{r["path"]}` | {r["base_lines"]} | {r["final_lines"]} | '
                  f'{r["maximum_width"]} |' for r in audit['files'])
added = json.loads((worker / 'clash/all-additions/results.json').read_text())['additions']
assert len(added) == 54
census = verification / 'logs/final-replay-axioms/evidence_axioms_final_Census.log'
constants = [json.loads(line.split(' ', 1)[1]) for line in census.read_text().splitlines()
             if line.startswith('DERAND-AXIOMS ')]
assert len(constants) == validation['stored_constants']
signatures = []
signature_rows = []
for declaration in added:
    name = declaration['name']
    matches = [row for row in constants if row['name'] == name or
               row['name'].endswith('.' + name)]
    assert len(matches) == 1, (name, matches)
    row = matches[0]
    signatures.append('### `' + name + '`' + (' (private)' if declaration['private'] else '') +
        '\n\nSource: `' + declaration['path'] + ':' + str(declaration['line']) + '`.\n\n' +
        '```lean\n' + name + ' :\n' + row['type'] + '\n```')
    signature_rows.append(dict(declaration=declaration, kernel_name=row['name'],
                               type=row['type'], axioms=row['axioms']))
(worker / 'source-audit/signatures.json').write_text(json.dumps(signature_rows, indent=2) + '\n')
scanner = runpy.run_path(str(worker / 'tools/frozen_headers.py'))
source = (payload / 'src/TCSlib/Complexity/Randomized/Build/IterateFind.lean').read_text()
e1 = next(d['header'] for d in scanner['extract'](source)
          if d['name'] == 'computesFunInTime_find').rstrip()
scope = worker / 'scope-request'
answer = (scope / 'SR-01/answer.txt').read_text().rstrip()
standing = (scope / 'standing-discretion.txt').read_text().rstrip()
sr02 = (scope / 'SR-02/request.md').read_text().rstrip()
rejection = (scope / 'SR-02/automatic-review-rejection.txt').read_text().rstrip()
ex01 = (scope / 'EX-01.md').read_text().rstrip()
ex02 = (scope / 'EX-02.md').read_text().rstrip()
overlap = (worker / 'overlap/all-declarations.md').read_text().rstrip()
seals = (worker / 'seals/summary/final-canonical.md').read_text().rstrip()
commit_table = '\n'.join(f'| `{row["commit"]}` | `{row["signing"]}` |'
                          for row in record['commits'])
history = Path('/private/tmp/derand-worker/delivery-history.json')
deliveries = json.loads(history.read_text()) if history.exists() else []
delivery_text = '\n'.join('* ' + row['phase'] + ': `' + row['commit'] + '`; ' + row['status']
                          for row in deliveries) or '* No earlier delivery recorded.'
title = 'checkpoint 2' if phase == 'checkpoint2' else 'final'
text = f'''# derand · {title}

## Status and review disposition

All three frozen targets are **proved with only `propext`, `Classical.choice`, and
`Quot.sound`**. No target is proved modulo an admission in this payload. The exact
final source passes the complete 387-module replay with zero errors; its sorry list
is the issued baseline minus precisely the three requested targets: **23 declarations
in 10 modules**. No statement is weakened.

**Rule 10 disposition: HOLD, disclosed exception EX-02.** The canonical seals of the
harvest E1 retain nine new diagnostics, alongside eleven inherited diagnostics in
the unchanged old theorem, in each of four variants. All 56 variants for the other
14 changed/new files pass. This delivery does not claim seal clearance. A proposed
reader fix in two further frozen providers was rejected by automatic approval review
and was not applied. The maintainer must assess this exception before landing.

Worker: external Codex, the worker called “Claude” in issued-r2. The host addendum
overrides the environment addendum where stated. The r2 issue replaces r1.

* Issued exchange pin: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
* Source base: `{base}` on `cryptography/pass-shelat-ch2-4`.
* Final source tip: `{tip}` on local-only branch `fill/derand`.
* Lean: 4.25.0, arm64 macOS; Mathlib pin
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
* The source branch is never pushed; delivery is only `inbox/fills/derand/`.

| Frozen target | Final status |
|---|---|
| `Complexity.exists_seedMajorityTM` | proved; standard axioms |
| `Complexity.seedMajority_mem_DTIME` | proved from the contract through `mem_DTIME_iff`; standard axioms |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | proved; standard axioms |

## Checkpoints and proof route

Checkpoint 1 delivered E1, E2, E3, approved SR-01, and the corollary from the still
admitted host; its full 377-module replay passed. This payload completes checkpoint
2's host as well as Theorem 180.1. The consumer was developed first modulo the host,
as the issued proved-modulo rule expressly permits. Filling the host removed that
dependency, verified by both the all-constant axiom census and a kernel dependency
path audit. No mathematical work was delegated; all proofs and checks were run by
this worker. Other-worker messages concerned shared resource scheduling only.

The host retains `x` in the paired state `⟨x, ⟨i, a⟩⟩`. Binary ranks enumerate all
`2^w` seeds using the existing `bitsEquiv`; the finite prefix count supplies the
induction invariant. The generic-fuel harvest uses the existing total length guard
and its closed `Inv`. The terminal rank is included in `range (R+1)`; no bound is
assumed for an unguarded increment past termination. Fuel is binary `Nat.bits (2^w)`,
never an exponential unary word. Published arithmetic and pairing machines compute
each round, and the explicit polynomial per-round budget yields
`c * (2^w * (n+1)^e)`. The native initial-configuration envelope follows from the
public head-position interval bound before halting and the public halt/run readers
after halting. A zero time coefficient is impossible by `not_computesInTime_zero`.

The consumer uses `ceilRoot d n = 0` for `n=0`, and
`Nat.nthRoot d (n-1)+1` otherwise. The unary word is computed using the published
bounded state search and fixed unary powers, not a copied root machine. A secure
generator is truncated and expanded to the syntactic envelope
`a*(s^d+1)^k+s+1`. Non-uniform advice chooses a bad input at each seed length and
security gives a uniform `1/12` gap threshold directly; this is the quantified
threshold form of the paper's infinite-bad-length contradiction. Published
`verifier_toNUPPT`, probability and uniform-prefix identities identify the advantage.
Below the threshold, both width and test use true coins; above it they use generated
coins. Thus the acceptance margins are `7/12` and `5/12`, and the strict-majority
reader identifies the language. There is no finite table. Logarithm/rpow limits and
one finite-exception constant give the time comparison, followed by the published
DTIME monotonicity and constant-factor transports.

## Source files, scope, and sketch edits

| File | Base lines | Final lines | Maximum width |
|---|---:|---:|---:|
{sizes}

Every changed/new Lean line has Python `len` at most 100. Every file has at most
1000 lines except `Classes.lean`, whose inherited 1403→1415 length was specifically
approved with SR-01. E1 stays at 801 lines. No new `@[simp]` attribute is added and
imports are precise. The source audit verifies each file's SHA256 against the final
commit. Four host helpers and six consumer helpers are inserted before consumers
in the final order; the original 377-module relative order is preserved, without
cycles. No parent facade or other frozen provider is edited.

The two owned module titles/Main results/Contents and target Status/sketch paragraphs
describe the delivered proofs. The helper docstrings give their formulas and source
tags; every proof of at least 15 nonblank proof lines has a proof sketch. The explicit
`advance` formula was clarified in the final comment-only commit. All 93 original
declaration headers, whole definitions, declaration order, and frozen proofs in the
five affected existing files are preserved byte for byte; the one-character header
control reports exactly one difference. This includes leaving the original
`polyTimeComputable_find` and `final_bound` unchanged.

## New declarations and final signatures

There are 54 source declarations (53 public, one private). The complete kernel-type
signatures are listed below; section variables are included by the elaborated
universal quantifiers. `source-audit/signatures.json` also records the actual kernel
name of the private lemma. Generated auxiliary constants are included in the separate
321-constant census, rather than mistaken for additional source declarations.

E1's source signature, in full, is:

```lean
{e1}
```

This is one public generic-fuel addition. It accepts arbitrary numerical `R` via a
fuel machine for `Nat.bits (R |x|)` and gives
`c*(A*(2*n+2+P.eval n+5)^D+1)*(R n+2)`. It reuses the private helpers in place,
retains the total guard/invariant, and uses an arbitrary FP initializer so that the
host can carry `x`. It never applies `final_bound` to exponential fuel. E2 and E3
use the issued signatures without binder-style changes; SR-01 is the only additional
approved shared-file declaration.

{chr(10).join(signatures)}

## Overlap and reuse

All 54 additions are disclosed below, including technical specializations and the
private lemma. Unless marked “new”, TCSlib path/line references are at the issue base;
Mathlib references are at the pinned revision. New own-definition references are at
the final tip. No private foreign lemma is silently copied.

{overlap}

E1's generalized assembly is deliberate repetition explicitly required by the brief.
Its own-file private `Inv`, `inv_*`, `verdictWord`, `stepWord`, and `outWord` are reused
in place. The existing theorem is not re-derived or modified. The machine assembly
uses proved `exists_loopFindTM`/`loopHost_contracts` and the published clean-module
host interfaces; it does not consume admitted loop-host or timed-conditional specs.
The existential projection engine does not count witnesses with the required time
bound, the unary H16 counter is unsuitable as exponential unary fuel, and polynomial
block-majority tests do not supply this full seed-space host. No competing loop or
binary-arithmetic engine is introduced.

Searches used `rg`/`rg --files` across TCSlib and pinned Mathlib before each cluster.
The complete raw search records and probe sources are retained. The searched shapes
include `exists_proj_decider`, `enumMachine_contracts`, H16/counter loops,
`polyTimeComputable_find`, `Clean.envelope`, `Nat.bits`, `Nat.testBit`, `bitsEquiv`,
`finFunctionFinEquiv`, `eq_bits_append_replicate`, binary arithmetic, `Nat.sqrt`,
`Nat.nthRoot`, unary/stateFind searches, and EXP/BPP inclusions. Before the probability
argument, searches included `prfAdv_eq_expect`, `prgAdv_*`, `uexp_*`, `uprob_*`,
`uprob_comp_equiv`, `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`,
`HardcoreBit.pushesUniform_restrict`, `randProb_eq`, `randProb_eq_uprob`, and
`abs_uexp_sub_le_uprob`. The implementation reuses published probability/expectation
and uniform-prefix identities; it introduces no replacement identity of those kinds.

## Scope requests

### SR-01: specifically approved

Exact session request and answer:

```text
{answer}
```

The reader is beside `InBPP`, proved by `Iff.rfl`, with a formula docstring and no
attribute. It changes no definition or existing statement. The exact diff/search
record is under `evidence/worker/scope-request/SR-01/`.

### Standing exception instruction

```text
{standing}
```

### SR-02: proposal not applied; specific human answer pending

```text
{sr02}
```

Automatic review rejected applying/checking the provider patch. Exact recorded reason:

```text
{rejection}
```

No mutation of either provider was made. The proposed patch and prototype source
remain historical evidence, not part of `src/` or the patch series. There is no
claim that standing discretion overruled this automatic rejection.

### EX-01: execution arrangement

{ex01}

### EX-02: remaining Rule 10 finding

{ex02}

These are the complete exceptions used. E1/E2/E3 were pre-approved by the issue;
SR-01 and its inherited-size exception were expressly approved. No other frozen-file
change was taken. EX-02 is a transparent exception disposition under the standing
instruction and remains a maintainer review HOLD, not specific approval of SR-02.

## Promotion and reader requests

* Promote `SeedMajority.envelope_of_computesInTime` to the native finite-machine
  layer (`TuringMachine/Finite.lean`): `Clean.envelope` requires a clean seam
  contract, while this generic result only needs a completed native computation.
* Promote `Derand.eff_mapCoins` beside the `polyTimeModel` efficiency readers: it is
  a generic coin-map/P-preimage wrapper, not specific to PRG derandomization.
* Promote a generic length-threshold wrapper beside `StateLoop.lenLe_comp`; the
  local private `short_poly` merely specializes that public machine.
* SR-02 is the proposed typed-view/interface route for the remaining E1 issue.
  It requires specific scope approval and subsequent proof/seal work before use.
* The ceiling-root order lemmas could be proposed to the pinned Mathlib root layer
  at integration. No package source was edited.

These are requests for maintainer integration, not extra changes in this payload.

## Native replay, axioms, headers, and edge cases

| Check | Result |
|---|---|
| Both issued SHA256SUMS (`shasum -a 256 -c`) | PASS |
| Exact-base full issued order | 377/377; zero errors; 26 sorry declarations/12 modules |
| Checkpoint-1 full issued order | 377/377; zero errors; 25/12, exactly the corollary removed |
| Final order with ten helpers | 387/387; zero errors; 23/10, exactly all three targets removed |
| Final source provenance | every one of 387 recorded source hashes equals `{tip}` |
| All stored constants of changed/new files, plus old-find consumer | {len(constants)}; standard axioms only |
| Old `polyTimeComputable_find` and `polyTimeComputable_iterateFind` axiom sets | identical at base and final |
| Kernel sorry-dependency paths from all three targets | absent |
| Frozen header/body/order/proof audit | 93 original declarations; zero differences |
| One-character header negative control | exactly one difference |
| Name-clash scan over 1274 base Lean files | 54 additions; zero collisions |
| Explicit foreign-definition selector scan | base 0, final 0, added 0 |
| Public docs and long-proof sketches | 54 additions; zero issues |
| Source scope/width/size | PASS with specifically approved Classes inherited-size exception |

The final replay began at `904123d3780cc1f5daf4f37ad49d90395595c1a9` and advanced to
`{tip}` before `State.lean` was visited. The only transition was that file's explicit
formula in a docstring; non-comment source tokens are identical. The advance record
and source diff are retained. The final validator independently compares **every**
recorded source hash, including modules checked before the advance, to the final tip.
It is therefore an exact-final-source replay, without pretending the checkout stayed
at one hash from its first step.

The edge probe checks zero width/coins and zero root, rejects zero time coefficient,
and verifies the zero-prefix probability behavior. The main proofs handle ties by
strict comparison, all small lengths and `n=0` through the piecewise true-coin branch,
seed lengths shared by many input lengths through the advice length bound `|x_s|≤s^d`,
and `ε≥1` through the same positive degree choice with reciprocal below `min(ε,1)`.
The generator envelope holds at every length, including zero. The finite-exception
constant is positive since it starts with 1. The enumeration includes terminal rank
`R`; its prefix count bounds include the terminal value and zero-width seed space.

## Whole-file Rule 10 evidence

All seals use the actual full TCSlib import closure, resolved Lean Names (including
private declarations), with installation/EOF checks and raw request catalogs. A
excludes `PolyExpr.eval` as notation and B seals it. Strict seals projection coercions;
canonical coe treats projection coercions as notation. Reducible abbreviations remain
notation in both. The canonical summary verifies its generated sources against the
exact final source before selecting results from development phases.

{seals}

The only failing declarations in every harvest variant are the unchanged
`polyTimeComputable_find` (11 diagnostics at final lines 362×2, 380, 382, 389, 390,
433, 434, 539, 555, 556) and E1 `computesFunInTime_find` (9 at 602×2, 622, 624,
631, 632, 676, 677, 799). These are source line numbers, with raw probe line maps
delivered separately. There is no strict/coe or A/B diagnostic-count difference to
attribute. Base seals cover the five pre-existing edited files; helpers have no base.

All four paired controls pass unsealed; each sealed negative fails exactly once,
while its reader-based positive remains valid. Diagnostic counting recognizes both
`error:` and `error(...)`. Failed early harness prototypes remain in the evidence and
are not treated as valid seals. The non-canonical carrier probes reduce 20 diagnostics
to 12, with five E1 diagnostics remaining; they neither isolate every dependency nor
clear Rule 10. The explicit-unfold scan passing does not erase implicit reductions.

## Lint line-set comparison

The prescribed `python3 -I scripts/campaign_style_lint.py ... --check8b` commands ran
at the exact base and final. Their nonzero exit codes reflect inherited FAILs.

| Corpus | Base FAIL/WARN | Final FAIL/WARN | Added FAIL lines |
|---|---:|---:|---:|
| Cryptography | 92/101 | 92/101 | 0 |
| Complexity | 25/391 | 25/390 | 0 |

The diff compares diagnostic line sets, not just totals. E3 removes the DTIME
`DecidesInTime` missing-reader warning. In Classes, the size warning changes
1403→1415 under the approved inherited-size exception, and the missing-reader list
changes from `InBPP, InBPPStrong, InCoRP` to `InBPPStrong, InCoRP` because SR-01
supplies the reader. These two changed WARN lines are the only added WARN lines;
three old WARN lines disappear. All full lint logs and line-set records are included.

## Host resources and coordination

The cap was **at most three Lean processes total on this Mac**, shared with other
jobs. Every Lean, Lake, and `scripts/lean_check_tree.sh` command used the unchanged
issued `lean-slot.sh`, `LEAN_SLOT_TAG=derand`, and default `~/.lean-slots`. Every cache
command acquired `-k 3`. No `lake build` or unfiltered cache get ran. Each check-tree
call checked one module; each olean tree had one writer. Python used `python3 -I`.

The Mac has 12 CPUs and 19,327,352,832 physical memory bytes (18 GiB). Initial
headroom was `(4182+276651+28714+9187)*16384 = 5,222,137,856` bytes, 4.863495 GiB;
initial disk free was 231,367,417,856 bytes, 215.477699 GiB. The final replay preflight
recorded 7.389206 GiB headroom and 186.241554 GiB disk free. The delivery artifact
preflight recorded 6.491745 GiB and 182.661835 GiB. All passed the 4/12 GiB floors.
`sysctl`, `vm_stat`, `memory_pressure -Q`, `df -k`, `mount`, and explicit computations
are delivered. All working/scratch paths are APFS, with no RAM disk. No Lean
137/139 or jetsam shortage occurred. Long modules and wrapper waits were normal;
there were no self-imposed module timeouts.

The physical package tree is job-owned in the verification worktree. The proof
worktree links that same job's tree read-only by convention and runs no Lake;
it has its own independent TCSlib olean tree. No package/dependency tree or TCSlib
olean was copied from another worker. The shared host toolchain is
`~/.elan/toolchains/leanprover--lean4---v4.25.0`; the permitted archive store is
`~/.cache/mathlib`. It already contained **32,667 files, 1,595,387,830 bytes** before
this session's cache work. Their individual origin is unknown; they are not described
as session downloads. The narrowed 129-root cache command downloaded zero archives
and decompressed 3,082. The one extra `NthRootLemmas` root downloaded zero and
decompressed 1,933. Additional exact imports were already cached. Pin checks report
`PACKAGE PINS PASS: 11 present; 4 absent; 0 mismatches`. The four absent packages are
documentation-only `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, and `MD4Lean`, not imported
by this order. There are no zero-byte package oleans; Mathlib-import probes pass.

Only derand slot-log lines are copied to `logs/slots.log`. Resource coordination
messages were authorized by Seyoon. At peer requests, only validated derand Python
dispatchers paused to let current native children finish and provide acquisition
gaps. No native Lean or other worker process was signaled. The precise 12-second
gap and 40-second dispatcher pause, release/acquire times and finally-block resumes
are recorded in `resource-coordination.md`, `courtesy-gap.jsonl`, and
`cache-window.jsonl`. No mathematical work was shared or delegated.

## Evidence index and completeness

`evidence/verification/` contains the complete verification-worktree evidence;
`evidence/worker/` contains the complete proof-worktree evidence. Their README maps
the original absolute paths. Both include raw logs, successful and failed probes,
source archives, tool versions, catalogs, manifests, request records and controls.
The scratch snapshot preserves all top-level scratch files and the complete rejected
SR-02 prototype; its provenance inventory distinguishes historical proposals from
the accepted source. No running log was moved; packaging happened after check writers
finished. No package tree, toolchain, or compiled TCSlib olean is delivered.

| Evidence | Location under `evidence/` |
|---|---|
| Issued packs, sums, wrapper | `verification/inputs/issued/` |
| Baseline/CP1/final replay, timestamps and max RSS | `verification/logs/base-bootstrap/`, `checkpoint1-full/`, `final-full/` |
| Final replay order and source advance | `verification/logs/final-order.txt`, `final-source-advance.json` |
| Final validation and post-check controller | `verification/logs/final-validation.json`, `post-replay.log`, `post-replay-*.log` |
| Final all-constant axiom and path probes/logs | `verification/axioms/final/`, `verification/logs/final-replay-axioms/`, `final-replay-paths/` |
| Canonical final seal selection and all failures | `worker/seals/summary/`, `worker/seals/<phase>/` |
| Baseline seal logs | `verification/seals/base/` |
| Paired controls | `worker/controls/`, `worker/seals/controls/`, `worker/logs/controls-unsealed/` |
| Frozen headers, output, one-character control | `verification/headers/final-replay/` |
| Clash/lint results | `verification/clash/`, `verification/lint/` |
| Full-closure explicit-unfold scan (3,928 catalog entries) | `worker/unfold/`, `worker/logs/explicit-unfold-exact-final.log` |
| Source widths, lines, SHA256 and signatures | `worker/source-audit/`, `worker/logs/source-audit-final.log` |
| Overlap and doc audit | `worker/overlap/`, `worker/docs/` |
| Scope decisions and automatic-review rejection | `worker/scope-request/` |
| Historical scratch inputs and prototypes | `worker/scratch/` |
| Development tools and delivery generators | `worker/tools/`, `worker/generators/`, `verification/tools/` |
| Exact commit reproduction | `reproduction/replay.log`, `reproduction/metadata.json` |

`evidence/SHA256SUMS` names every evidence file except itself. The top-level
`SHA256SUMS` names every payload file except itself, including the evidence manifest.
Hash verification and exact path-set checks run before each push; the delivery Git
index is checked against that same physical set. Nothing named in a manifest is
omitted. Invalid/failed research attempts are retained transparently, not substituted
for the final accepted checks. The final ZIP has `derand/` at its root, and each ZIP
entry is compared byte-for-byte by SHA256 to this payload and checked by ZIP CRC.

## Commit reproduction and delivery

The complete format-patch series starts at the exact issue base. `COMMITS.tsv` gives
author, email, author date, committer, email, committer date, and signing for every
commit. All source commits use the configured identity
`Seyoon Ragavan <complexzetaprime@gmail.com>` with `commit.gpgsign=false`.

| Source commit | Signing |
|---|---|
{commit_table}

Applying every patch to a separate scratch clone at `{base}`, with the recorded
committer identity/dates and signing disabled, reproduced **every commit hash** and
ended at `{tip}`. This is checked afresh for this payload before pushing; the raw
commands, expected/actual hashes and metadata are delivered under `reproduction/`.

Earlier delivery records:

{delivery_text}

The worker uses its own `codex/delivery-derand` exchange worktree and stages only
`inbox/fills/derand/`. Each delivery commit uses `commit.gpgsign=false`, pulls with
rebase from `exchange/pass-shelat-ch5-8`, rechecks hashes/exact tracked file sets,
and pushes normally to that branch. No force push or other inbox edit is used.
The delivery commit cannot include its own hash in its payload; the chat records it
after the push. Maintainer review and Seyoon's PR approval remain the landing process.
The maintainer also rebuilds full-library downstream modules outside this issued
order and `audits/pass-shelat/Checks`, as the brief specifies.
'''
(payload / 'REPORT.md').write_text(text)
print(f'REPORT COMPLETE: {payload / "REPORT.md"}; {len(text.splitlines())} lines; '
      f'{len(signatures)} signatures; {len(constants)} stored constants')
