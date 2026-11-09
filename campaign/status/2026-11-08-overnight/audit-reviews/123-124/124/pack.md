# Gate124: Private SafeRun bridge and three public segment readers

**Prepared for Codex audit. Not yet clear to merge: #244 — external audit pending.**
Seyoon alone dispatches, rules on design/debt and merges; no audit is dispatched here.
PR https://github.com/Shilun-Allan-Li/tcslib/pull/244; branch `codex/ab34-safe-run-segments`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8; audited HEAD `cfa6a3ee327b03e601b25fd5f0535e85fd18f897`.
Final records/exchange pins and bundle SHA/section count are supplied by the published
exchange README and issued prompt. Frozen private preparation wording remains historical
data; this pack and STATUS.md give the current remit.

## Exact source and evidence

| Input | Exact binding | Evidence |
|---|---|---|
| BASE owner | 9b5dcf46408db681bcbc721930ef2203fa6bc47d, Git blob `3ac162843c4363e2c31082efa4b66408fd184ce8`, SHA256 `1a7d25619fb88b51d012e48fb66b758ce08c199e7d3aad219c25f18a7e741b4d` | `review/source/BASE/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean.txt` |
| Actual adopted HEAD owner | cfa6a3ee327b03e601b25fd5f0535e85fd18f897, Git blob `3362598b94a5351be6ae032569ec975cd9d4fd0f`, SHA256 `e64bb55b65e76d234a316e01e9704df876592f3c3bf36857dc0df030a6dcadad` | `review/source/HEAD/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean.txt` |
| Exact private preflight identity | owner bytes equal frozen proposed source e64bb...; full owner plus four proofs and14 pairs | `review/proof-source-identity-binding.json`, `review/inputs/exact-adopted-private-bridge-preflight/` |
| Source freeze |18→18 public,0→1 private; all existing headers/imports/definitions/attributes/docs/names exact | `review/qa/source-freeze.json`, `review/qa/declfreeze.txt`, complete literal reverse mapping |
| Full screen population | same exact33 named sources at each side | `review/screen-population.txt`, full `review/source/BASE` and `review/source/HEAD` |
| New actual replay | PASS exact cfa full80/static0, whole895 input/output, source unchanged | `review/replay/` full RESULT/request/logs/maps plus all80 compiled source captures |
| Selected ABI/AX |3 BASE roots reused exactly; actual replay-bound4 HEAD roots PASS, new private helper has no BASE counterpart | `review/metadata/` raw requests/logs/results; actual HEAD4 PASS, public3 all selected fields exact to BASE |
| New actual full screen | Completed exact33-file cfa HEAD, 0 new/0 BASE-only pairs; all dispositioned | `review/screen/HEAD-RESULT.json`, complete raw stdout and pair records |
| Historical old head |535c full80/full33 and3 new pairs, old metadata only | `review/historical-535c/`; never cfa validation |
| Style/campaign/size | fresh exact BASE/HEAD exports, complete stdout and baseline diff | `review/qa/` receipts/outputs/comparison |
| Publication | Exact source/records/bundle binding is in exchange README and issued prompt | `arora-barak-ch3-4/outbox/gates/124-safe-run-gate/` |

## Authorized source scope and preserved contracts

Only `TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean` changes. One new
private non-simp theorem, `Turing.safeRun_iff_segment`, identifies the own
`SafeRun H avoid c t c'` definition with
`Segment H {some avoid} (fun _ => True) c c' t`. It uses own `SafeRun`, the
published `segment_iff`, singleton membership and trivial-invariant logic.
The three existing public `SafeRun.zero`, `SafeRun.cons` and `SafeRun.trans`
keep their exact literal formal headers and docstrings, and call this one
private bridge around their distinct public `Segment` operation. All existing
names, definitions, imports, attributes and other source bytes are exact.
No new public API or library import; one new private theorem is explicit.
The source freeze reverses precisely that insertion and those three proof bodies
to recover BASE byte for byte. Formal header means before `:=`; BASE zero had
a term proof, while the replacement has a tactic proof.

SafeRun avoids its forbidden state strictly before the final time. Its zero
contract has no nonavoidance assumption. `Segment.zero` requires only the
trivial head invariant; cons uses the exact one-step equation, start-state
nonavoidance and `1+t=t+1`; trans composes the exact middle configuration and
time sum. The private bridge does not strengthen endpoint or halting assumptions.

## Canonical public equations and full context

| Reader | Canonical published equation | Source |
|---|---|---|
| private bridge | `Turing.segment_iff` | `TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:432` |
| `Turing.SafeRun.zero` | `Turing.Segment.zero` | same file:444 |
| `Turing.SafeRun.cons` | `Turing.Segment.cons` | same file:539 |
| `Turing.SafeRun.trans` | `Turing.Segment.trans` | same file:464 |

The complete canonical file and all33 named source files appear in both
`review/source/BASE` and `review/source/HEAD` as `.lean.txt`. The exact patch from BASE is
`review/actual-BASE-HEAD.patch`; full four chunks and the reversal are in
`review/literal-source-and-scope-binding.json`. Standards are complete under
`review/standards/policy.md`, `review/standards/workflow.md`,
`review/standards/campaign/standards/TEMPLATE.md`, the three controls under
`review/standards/campaign/maintainer/`, and `review/standards/campaign/duplication-ledger.md`.

## Validation and explicit limits

Frozen `review/scope.json` retains preparatory lint comparison hashes. The fresh current QA is `review/qa/comparison.json`, with `review/qa/BASE-QA-receipt.json`, `review/qa/HEAD-QA-receipt.json` and their matching raw stdout.

- Complete private preflight owner source is byte identical to this actual HEAD.
  Its native check on whole MAC8 passes with zero errors/sorry warnings and the
  same six inherited warning messages. The instrumented source adds diagnostic
  Lean import/output; the uninstrumented owner and exact input hashes are given.
- All FOUR complete proofs (including the new private bridge) pass native and
  sealed whole scopes. Inventory reaches exactly the original seven ordinary
  guards. Both modes remove only `Action.apply` from default simp and differ
  only by the guard line. Four AX sets are standard only. Imported theorem proof
  values remain citation boundaries; own SafeRun unfolding is intentionally
  allowed. This is a bounded four-proof opacity check, not a global theorem.
- Fresh fourteen positive kernel-checked rfl controls and fourteen negative
  same-identity failures demonstrate all seven guards are effective. All raw
  sources/logs/receipts and exact definition/mode/kernel-name identities are in
  `review/inputs/exact-adopted-private-bridge-preflight/`. Expected control errors are
  intentional; all preparation history, including the first successful unused
  simp-argument warning, remains visible.
- Actual refined-head full80/static0 replay **PASS** at exact cfa; complete895
  input/output maps and source unchanged. All80 module logs and committed
  sources plus the full1003 source SHA map are in `review/replay/`. The actual
  replay-bound HEAD4 metadata query passes with zero errors/warnings. BASE's
  previously fresh selected3 run is reused only with identical9b5 pin/probe
  and unchanged current MAC8 owner object. Public3 all selected metadata fields
  are byte-exact to BASE. The new private helper's complete type/universes/
  privacy/non-simp/AX are separate, with no BASE counterpart.
  No proof-value or whole-owner/global metadata equality is inferred.
- Default simp argument: all existing imports/source attributes are byte exact.
  The only added declaration is a private theorem with no attributes; compiled
  simp-lemma and simp-unfold flags are both false. Existing selected public3
  flags stay exact. This is a source/selected-root argument, not a whole
  environment or generated-auxiliary metadata certificate. Full raw type repr
  is authoritative; the consumeMData field removes only outer metadata.
- The fresh style runs both exit0 with byte-identical zero findings. Campaign
  lint runs both exit1 on inherited findings; their complete stdout differs
  only in the owner INFO row,326→318 lines and0→1 private declarations, while
  public18 stays exact. Full commands, raw outputs and diff are under `review/qa/`.
- The NEW exact33-file cfa HEAD screen completed with exit0. Directed pairs
  2107→2107; 0 new/0 BASE-only, every row dispositioned in
  `review/screen/pair-dispositions.json`. Raw counts use the at-least60-normalized-
  character body filter, not source-interface declaration counts. No helper
  screen was launched. The old535c full80/full33 results and its three new
  adapter pair observations stay historical under `review/historical-535c/`; only
  the current cfa source, replay and full screen validate this refined head.

Neither an older replay nor this private source identity establishes automatic
validity after another source PR merges. Preserve seven accepted SG1 kinds,
FE-LIVE/FH1/BLIVE separation, the54-name affected union (not54 copies), bounded
class-image residual and the nine inherited Primitives AX closures. No direct
admission, blanket debt permission, global absence/clearance or retirement is
claimed. Mathematical sorries and other family choices remain outside scope.

## Auditor checks

1. Check the exact source pin and full BASE/HEAD owner. Verify the one private
   non-simp helper, all existing public headers/imports/definitions/attributes,
   source reversal and exact source-to-preflight identity. Inspect every explicit
   simp/rw/unfold argument, including the private bridge; ordinary imported
   definitions are not explicitly unfolded. Own SafeRun is the allowed own def.
2. Restate each preserved public contract, strict-before-end avoidance and zero
   assumptions, then verify the public equations' orientation, instantiation and
   exact time conversion. Inspect all four complete scope placements, all seven
   ordinary guards/default simp removal and all fourteen control identities.
3. Check the three selected public full raw types/universes/privacy/kind/simp/AX
   against BASE, and the new private helper separately. Check exact actual HEAD
   full80/static0 replay and complete895 provenance in this packet. Missing or
   older outputs are not PASS and snapshots must not be composed.
4. Compare full BASE/HEAD lint and exact same33-file screen stdout, disposition
   every new directed pair, retain old535c observations as old-source history,
   and preserve bounded debt accounting. No global retirement follows.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`
with blocker/major/minor/note per TEMPLATE, then verdict and counts. Identify
unresolved source/evidence gaps. Do not change source, push, dispatch another
auditor or declare merge clearance.

**Deliver a downloadable `gate124-safe-run-findings.md` containing the findings
table and verdict line, and also paste its content in your reply.**

## Independent provenance and current context

The actual80-module exact-head replay has0 failures and static0 mismatches/31
inherited admissions. Both895 input/output maps and the unchanged MAC8 input are supplied.
Independent public input anchors are the three files under
`campaign/status/2026-11-08-mig1-merge/`: receipt.json, object-hashes.json and Lean-tree.json.
The replay input895 hashes equal that adoption, not merely a self-reported count.
Actual static helper and diagnostic helper/context are in reproduction-tools/.

Campaign changes after MAC8/9b5 are records only. Later source merges require the standing
current-tree validity check; no unmerged proposal is assumed landed. Retire only the stated
proof implementations after external audit closure and Seyoon’s merge; no global absence,
all-owned-type equality or new debt exception follows.
