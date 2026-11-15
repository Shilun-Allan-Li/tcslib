# sc-garble · checkpoint 2

This is a partial checkpoint, with six of seven requested admissions proved. B1's
`sliceMultiMessageSecure_of_prfOut` remains for the final stage. The complete source series
is based on the exact PR #315 head `fbd37f447596d4207c8d08b7ef7602f57fe95198`; it is proved
modulo #315's merge. The issued exchange pack is pinned at
`7d85785c2e98f0bfdec081a875a9343f06043a8a`. Both issued checksum packs passed.
The local proof head is `{head}`. The unsigned format-patch series and complete identity/date
rows in `patches/COMMITS.tsv` reproduce every commit hash in an isolated scratch clone.
The proof branch remains local; only this assigned delivery path is pushed.

## Target status

| Target | Status |
|---|---|
| `spDecStr_wrongKey` | Proved; standard axioms only |
| `specialScheme_wrongKey` | Proved; standard axioms only |
| `specialScheme_multiMessageSecure` | Proved directly from D4; standard axioms only |
| `nestedSpecial_wrongKeyBot` | Proved; standard axioms only |
| `uprob_not_good_le` | Proved by averaging B2 |
| `yaoSeed_good_whp` | Proved using the stronger B2 seed law and disjoint blocks |
| `sliceMultiMessageSecure_of_prfOut` | Pending B1 post-map and maximizing advice |
| Required `uprob_not_good_le_of_perm` | Published and proved with the prescribed statement |

The source scan is exactly 32 → 26 admissions, removing precisely these six targets and
adding none. The remaining 26 admissions are in 12 modules; the final requirement is 25 in 11.

## B2 and the Yao proof

`good_of_no_crossOpening` reduces goodness to failure of all distinct-assignment row openings.
`uprob_crossOpening_le_of_perm` restricts the independent vertex-key table to distinct argument
vertices and a different output vertex, reads independent row coins, and averages `WrongKeyBot`
over the output key. Each gate has at most four assignments and three different assignments
per row, so existing finite union bounds give twelve events per gate.

The shared theorem `uprob_not_good_le_of_uniform_data` is stronger than B2's requested seed
law: permutations may depend on the raw seed. No bad-row event reads a permutation, so the
joint key/row-coin marginal alone must be uniform. `uprob_not_good_le_of_perm` is its exact
fixed-permutation corollary; the old uniform-permutation target averages that corollary.
This is a mathematical strengthening, not a weakened statement or additional hypothesis on B2.

Yao's key blocks `b*S+v` and row-half blocks `2*S+2*(4*i+idx(a))+b` are distinct and below
`10*S`. Binary assignment indices are injective below four for arities zero, one and two.
Restriction along the block/bit injection, followed only by standard equivalences, proves the
full uniform key/row-coin marginal. The unused `2*S` shift bits need no further law because
the stronger B2 seed theorem permits every seed-dependent permutation family.

The output collision corollary, located downstream in `GarblingSecurity/NestedBounds.lean`,
reuses `MultiMsg.uprob_eq_pair` and the output union bound. Output vertices may repeat.
`δ(n) = 12*S(n)*δ₀(n) + outLen(n)*(2⁻¹)^n` is negligible. Zero-length blocks, zero gates,
constant gates, and the one-position and two-position cases are included by the statements.
The output-collision helper has `[Nonempty ρ]`; Yao's pair of bit-vector coin spaces satisfies
it. The prescribed B2 theorem itself has no extra nonemptiness hypothesis.

The checkpoint-1 wrong-key and direct D4 proofs are unchanged. Their detailed rationale and
all original overlap disclosures are retained in `evidence/history/checkpoint1-REPORT.md`.

## Files and sketches

Every delivered source line has at most 100 Python characters, and every file at most 1000
lines. Yao has 970 lines. Its only changes are the permitted target body, its sketch and the
main-results bullet split. The circuit file differs by exactly the nine approved reader lines.
No new simp attribute is added.

| Repository path | Base lines | Checkpoint lines |
|---|---:|---:|
{table}

The target sketches describe the implemented arguments. The new long helper proofs include
formula docstrings, sketches and step comments where appropriate. Garbling's module title,
results and contents now describe the proved B2 APIs and its two definition-free helpers.

## Gate 27 hand-off

1. Maximizing slice advice and the empty-fit convention: pending B1.
2. Slice post-processor: pending B1; the shared zero-prefix mask identity is already proved.
3. Random-function slice law: D2/D4 provide full uniform pads; B1 will identify its use of
   their windows, without repeating that random-function proof.
4. Triangle/collision bound: inside D4, already consumed by the direct scheme proof.
5. Frozen scheme multi-message theorem: proved directly from D4; its downstream joint
   corollary remains proved through the SG-1 public relabelling readers.
6. B2: complete (`uprob_not_good_le_of_perm`), with both required corollaries proved.

## Overlap and reuse

All checkpoint-1 overlap disclosures remain binding and are included verbatim in the historical
report under `evidence/history/`. In particular, SG-1 replaces exactly six private readers,
the surviving private XOR lemma is unchanged, the scheme theorem consumes D4 directly, and
the inline nested-ciphertext length specialization is disclosed for promotion.

New statement-shape searches are captured in `evidence/reuse/checkpoint2-searches.log`; the
pre-implementation searches are also in chat and the original search log.

- `findSome_eq_some_of_dichotomy` combines Mathlib's `List.findSome?_eq_none_iff` and
  `List.exists_of_findSome?_eq_some`; it does not re-prove either list law.
- Output/argument marginals compose `HardcoreBit.pushesUniform_restrict` (Basic:220),
  `pushesUniform_eval` (250), product maps, and sum/product equivalences. The dependent row
  marginal uses `Equiv.piCurry` (Mathlib Logic/Equiv/Basic:170) and uniform evaluation.
- `wrongKeyBot_nonneg` is the one-position nonnegativity consequence of the published
  `MultiEnc.wrongKeyBot_iff` and `uprob_nonneg`; no probability identity is re-proved.
- The cross-opening bound averages the published wrong-key property with `uprob_prod`,
  `OneWay.uexp_mono` and `OneWay.uexp_const` (OneWayFunctions/Basic:69).
- The two nested finite union bounds use `uprob_exists_le` (Foundations/Probability:137),
  Finset sums and cardinality readers. The inline count specializes `2^arity*(2^arity-1) ≤ 12`
  to arities at most two; this is arithmetic bookkeeping, not a new union-bound proof.
- The old uniform-seed theorem uses `uprob_comp_equiv`, Fubini and constant expectation.
- `assignmentFold_small` packages the existing Yao binary fold's arity-zero/one/two facts.
  No public bound/injection theorem for `assignIdx` existed at the base; the helper is generic
  and definition-free and Yao supplies its own `assignIdx_eq` reader.
- `pushesUniform_bits_of_blocks` specializes uniform restriction to disjoint bit blocks and
  curries the selected table. Nearest relative: the block injection `dla_blockPos` and its
  injectivity proof in `Candidates/Concrete.lean:831–856`; that proof concerns a different
  candidate layout outside the issued order. Standard `finProdFinEquiv` and restriction are
  reused rather than any imported candidate construction.
- `key_row_blocks_injective` is arithmetic for this concrete layout; no probability law is
  repeated. `pushesUniform_key_row_blocks` composes it with the general block restriction and
  standard `sumArrowEquivProdArrow`, curry, `boolArrowEquivProd` and `piCurry` equivalences.
- Output collisions reuse `MultiMsg.uprob_eq_pair` (FromPRF/HybridLemmas:111), which itself
  supplies the Fubini/point-probability proof. The inline marginal merely composes uniform
  projection, evaluation and `pushesUniform_eval_pair` (HardcoreBit/Basic:263).
- The approved `DAGCircuit.isFaninTwo_iff` is an `Iff.rfl` reader of the existing definition.
  It is not an alternate circuit predicate or a re-proof of well-formedness.

Promotion requests: the generic option-complement bound, dependent row-coin marginal,
first-success dichotomy and bit-block restriction can move to shared probability/list layers;
the nested-string length reader can move beside `nestedSpecial`. No such frozen-file move
is made here. The circuit predicate reader was separately approved and is included.

## Scope requests and exceptions

Seyoon approved the exact circuit reader: “Approve the reader addition”. The original request,
patch, answer, and a byte comparison proving that deleting exactly those nine added lines
restores the entire frozen base file are delivered. No other frozen-file edit is used.

Seyoon authorized best judgment on exceptions while asleep and full disclosure, and messages
coordinating the Mac's shared resources. That instruction is preserved verbatim. The stronger
B2 seed law justifies avoiding a separate shift-block conditioning proof while proving all
requested conclusions. This route change is disclosed above.

Complete Rule-10 A/B seals (strict and coe), paired controls, the explicit-unfold scan and the
final 166-module sweep remain deferred to final proof stabilization. They are mandatory final
checks, not waived. The original base bootstrap and pilot seal evidence are retained.

Two own drivers were accidentally queued simultaneously during B2 development. The issued host
wrapper serialized their actual Lean runs; there were no concurrent writers to this olean tree.
Their queue-time source snapshots were too early. The original snapshots and the correction
are retained, and an authoritative serialized rerun passed. Future drivers have a local
nonblocking guard and capture source after acquiring a host slot. Full details and timings
are in `evidence/coordination/source-snapshot-correction.md`.

One own collision proof check was interrupted after increasing memory/time. A bounded diagnostic
localized a missing nonempty marginal hypothesis and an inference hotspot. Explicit finite
marginals fixed it; the final unrestricted proof checks pass in seconds. No other worker's
native process or lock was touched.

Automatic approval review initially rejected the checkpoint-1 combined pull/push based on the
general README rule. The explicit task §4 and host §5 override were then supplied; the same
direct scoped push was approved and succeeded. The exact event is recorded in
`evidence/coordination/checkpoint1-push-review.md`. No permission remained blocked.

## Host resources and evidence

Every own Lean/Lake/check command uses the issued wrapper, tag `sc-garble`, shared default
`~/.lean-slots`, cap three. Own checks are serial. The narrowed cache uses `-k 3`; there is
no lake build, unfiltered cache request or copied package tree. All Python runs use `python3 -I`.
The original Mac preflight, fresh own-package revisions, cache counts and exact issued pack
verification are retained from checkpoint 1. No dependency revision or base branch was advanced.

Authorized peer messages coordinated wrapper use and short dispatcher boundary gaps. Additional
checks queued behind other workers' cache or native jobs. Scoped slot traffic and resource
notes are delivered; another worker's locks or native process were never edited or killed.

Checkpoint checks cover all changed modules/helpers through the development logs, final owned
modules, YaoReal and the facade, all stored constants of every changed/new module, and signatures.
The six targets, B2 and `garbling_good_whp` are standard-only. The remaining B1 admission and
Yao's `yaoHybrid_polyTime`/`yaoHybrid_simulators` retain sorryAx; the Yao end-to-end consumers
still depend on those two outside-unit admissions. Raw base/final consumer axiom logs are included.

Frozen headers cover all 139 base declarations with exactly six expected SG-1 removals and
zero other differences. Both freeze controls detect exactly one violation. The name scan covers
1,275 base files and 29,518 explicit resolved names: 35 additions, two SG-1 replacements,
zero clashes. The full final sweep will additionally check generated descendants. Lint remains
92 FAIL / 101 WARN with identical line sets. Manifests name exactly all delivered paths and
have been verified with shasum. Every raw diagnostic source/log, including failures, is retained.

## New declarations: signatures

The complete Lean-elaborated signatures, including implicit parameters, are authoritative in
`evidence/logs/checkpoint2-check/`; the inventory is also provided as text below.

```lean
{signatures}
```
