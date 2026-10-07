# Epoch 3 (fill round + merge refactor) — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Fill campaign". External auditor:
cross-vendor LLM per decision log.

## Round 1 (`epoch3-pack.md` → `epoch3-findings.md`, audited at `b519a004`)

**Zero blockers, zero majors.** The auditor confirmed the audited bundle's
SHA-256 against the maintainer's file (exact match), extracted all 25
modules, and judged the constructions from the definitions rather than the
agent reports. All three delivered constructions were certified against
their audited designs:

- **3A parser + bridge**: the decoder implements Argument A's grammar on
  *every* word (fallback on the empty string; `decode_encode_pad` for all
  machines and padding lengths including the fallback's own 84-bit
  serialization; the up-front guard compatible with zero padding), and
  `codeCanonical_eq` identifies the primitive-recursive canonization with
  parse-then-reserialize on all inputs. The Mathlib joint was checked
  against the pinned sources (`exists_code` contract, `tr_eval` semantics);
  the per-statement (not per-`TM2.step`) cost accounting, sentinel coding of
  empty/trailing-false words, and the finite maximum — over the `2^n` input
  words, not over unbounded stack contents — were each verified.
- **B2 live block**: the enumeration order (offset `3·input + work`, nine
  records per state group), the final-cursor argument (`h' < L` via the
  record decomposition, including the last record with empty suffix), the
  no-stale-successor property, and the exact ledger were independently
  re-summed: `d_halt ≤ 3L + 3N + 13`, `d_live ≤ 3L + 5N + 14`, both within
  `universalBlockBound = 3L + 5N + 20`. The converse was confirmed to cover
  divergent sources with no fairness or eventual-halting assumption.
- **3C obliviousness**: length-only trajectories at every physical time
  (one-step correspondences through decoration and transverse coding, with
  no unchecked interval), idling after early source halting, absorbing
  configurations after the simulator's own halt (head equality persists for
  arbitrary `t`), and the stage ledger re-derived exactly to
  `c = 18(a+1)² + 23(a+1) + 3b + 25` including the truncated-subtraction
  reset at `p = 0`.

The auditor additionally ran ~14,000 bounded executable model checks
(8,191 words + 600 padded round trips + 1,800 mutated serializations +
3 oversized headers through the parser; 4,860 universal live blocks; 264
decorated schedule executions up to 7,736 steps) — no counterexample — and
independently reproduced the freeze with *ordered* comparisons and a
GitHub cross-check of the fill span (exactly four changed Lean paths;
the three Universal headers byte-identical; both statement-prose fixes
comment-only; the 22 Sweep promotions code-identical modulo comments and
`private`, with `indexedFold`'s `Nodup` and `source_bounds`'s
initialized-run scope preserved).

One minor, resolved in the closing commit:

| Finding | Resolution |
|---|---|
| 1 minor — the retained `exists_effectiveMachineCode` sketch paragraph still reads "with a polynomial `canonizerTime` … uses the composition combinators", superseded but unlabeled; the pack's "no polynomial bound is claimed anywhere" is literally false of that paragraph | The paragraph is now explicitly bracketed as the **original, superseded proposed sketch** with an end marker stating no polynomial `canonizerTime` is proved and no combinator construction was built; the implementation note and frozen theorem are untouched. The change is comment-only (verified by comment-stripped diff — flagged as a change to an audited file) and does not dispose of design question 1. The pack's overclaim is acknowledged as an erratum; the shipped pack is preserved as the historical artifact (standing precedent) |

Note-level dispositions:

- **Findings 2–5** (parser/canonization joint, bridge, B2 block, 3C layers):
  certifications with no change identified — recorded above.
- **Finding 6** (degenerate instances): acknowledged — several of the pack's
  own adversarial instantiations fail the theorems' hypotheses rather than
  stress the simulators (`not_computesInTime_zero` forbids initialized
  halting at time zero; a vanishing `T` empties `DTIME T`;
  `TimeConstructible (fun _ => 1)` is false at length 2). These vacuity
  facts are already theorems in-repo; no code change. Future packs pose
  theorem-level degenerate tests with globally admissible positive bounds
  and a clock witness.
- **Finding 7** (attestation methodology): adopted — future drift
  attestations pair the comment-stripped **multiset** diagnostic with
  **ordered** declaration/signature comparisons (the multiset alone cannot
  detect reordering; the auditor's ordered pass found none this round).
- **Finding 8** (`timed_universal` implementability): the endorsement and
  its obligations are recorded for the epoch-4A brief, verbatim: separate
  the clock from `α`; send **only `α`** to `c.canonizer` (canonizing the
  clock-dependent outer payload would decode the wrong machine at an
  uncontrolled cost); buffer emissions; decrement once per simulated source
  transition; intercept source halting before native halting so the success
  tag and buffer can be emitted; budget zero still parses its delimiters
  and returns `[false]`; first halting on transition `t` counts as success
  (deadline-inclusive); the countdown's `O((t+1)(|Nat.bits t| + 1))` and
  `≤ t`-bit buffering fit the quadratic allowance.
- **Finding 9** (reproduction scope): acknowledged — the auditor has no
  Lean/Lake environment, so elaboration, `#print axioms`, the lint run, and
  archive provenance remain **maintainer-side** evidence (the standing
  division of labor; the pack's attestations carry the "verify or
  challenge" framing for exactly this reason). The distinction between
  source-level inspection and kernel/provenance evidence is preserved here
  and in future packs; the archives and raw logs live in the maintainer's
  delivery store and `audits/epoch3-agent-reports/`, and can be supplied on
  request.

**Both human-reserved design questions remain open** (plan §5, questions 1
and 2): this round certifies the constructions' correctness at source level
and explicitly does not dispose of the 3A bridge's architectural placement
or the 3B interpreter's design posture.

**Epoch-3 audit gate closed.** Campaign standing: 20/21 sorries proved;
the sole remaining admission is `timed_universal` (epoch 4). Next:
epoch-3→4 merge splits (Encoding bridge module; Oblivious
decoration/coding layers; Universal block-simulation promotions incl.
`universal_run_join`), then the epoch-4A brief carrying finding 8's
obligations.
