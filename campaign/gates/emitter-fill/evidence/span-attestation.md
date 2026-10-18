# Maintainer whole-span attestation — the emitter fills

Evidence for `audits/emitter-fill-pack.md`. Span: `d7b5b6f9` (the
pre-fill base every brief pinned, rev-parse-generated and
object-verified in each) → `938a25fc` (the P2 integration
attestation); the pack commit follows. All claims produced by the
maintainer from the repository, independent of the deliveries' own
attestations.

## 1. Commit enumeration

Exactly **four Codex fill commits** touch `Build/` in-span, one per
delivery, each integrated by `git am -3` after byte-identical replay
in an isolated worktree at its pinned base:

| Zip | Commit | File | REPORT | Result |
|---|---|---|---|---|
| fill-emitter-W | `bcee716b` | Wrappers.lean | batchW.md | complete (1/1) |
| fill-emitter-P | `200bdb91` | Primitives.lean | batchP.md | partial (2/3) |
| fill-emitter-L | `634ee795` | Loop.lean | batchL.md | complete (3/3) |
| fill-emitter-P2 | `a10771fe` | Primitives.lean | batchP2.md | completes the layer |

Maintainer commits in-span (`1aa994a0`, `09e10c89`, `938a25fc`, the
A2 integration pair) touch no `Build/` source. The concurrent A2
campaign commit (`07bbad98`) touches `ClassNP/Nondeterminism.lean`
only.

## 2. Whole-span freeze

Over the complete span, the net diff of `Build/`:

- deletes **exactly the seven audited contract `sorry` placeholders**
  and the three closing docstring lines of the Loop spec entries
  (each re-emitted with an append-only completion appendix) — nothing
  else;
- adds **zero non-private declarations**: the name-level public
  surface of all four files is identical (extraction
  `^(theorem|lemma|def|abbrev|instance|structure|inductive|noncomputable def) <ident>`,
  zero drift per file);
- adds **zero imports** beyond batch P's disclosed
  `Mathlib.Tactic.FinCases` (L's identical addition merges to the
  same line);
- name-level private additions: Wrappers **+1**, Loop **+119**,
  Primitives **+151** (= P's 83 + P2's 68), **zero removals
  anywhere** — total **271**, matching the four REPORTs declaration
  for declaration.

Per-delivery, each REPORT's byte-reconstruction freeze check
(removing exactly its new blocks reconstructs its base file
byte-for-byte) was shipped and is the stronger per-step record; the
round-3 auditor independently reproduced this technique on the spec
commits.

## 3. Admission stepping and sweeps

`Build/`-scope admissions stepped **7 → 6 → 4 → 1 → 0** across
W → P → L → P2, each step predicted at integration and matched by a
fresh 57/57 sweep with zero `error:` lines
(`audits/logs/{emitterW-e3contA2,emitterP,emitterPL,emitterP2}-sweep.log`).
The final tree: **12 admissions, all campaign** (EXP 1,
Nondeterminism 4, SAT 1, Tautology 1, Hardness 5), `Build/` at zero.
The P2 sweep log is the complete relaunched run after the recorded
maintainer timeout slip; no partial log was committed.

## 4. Closure attestations

The maintainer traversal at each integration (types, values including
opaque, constructors; `audits/logs/*-axioms.log`) confirmed at every
step: the newly closed contracts at empty roots and at most the
standard triple; the still-open contracts at exactly their own roots;
every campaign closure and library regression unchanged. The final
run asserts **all seven emitter contracts admission-free**. The
deliveries' own wider traversals cover 241 (P), 387 (P2), and the
W/L inventories of helper-and-generated declarations, all clean.

## 5. Sizes and policy

Loop.lean 5,713 and Primitives.lean 7,636 lines — both grown under
their recorded exceptions; the D7 trailing-split deferral covers them
(post-E5 re-measurement stands; the split proposal remains the one
reviewed internal-namespace package). Wrappers.lean 739, Convention
155 — under target. Build lint at every step: 0 FAIL, the two
standing size WARNs.
