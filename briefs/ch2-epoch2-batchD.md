# Ch2 fill campaign — Epoch 2, Batch D: TMSAT and the timed_universal bridge

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-D`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-D.zip` with `REPORT.md`, the full modified sources, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

The epoch's heavy batch (30 points; **continuation budget anticipated** —
the chapter-1 `universal` B2 precedent; see ground rule 7). Four targets:
polynomial time-constructibility, `TMSAT ∈ NP`, `TMSAT` `NP`-hardness, and
their completeness assembly — [AB09, Theorem 2.9]. This batch also carries
the campaign's **one planned mid-fill statement addition**: a public
quantitative bridge exposing `timed_universal`'s constant, specified by the
phase-3 audit and governed by the protocol below. Chapter 1's
`timed_universal`, `universal`, `one_work_tape_binary`, `exists_codeTM`,
the `MachineCode`/`EffectiveMachineCode` layer, and epoch 1's calculus are
all proved and citable.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/TMSAT.lean` — targets, in order:
  1. `timeConstructible_poly` (line 120, 7 pts)
  2. the **bridge statement** (see protocol below), then `TMSAT_mem_NP`
     (line 182, 12 pts)
  3. `TMSAT_NPHard` (line 228, 10 pts)
  4. `TMSAT_NPComplete` (line 240, 1 pt)

## The bridge protocol (read carefully — this is the unusual part)

The phase-3 audit requires `TMSAT_mem_NP` to rest on a **new public
quantitative bridge** for the Chapter-1 simulator. Inherited **verbatim**
from `audits/ch2-phase3-resolutions.md` (note 3 disposition):

> the fill obligation is pinned as the auditor specifies — a public
> quantitative bridge for **one simulator chosen before the code and
> input**, preserving both the success and timeout clauses of
> `timed_universal`; the suggested bridge form
> `(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoids importing `PolyBound`
> into Chapter 1 and is recorded for the fill brief, which must not infer a
> bound on the existing statement's arbitrary existential witness.

Mechanics, under the file-ownership rule:

1. **State** the bridge in `TMSAT.lean`, clearly sectioned, with a
   docstring flagging it as *the phase-3-mandated bridge statement, new
   public surface, for the epoch-2 audit*. The quantifier shape is binding:
   the simulator (and its constant) is fixed **before** the code `α` and
   the input — never per-(α, input); both the success clause and the
   timeout clause of `timed_universal` must be preserved; the suggested
   constant form above is a suggestion, any explicit closed form in
   `|α|`, `canonizerTime(|α|)`, and `(t+1)²`-shape is acceptable if it
   provably works.
2. **Prove it.** The intended route is re-running `timed_universal`'s
   construction quantitatively, from `Universal.lean`'s **public** API. You
   must NOT derive it by bounding the existing statement's existential
   witness — that inference is unsound (the witness is arbitrary) and the
   audit explicitly forbids it.
3. If the public API is insufficient (the proof needs `Universal.lean`
   internals), **escalate**: state the bridge, leave its proof `sorry`
   (allowed only for this one declaration, prominently reported), record
   precisely which internal fact is needed, and proceed with
   `TMSAT_mem_NP` **on top of the stated bridge**. The maintainer then
   handles the Chapter-1-side addition serially at epoch merge, flagged
   for its own audit — Chapter-1 files are not yours to modify.
4. The bridge must not import `PolyBound` (or any Chapter-2 notion) into
   anything Chapter-1-shaped; it lives in `TMSAT.lean` and speaks only
   Chapter-1 vocabulary plus explicit arithmetic.

## Binding disciplines inherited from the phase-3 records

- **`PolyBound` budget chain** (`TMSAT_mem_NP`): the certificate length and
  the verifier budget chain through `hc : PolyBound c.canonizerTime`
  explicitly; both the success and timeout clauses of the bridge are used —
  a candidate that runs out of deadline must *reject*, not diverge.
- **Exact-value emission discipline** (`TMSAT_NPHard`; round-1 finding 3,
  carried in the docstring): the certificate length `Q` is emitted
  **exactly**, by the docstring's three-way case split (`C₀ = 0` → empty
  run; `C₀ > 0, c₀ = 0` → fixed constant from finite control;
  `C₀ > 0, c₀ > 0` → `timeConstructible_poly C₀ (c₀ - 1)`). Majorizing `Q`
  changes the language — the docstring's `C₀ = c₀ = 0` counterexample is
  the audit's own.
- **Deadline majorization formula** (same docstring, binding): `r := max 1
  c₀`, `D := (K+1)·(B+1)^2·(C₀+3)^(2e)`, `T' n := D·(n+1)^(2er)`, computed
  exactly by `timeConstructible_poly D (2er - 1)`. The deadline **may** be
  majorized; the certificate length may **not**.
- The docstring sketches of all four targets are the audited routes; your
  `REPORT.md` maps each named obligation (pairing parser, wrapper
  totality, relocation-and-capture, emission chains, binary countdowns,
  `pairEncode_injective` pinning) to its discharging lemma.

## Environment and verification

As the epoch-1 briefs: pinned toolchain; `lake exe cache get`; **never
`lake build`**; bootstrap the 53-module list; iterate
`bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/TMSAT` plus the
later modules; final full sweep, zero `error:` lines. **Axiom prints** for
the four targets **and the bridge**: at most
`[propext, Classical.choice, Quot.sound]` (subsets fine — disposition D1);
`sorryAx` only in the single escalation case of bridge-protocol step 3, and
then rooted **only** at the bridge statement (verify the root; report it).

## Ground rules (binding)

Identical to epoch 1 (`workflow.md` §4): exclusive ownership of
`TMSAT.lean`; `private` helpers, every new declaration listed (the bridge
is deliberately **public** — the one exception, mandated above); statement
freeze on all existing declarations; escalation over alteration; no
out-of-scope sorries; docstrings stay; precise imports. Rule 7,
**continuation**: at 30 points, if the budget exhausts, deliver a partial
zip stating the frontier exactly (which obligations proved, which stated
with listed `sorry`s — allowed only in a partial delivery); the maintainer
issues a continuation brief.

## Out-of-scope sorries you will see (leave untouched)

`NP_subset_EXP` / `EXP_subset_NEXP` (2A / epoch 3);
`mem_NP_iff_exists_length_le` + the HALT pair (2C); the
`Nondeterminism.lean` compilations and padding (2B / epoch 3); everything
in E3/E4 (`SAT.lean`, `Tautology.lean`, `CookLevin/*`).

## REPORT.md checklist

- [ ] Four targets + the bridge: filled/stated, with the obligation-to-lemma
      map and the exact bridge constant you proved.
- [ ] Base hash recorded; new declarations listed — the bridge flagged as
      the mandated public addition.
- [ ] Requested shared lemmas / escalations — or "none"; bridge-protocol
      step 3, if taken, documented with the missing internal fact.
- [ ] Final sweep log tail + axiom prints (at most the triple; `sorryAx`
      only per the bridge escalation, root-verified).
- [ ] Diff touches only `TMSAT.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (see
`briefs/ch2-epoch1-batchA.md` §pitfalls, same pin), plus:
- `timed_universal`'s statement shape: destructure its success/timeout
  disjunction before quantitative work; do not let `rcases` discard the
  timeout clause you must preserve in the bridge.
- `canonizerTime` is a function of `|α|`, not of `α` — keep the bridge's
  constant a function of lengths only.
- Unary-run emission: `List.replicate` bookkeeping under binary countdown;
  the epoch-1 `takeTrues_replicate` pattern (private, batch 1D) is the
  shape, not a citable API.
- `pairEncode` nesting order in the quadruple is
  `pairEncode α₀ (pairEncode x (pairEncode 1^Q 1^T'))` — get the
  associativity direction from the statement, not from memory.
- Budget normalizations: epoch 1's `comp_time_bound` is private; re-derive
  the `(s+1)^e`-absorption you need as your own private lemma.
