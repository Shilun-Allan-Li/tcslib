# External audit pack: segments composed along a sequence (PR #202, an API gate)

## Why this PR

G5 is the Hennie–Stearns simulation of `k` work tapes on two ([AB09, §1.7]),
`Turing.FinTM.two_work_tapes_run` in `Robustness/TwoTapes`. Its controller simulates one source
step per round. The source machine's state is kept in finite control, so each round starts from a
different control state.

No published lemma iterates such rounds:
- `Turing.Round.iterate_seq` and `Turing.RoundContract` compose rounds that share one anchor
  state;
- `Turing.Lockstep` needs an encoding that is a function of the source configuration. G5's zone
  contents depend on the run's history, so they are not.

The user ruled **API first** (2026-11-05; `campaign/items/u2/G5-statements-plan.md` §8, Q2): the
generic composition is published before G5's fill, and the fill cites it rather than writing its
own induction over rounds.

**The PR:** #202 on `lean/segment-iterate`, head `7b5774fb8d47fd119d2d314f9f6e717cffcee7de`:
- `f0b31bb9fccf658c169dddc04e60c15a2e835871`, the change (`evidence/patches/`), on the campaign at
  `3a8c6199d0e94636069f2064489ab0b455b8687d`;
- then a merge of the campaign (#196's merge `bdc73ab1`), which changes no line of the PR's file.

Against the campaign, the PR changes one file, `Build/Contract/Basic` (+25 −11; blob `43fce3e2`).

## What changed (verify)

| File · declaration | Statement | Proof |
|---|---|---|
| `Build/Contract/Basic` · `Turing.Segment.iterate_seq` (new) | `(cs : ℕ → Cfg k Γ S x) (τ : ℕ → ℕ) (h0 : P (cs 0).workTapePos) (n : ℕ) (h : ∀ r < n, Segment M F P (cs r) (cs (r + 1)) (τ r)) : Segment M F P (cs 0) (cs n) (∑ r ∈ Finset.range n, τ r)` | induction on `n`: `Segment.zero` at `0`; `Finset.sum_range_succ`, then `Segment.trans` of the prefix and the last segment. This is the induction `Round.iterate_seq` carried, with each round's segment taken as a hypothesis |
| `Build/Contract/Basic` · `Turing.Round.iterate_seq` | unchanged | now `Segment.iterate_seq cs τ h0 n fun r hr => (hround r hr).segment ha`; its sketch says so |
| `Build/Contract/Basic` · the module docstring | the main-results list names `Turing.Segment.iterate_seq` beside `Segment.trans` | — |

**Names** (`evidence/names/`): `Segment.iterate_seq` is used on no ref (354: the campaign, `main`
and every PR head) except #202's own branch. `Round.iterate_seq`'s statement is unchanged; its
users are `ZoneRebalance`'s `zr_pinLoop` and `NTimeDiagonalizer`, both in the replay.

## Brief for the auditor

1. **The statement.** Is `Segment.iterate_seq` true as stated, at the right generality, and named
   and documented for public use?
   - All segments share the forbidden set `F` and the head relation `P`; the starts `cs r` are
     arbitrary. Is a per-segment `F r` or `P r` needed for a consumer like G5, or does `mono`
     (weakening) cover it?
   - `h0` is used only at `n = 0` (`Segment.zero` needs `P` at the start). It is kept so that
     the lemma holds at every `n`, as `Round.iterate_seq` does.
   - The argument order follows `Round.iterate_seq` (`cs τ h0 n h`), less its anchor hypothesis
     `ha`.
2. **The home.** It sits in the `Segment` namespace beside `Segment.trans`, in `Contract/Basic`,
   the generic segment and contract layer, which every consumer already imports.
3. **The corollary.** Is `Round.iterate_seq`'s new proof right, and is anything lost? Its
   statement is unchanged (`evidence/freeze/`), and its consumers re-elaborate in the replay.
4. **Rule 10** (`evidence/rule10/`). Sealed copies of both proofs, with `MultiTapeTM.runFrom`,
   `Segment`, `Round` and `roundStop` irreducible, elaborate with 0 diagnostics. The 8 controls
   (a delta goal and an equation goal per sealed definition) all pass unsealed and all fail
   sealed. All four files were re-run on `oleans-lsi2`, the replay's snapshot, with outputs
   identical to the first run (`runs-lsi2.txt`). Does either proof reach any other definition?
5. **Duplication** (`evidence/screen/`, `evidence/sweep/`).
   - **The screen:** the v3 screen over 17 files (`population.txt`: every campaign `.lean` file
     that mentions `Segment`, among them `CounterLoop`, `ZoneRebalance`, `NTimeDiagonalizer`,
     `CfgRecord`, `WindowRun` and the `Machines` simulators), at base and head, restricted to pairs
     with a `Contract/Basic` declaration on one side.
     - **Base and head are identical**: 1,339 declarations, 778 pairs and 285,948 characters
       each; 0 new pairs, 0 gone (`pairdiff.txt`). The same 23 pairs have a `Contract/Basic`
       declaration on one side at both (`restricted.txt`), all inside the file's existing
       contract, segment and round layer, and none involves either `iterate_seq`.
     - The declaration count is unchanged because `Round.iterate_seq`'s new body (54 characters
       without whitespace) falls under the screen's 60-character cut-off, while
       `Segment.iterate_seq` (124) enters. The induction moved; it was not copied.
   - **The sweep:** every declaration of the head's 925 `.lean` files with an induction, a
     `Segment`, a `.trans` and a range sum. Two match: `iterate_seq` itself, and `zr_pinLoop`,
     whose induction is on its validity invariant and which composes its rounds by
     `Round.iterate_seq`.

   Does anything else re-derive the composition, including inline steps?
6. **Lint** (`evidence/lint/`).
   - The campaign lint on `TuringMachine`: 0 FAIL, 71 WARN over 92 files at base and at head. The
     only change is the size WARN on `Contract/Basic`, 1,473 → 1,487 lines.
   - The policy linter: the same one finding at base and head, `Contract/Basic`'s size. The file
     was over 1,000 lines when it landed (gate 15); file size alone is not a reason to split
     (user rule).

## Repository-side attestations (verify or challenge)

- **Axioms** (`evidence/axioms/`): `Segment.iterate_seq`, `Round.iterate_seq` and `Round.iterate`
  are on `[propext, Classical.choice, Quot.sound]`.
- **Freeze** (`evidence/freeze/`, `declfreeze.py` from the base to the head): public 91 → 92; added
  `Turing.Segment.iterate_seq`; none removed; the one changed body is `Turing.Round.iterate_seq`'s;
  the one private declaration is unchanged.
- **Replay** (`evidence/merged-tree/`): `replay-lsi2` at `7b5774fb`, the downstream closure of
  `Contract/Basic`, 112 modules, chained from `oleans-ldwa3` (the campaign after #196). It passed:
  112 modules, 0 failed. The static check found 0 mismatches. The only `sorry`s are the campaign's
  existing 45: `RecordTable` 4, `TQBF` 21, `RAMSimulation` 14, `Hierarchy` 4, `Savitch` 1 and
  `TwoTapes` 1 (G5's own `two_work_tapes_run`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/98-segment-iterate-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `segment-iterate-api-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
