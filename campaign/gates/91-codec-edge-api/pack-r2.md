# External audit pack, round 2: the configuration codec's edge mode (PR #184, an API gate)

**Round 1** (`pack.md`; findings `findings.md`; resolutions `resolutions.md`): **FAIL, 0
blockers, 1 major, 4 minors.**
- **The major:** the private `upd_le` re-proved `LogProg.register_update_le`.
- **The minors:** four `by simp [W]` unfoldings of `Word`'s `W` in `Machine`; CL-1's per-file
  accounting; the site equations' and `Checks`' docstrings; the design note's stale independence
  sentence.

No defect was found in the statement or the decider's contracts.

**The PR now:** #184 on `lean/codec-edge`, head `b360808c150fbab8ddd4fd1888e8bffaf75fa3a6`, still
stacked on #182's `940932752e598b4a452311465dee81adea46d17b`. The fix is one commit
(`evidence/round2/patches/0004-…`) in three of the seven files: `Deciders`, `Machine` and
`Checks`.

## What changed since round 1 (verify)

| File · declaration | Change |
|---|---|
| `Deciders` · private `upd_le` | removed; its 13 uses in `edge_round` and `edge_tail` now cite `register_update_le _ r _ _ hv hn` |
| `Machine` · `cpNext`, `icNext` (the new arms), `cpNext_Ue`, `icNext_S1` | `⟨0, by simp [W]⟩` becomes `⟨0, by rw [W_eq]; omega⟩` |
| `Machine` · the 24 site equations, `cpDst_Ue` … `icNext_S2` | docstrings state each register, factor, count or exit |
| `Checks` · module docstring | five languages; the edge check described |

The records: `campaign/duplication-ledger.md`, CL-1's census; the design note's §7 sentence,
superseded.

## Brief for the auditor

1. **Finding 1.** Is `upd_le` gone, with every use now citing `register_update_le`? Does any other
   helper of the PR re-prove existing material? The screen is in `evidence/round2/screen/`.
2. **Finding 2 and rule 10.** Is any other-file definition still unfolded explicitly or by
   reduction in the PR's new code? `evidence/round2/unfold-scan.txt` lists every definition named
   in an added `simp`, `rw`, `unfold` or `delta`. The sealed copies and controls were re-run at the
   head (`evidence/round2/rule10/`).
3. **Findings 3–5.** Are the ledger's CL-1 census, the docstrings and the design note now
   accurate?
4. **Unchanged since round 1:** confirm that `Word`, `Langs`, `Run` and `Parse` are byte-identical
   to round 1's head `8d43e126`, and that `Machine`'s changes still only extend
   (`evidence/round2/freeze/Machine-extension.txt`).

## Repository-side attestations (verify or challenge)

- **Elaboration chain** (`evidence/round2/elab-chain/`): all 16 `Codec` modules at the head,
  compiled in dependency order into a fresh copy-on-write clone of #182's compiled head; 0
  diagnostics each.
- **Rule 10** (`evidence/round2/rule10/`): the three sealed copies elaborate with 0 diagnostics.
  Controls: unsealed 73 of 74 pass (`vword`'s delta goal fails, as before); sealed, all 74 fail.
- **Census and axioms** (`evidence/round2/census/`):
  - `Machine` 1149 → 1151, the two auxiliaries of the `W_eq` proofs;
  - every other module as round 1;
  - 16 axiom prints, 14 on the standard three and 2 without `Classical.choice`.
- **Freeze, screen, lint** (`evidence/round2/`):
  - freeze: the public counts as round 1; `Deciders`' privates are 0 → 2;
  - screen: 171 → 185 declarations, 58 → 83 pairs, the same 25 new (CL-1);
  - lint: 0 FAIL and 83 WARN, the list unchanged; `style_lint` gives 0 findings on all seven files.
- **Replay:** as in round 1 (note 15). After #181 and #182 merge, #184 is retargeted, merged with
  the campaign and replayed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/91-codec-edge-api/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `codec-edge-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
