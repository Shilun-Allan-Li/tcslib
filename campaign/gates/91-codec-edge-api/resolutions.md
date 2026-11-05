# The configuration codec's edge mode (PR #184, an API gate): resolutions

**Gate, round 1:** the API gate of PR #184 (`lean/codec-edge` at `8d43e126`, stacked on #182's
`lean/arm-embed`). Pack `pack.md`. **Ruled (user, 2026-11-04):**
- the edge decider's home was decided at pre-ship by the user's rule: a fifth mode of the codec
  machine (design note §7);
- the writer is the maintainer, as an API PR;
- the duplication the screen finds (the edge member of the code languages' families) is ledgered as
  CL-1 for the dedup window.

The edit is additive in Hydroxyi's `Codec` files, under the 2026-10-27 authorization, FYI only (the
user's to send). Bundle SHA-256 `f735178735c65d24b897e5328f97969a2a1c1c188d789d16b59573206f9cc4aa`
(148 sections), the Lean at `8d43e126345a9e94998b1b11f0eee315518ae73f`, the records at `884dda30`.
**Staged (2026-11-04); dispatched (user, 2026-11-04).**

**Replay:** after #181 and #182 merge, as ruled for the chain: #184 is retargeted to the campaign
branch, merged with it, and replayed over its downstream closure from #182's post-merge snapshot.

**Round 1** (`pack.md`, head `8d43e126`). **Findings** (`findings.md`, verbatim, SHA-256
`8d96734e7f52aba99fd34a7d9215821b20df9ddea74d7988bd03cd0bb22d8215`; received 2026-11-04): **FAIL, 0
blockers, 1 major, 4 minors, 10 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The private `upd_le` re-proves `LogProg.register_update_le` (`Logspace/InputAccess`, already imported); outside CL-1. | **True; fixed** (`b360808c`): `upd_le` is removed and its thirteen uses cite `register_update_le`. The screen drops it, 186 → 185 declarations, and its 25 new pairs are unchanged (`evidence/round2/screen/`). |
| 2 | minor | Four new proof terms in `Machine` unfold `W` (`by simp [W]`); no sealed copy covers `Machine`. | **Fixed** (`b360808c`): `by rw [W_eq]; omega`. `evidence/round2/unfold-scan.txt` lists every definition named explicitly in a `simp`, `rw`, `unfold` or `delta` of the PR's added code: only `CA` (inside `Machine`, its own file) and `EdgeOK` (`Deciders`' own private). `astep` is read only through #182's step equations, `CA` through its row equations. |
| 3 | minor | CL-1's per-file accounting is incomplete (`Langs` was already above one fifth). | **Fixed** in the ledger: `Langs` 8/9 → 10/12, `Checks` 4/26 → 5/31, `Deciders` 3/16 → 4/22 (with `upd_le` gone); the acceptance covers `Langs`' existing crossing. |
| 4 | minor | Twenty-four site equations say "See `cpDst_Ue`"; `Checks`' introduction says four languages. | **Fixed** (`b360808c`): each site equation's docstring states its register, factor, count or exit; `Checks` names five languages and the edge check. |
| 5 | minor | The design note's §7 says #184 is independent of #182. | **Fixed:** the sentence is superseded in place. #184 reads the machine through #182's step equations, is stacked on it, and lands after it. |
| 6–15 | note | Provenance, the language's meaning, the check and layout, the adversarial cases, the machine, the deciders' contracts, the seal, the census, names and lint, the replay order. | Agreed. Note 9's optional sanity lemmas (zero tapes, radius zero) are left to the deepening fill, which may state them if it needs them. The replay follows the order in note 15. |

**Round 2 staged (2026-11-04)** at #184's head `b360808c`. Pack `pack-r2.md`; bundle SHA-256
`dc714b814eb7addd38ecc6c0a4da79a05c587107b70d23907b5c2670f02c28d7` (237 sections), the records at `2a202794` (rebuilt
after the evidence's freeze copies were renamed `.lean.txt`). **Dispatched (user, 2026-11-04).** Evidence `evidence/round2/`:
- the elaboration chain: all 16 `Codec` modules at 0 diagnostics, in a fresh clone of #182's
  compiled head;
- the three sealed copies at 0 diagnostics; controls 73/74 unsealed and 0/74 sealed;
- the census: `Machine` gains two auxiliaries from the `W_eq` proofs (`cpNext._proof_3`, `_4`), and
  the rest are unchanged;
- the axioms: 16 prints, unchanged;
- the freeze: as round 1, except that `Deciders`' privates are 0 → 2; `Machine` still only
  extends (`Machine-extension.txt`);
- the screen: 171 → 185 declarations, 58 → 83 pairs, the same 25 new;
- lint: 0 FAIL and 83 WARN, the list unchanged; the policy linter gives 0 findings on all seven
  files.

**Round 2** (`pack-r2.md`, head `b360808c`). **Findings** (`findings-r2.md`, verbatim, SHA-256
`2597887bada7ad29839af904003071b05fbb89ecb4d20f85754cbae252ae9de3`; received 2026-11-04): **PASS, 0
blockers, 0 majors, 3 minors, 9 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `evidence/round2/elab-chain/chain.log` records `8d43e126`, not the head `b360808c`, and ends before the repair's commit time; no source-hash manifest ties the run to the committed files. | **True:** the chain ran on the repaired working tree before the commit, and its header names the checked-out commit. **Fixed** (`evidence/round2-resolution/elab-chain/`, `scripts/elab_chain_r2res.sh`): re-run at #184's head `e6eaaf94` (after minor 2), `TCSlib` clean, in a fresh copy-on-write clone of `oleans-larm` (`replay-larm`, 138/138 at #182's `8fd6f91a`). The log names `ARMProof` as the one Lean file outside `Codec` that differs from `8fd6f91a`. `ARMProof`'s dependents among the Codec modules' imports are recompiled first (6 modules), then the 16 Codec modules: **22 of 22 exit 0 with empty output**, each with its blob at HEAD equal to the compiled file's hash (`Machine` 88 s). |
| 2 | minor | Seven PR-new docstrings are labels, not statements (`mem_edgeLang_iff`, `mem_edgeLang`, `edgeChk_def`, `edgeLang_iff`, `CA_acc`, `CA_rej`, `CA_vDone_edge`). | **True; fixed** on #184 (`e6eaaf94`, docstrings only, `style_lint` clean): the four membership and check lemmas state their equivalences, `CA_acc`/`CA_rej` the returned bit in every mode, `CA_vDone_edge` the jump to `eStart` when the scan accepted and to `rej` otherwise. |
| 3 | minor | The pack's inventory omits `edge_loop` (13 calls: 6 in `edge_round`, 2 in `edge_loop`, 5 in `edge_tail`) and says 24 site equations where there are 25 (9 copy, 4 scale, 12 increment). | **True; corrected here.** `pack-r2.md` stays as dispatched. |
| 4–12 | note | Integrity and scope, `upd_le`'s removal, CL-1's census, rule 10, the language's meaning, the machine, the census and axioms, lint, the replay order. | Agreed. On note 12, the replay order stands: #181, then #182 with its merged-tree replay, then #184 retargeted, merged with the campaign and replayed. |

**Gate 91 closes (round 2, PASS, 2026-11-04).** Minors 1–2 fixed (#184 at `e6eaaf94`). **#184 is not
yet clear to merge:** it is stacked on #182, and its merged-tree replay comes after #181 and #182
merge.
