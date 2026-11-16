# Gate 142 · Removing the held RD-2/H6 route (PR #328)

**Not yet clear to merge** · PR #328 is a draft. Seyoon dispatches and merges.
The Lean commit is `dcbab37806581f2bd0fd24cb55fee75fcacd2dab`, against campaign Lean
`20394834d86a509ad5776c36dbbfccc33b023306` (the campaign after #325). This is the first audit.

## Scope

Chapters 3–4 closeout, work package W2 (`campaign/closeout/PLAN.md`, bundled). Seyoon ruled on
2026-11-16 (decision D1) to remove the RD-2/H6 route: a closed-form configuration codec for
Claim 4.4(2) with 41 admissions, held since 2026-10-14 and used by nothing since TQBF's hardness
was proved through the ARM route and `Complexity.Codec`. The census (`campaign/closeout/census/`,
bundled) shows these were the only admissions in the chapter 3–4 scope.

One maintainer commit, `dcbab378`:
- `ClassPSPACE/TQBF.lean`: delete the two `Complexity.ConfigCodec` blocks (64 declarations, 21 of
  them admitted) and the two `FormulaKit` imports. Kept unchanged: `PSPACEHard`,
  `PSPACEComplete`, the collapse corollary, the proved Claim 4.4(2) theorem
  `exists_adjacency_codec_cnf` with its fill appendix, `TQBF`, and Theorem 4.13 (`TQBF_mem_PSPACE`,
  `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`). The module docstring and the docstrings of
  `exists_adjacency_codec_cnf` and `TQBF_PSPACEHard` no longer describe the removed route.
- Delete `FormulaKit.lean`, `FormulaKit/Gate.lean` and `FormulaKit/Emit.lean` (20 admissions), and
  their import in the root `TCSlib.lean`.
- `ClassPSPACE.lean` and `ClassPSPACE/TQBFHard.lean`: docstrings only.

## Brief for the auditor

1. **Nothing kept depends on what is removed.** Check that no remaining file in the PR's tree
   imports a deleted module or names a removed `ConfigCodec` declaration, and that the
   removed code had no consumer (search the tree; the evidence's replay driver asserts no
   remaining module imports a deleted one).
2. **Statements.** Check that every remaining declaration's statement is unchanged; the
   inventory (`evidence/SOURCE.json`) lists 64 removed declarations, no added one, and two
   changed declarations (`exists_adjacency_codec_cnf`, `TQBF_PSPACEHard`) whose changes are
   docstring-only. Check the docstring edits are accurate and keep their citations.
3. **Admissions.** Check that the three changed modules have no admission, and that the chapter
   scope's census now has none.
4. **Rule 10.** Seals (`seals/`): the two changed proofs pass with every other-file definition
   they reach irreducible (24 definitions); the 48 paired controls each close natively and fail
   sealed. These proofs did not change; the check confirms the removal did not disturb them.
5. **Lint and screen.** The campaign lint's check-8 warning on `TQBF.lean` shrinks from 28
   definitions to 2 (`PSPACEHard`, `PSPACEComplete`, both pre-existing); the normalizer reports
   the shorter message as "new". The copy screen on the three changed files: BASE 125
   declarations and 10 pairs, HEAD 106 and 5; no new pair, five gone with the removed code.
6. **Records.** Check that `campaign/backlog.md` (§2 RD-2) and the closeout plan record the
   ruling.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the changed
  modules (`TQBFHard`, `TQBF`, `ClassPSPACE`) on the campaign snapshot after #325 (876 objects;
  prospective tree `53096cd02c10ea9744ef08b6f0afe464a22ec0ff`). 3 passed, 0 failed, 0 admissions.
  The driver, extended for this gate to allow deleted modules (`drivers/driver/driver.py`),
  removes the three `FormulaKit` objects: 873 output objects.
- Metadata: both changed proofs use standard axioms only.
- `evidence/DATA-CARRIER.json` and its recovery map hold 101 logical files, including the base
  sources of the deleted files. Decode each gzip+base64 blob and check its SHA-256 and byte
  count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate142-remove-rd2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
