# Gate 134 · `SAT_exists_linear_verifier` in ClassNP/SAT (PR #301)

**Not yet clear to merge** · PR #301 is a draft. Seyoon dispatches and merges.
The Lean commit is `785e34262460b8ad9330e3c403ebfa76cc641cc1`, against campaign Lean
`5ab222167eb12664d97d255766c5def15b6d5d50` (the campaign after #296). This is the first audit.

## Scope and ruling

Seyoon approved on 2026-11-14 (Ladner decision LD9; `campaign/backlog.md`, P3.4) the reader

```lean
theorem Complexity.SAT_exists_linear_verifier :
    ∃ V : Language Bool, V ∈ P ∧
      ∀ x : List Bool, x ∈ SAT ↔
        ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V
```

immediately after `SAT_mem_NP` in `ClassNP/SAT.lean`, proved by
`⟨satVerifier false, satVerifier_of_poly false satVerdict_false_poly, sat_verifier_equiv⟩`. The
change is that one declaration (`patch/campaign-to-head.patch` in the carrier, 10 added lines).

## Brief for the auditor

1. Check the statement says what the docstring says, and that it is the exact certificate bound
   of SAT's verifier, not a restatement of `SAT_mem_NP`.
2. Check rule 10: the proof uses only same-file declarations. The whole-proof seal (every
   other-file definition reached made irreducible, `[-simp]` on the `@[simp]` ones) passes, with
   17 sealed definitions and 34 paired controls (each closes natively and fails sealed).
3. Check the copy screen on `SAT.lean`: BASE `declarations screened: 193; copy pairs: 39;
   reproduced text: 11,122 chars`, HEAD `194; 40; 11,185`. The one new pair
   (`evidence/PAIR-DISPOSITIONS.json`) is `SAT_mem_NP` sharing the three witness citations.
   Deriving `SAT_mem_NP` from the reader is a possible later proof change, outside this approval.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the 52-module downstream closure on the
  campaign snapshot after #296 (876 objects; prospective tree
  `adb0a4ba2287fe31478e76de505ab4df158b3204`). 52 passed, 0 failed; the 27 admissions are inherited
  from the campaign.
- Metadata: the new theorem uses standard axioms only. Lint: no new style or campaign finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 230 logical files: replay receipts and
  logs, seal and control sources and logs, metadata, QA, both screens with the population and
  scorer, the campaign version of SAT, the patch, and the drivers. Decode each gzip+base64 blob
  and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate134-sat-linear-verifier-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
