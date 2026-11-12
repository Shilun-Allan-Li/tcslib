# Gate 17 · resolutions (round 1)

**Verdict received: CLEAR** (Codex). The findings had 0 blockers, 0 majors, 2 minors and 0 notes, at audited head
`63ca0eb3dccb65542e90c181b7ceb0a4a4a46272`. The findings are stored verbatim in `findings/`, with a SHA256SUMS file.
**Gate 17 is CLOSED.**

| ID | Severity | Resolution |
|---|---|---|
| G17-01 | minor | **Fixed.** Added a public, non-`@[simp]` lemma `PRFGame.LState_eq` beside the abbreviation, proved by `rfl`. Its docstring states the product-type expansion. My review's item 9 ("no action (abbreviation)") was wrong: policy §1 requires every new public `abbrev` to land with an `_eq` or `_iff` lemma. |
| G17-02 | minor | **Fixed.** The CPA deviation paragraph now says that [PS10]'s proof is qualitative (a PRF reduction and a negligible collision event). The `2 · prfAdv + q(n)/2ⁿ` bound and the bit-in-seed layout are now attributed to the issued brief. The CCA1 docstring only says "as for CPA", so it needed no change. |

**Remark accepted.** The auditor notes that covering later encryption collisions shows the quadratic term is
sufficient, not that it is necessary. That is correct. The review's sentence "`q²` is needed" overstated the point;
the quadratic term is what the proof's query-by-query argument gives. An erratum has been added to the review.

## Resolution commit

Commit `980eed05dae718a38825622ba6e49d69cc1c8bdb` on `land/pass-shelat-pk-cpa-cca1`, the new #293 head (parent
`63ca0eb3`). It changes two files and adds 7 lines: `OracleFromPRF/Lazy.lean` (+5) and `OracleFromPRF.lean`
(+2/−1, docstring only). No statement or proof route changes.

## Checks (`landing-r2/`)

- **Rebuild:** the 28 downstream modules, run in `root-order.txt` and through `TCSlib`, are all rc 0 with 0
  errors on the full-library tree.
  - Every row's `source_sha256` matches the Git bytes at `980eed05`.
  - Warnings and admissions are unchanged from the pre-fix run. They are four pre-existing admissions in
    `EncryptThenTag` and `NonMalleability/{Indistinguishability,Simulation}`, none in a changed file.
- **Axioms:** `axioms-head.log` gives `[propext, Classical.choice, Quot.sound]` for `prfFixedScheme_cpa`,
  `prfFixedScheme_cca1`, `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2`. `LState_eq` uses no axioms.
- **Rule 10:** the new lemma reads only its own file's abbreviation. The docstring edit has no proof content.
