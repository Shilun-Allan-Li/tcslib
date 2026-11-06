# Gate 07 (Pass–shelat ch. 2–8), round 3: closing check of round 2's findings

**What is audited:** PR [Shilun-Allan-Li/tcslib#210](https://github.com/Shilun-Allan-Li/tcslib/pull/210)
at `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee`, one commit on round 2's head `3436321ba28042549bead976dc654aab3d661f10`
(docstrings only, three files: `evidence-r3/repair-r3.diff.txt`), base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`.
This round checks **only** round 2's findings R2-01 – R2-03 (`findings/gate07-eqlemmas-r2-findings.md`,
`resolutions-r2.md`) and the one repair commit. Round 2's other conclusions stand.

**The source** is [PS10], `Pass–Shelat.pdf` at the root of `cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`); not needed unless you want it.

- **The deliverable:** **`gate07-eqlemmas-r3-findings.md`**, committed as
  `inbox/gate07-eqlemmas-r3-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and pushed
  (protocol: that branch's `README.md`; write only that file, `git pull --rebase` first, never
  force-push, no PR).

## Brief for the auditor

1. **R2-01 (major): F02's consumer.** `evidence-r3/probes/` holds probe files that import
   `HardCoreCollection` from outside it; `R2-01-MAPPING.md` maps each example to its line and log line.
   - The seal (`seal-list.txt`, 42 constants): `PermCollection.glPad`, `Collection.glPad`, every plain
     TCSlib definition reached through their elaborated types and values (`R201Collect.lean`/`.log`),
     the matchers reached, and also `PermCollection.glPad_domEquiv`; `PolyExpr.eval` unsealed (Q1).
   - Pass examples P1–P7 (`R201PassSealed`, `R201PassOpen`): the domain equivalence and its round
     trip; the conjugated permutation equation `perm' = e⁻¹ ∘ (perm_i × id) ∘ e` through `glPad_perm`;
     `perm'` applied and inverted, read through `e`; the field `f' = encD' ∘ perm'`.
   - Controls C1–C5 (`R201ControlOpen` rc 0; `R201ControlSealed` exactly 5 errors): the old readings
     (`z.1`, `(x, r)` as a padded-domain element, `perm'` and P3 by `rfl`, and the statement of
     `glPad_domEquiv_apply`).
   - The maintainer's reading of C5: `glPad_domEquiv_apply` (`e z = z`) is an own-file lemma whose
     statement is well typed only by reading the padded domain as the product; consumers do not
     need it — `glPad_domEquiv` with the `Equiv` lemmas and `glPad_perm` state and prove the
     permutation fact. **Is that the right interface, and do the probes show it?** Say whether F02
     is now fixed.
   The probes were run on the olean tree of this head's replay; their logs are in the folder. If you
   have a Lean toolchain you may re-run them; otherwise review the files and logs as in round 2.
2. **R2-02 (minor):** the six docstrings (`invProb_def`, `predProb_def`, `acceptProb_def`,
   `distAdv_def`, `invProbOpt_def`, `glPadInvFun_eq`) now state the formula. Are the formulas right?
   No statement or proof changed (`evidence-r3/decls-vs-3436321b.tsv` is empty).
3. **R2-03 (minor):** (a) `sorry-compare-vs-05fe903f.tsv` (tool `sorry_compare.py`): only Factoring
   8 → 10 and RSA 9 → 10 against the PR base, total 63 → 66, exactly S1–S3; (b) the extractor
   `decls2.py` keeps a `|` line inside a statement when a `match` is open in it;
   `decls-vs-base.tsv` (367 / 58 / 2) and `decls-vs-r1.tsv` (184 / 55 / 2) regenerated;
   `extractor-fix-diff.txt` shows the only changed row is `GGMRed.queryOf_eq`, now with both arms.
4. **The repair commit**: docstrings only; replay of the 105 modules downstream of the three files
   plus Checks, all rc 0 (`replay-head.log`); `style_lint` and check 8b unchanged
   (`style-lint.log`, `check8b-diff.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round-2 item: `R2-01: fixed / not resolved — <reason>` (also R2-02, R2-03), and
`F02: fixed / not resolved`. Severity as in rounds 1–2. The gate closes at **0 blockers and 0 majors**.
