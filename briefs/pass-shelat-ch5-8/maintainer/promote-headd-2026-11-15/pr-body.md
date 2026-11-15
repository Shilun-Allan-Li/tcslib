## Promote `headD_drop_ofFn` to the shared list layer (Gate 29 G29-02)

Seyoon's ruling of 2026-11-15 on Gate 29 finding G29-02 is "promote it now". The finding is that the learning unit's new
`LearnPRF.firstBit_of_pos` (#313, `Randomness/Learning/Random.lean`) re-proves the index-0 case of the public Lamport
bit reader `Authentication.LamportFill.headD_drop_ofFn`. This PR publishes that reader, in generic form, in a shared
layer upstream of both files. The Lamport copy is re-derived from it, proof only. The learning re-point of
`firstBit_of_pos` is a later #313 landing edit, after this PR merges. It is **not** part of this PR.

**Branch:** `promote/pass-shelat-headd-ofFn` at `c18afbe6`. It is 1 commit on `cryptography/pass-shelat-ch2-4` at
`dd98360d`. That tip has the same Lean tree as `711a9f4a`: the commits after it change records only.

### Changes

**`TCSlib/Cryptography/Foundations/BitLists.lean`**
- New theorem `TCSlib.Cryptography.headD_drop_ofFn`, placed right after `headD_drop`, which its proof uses. It has a
  formula docstring and a proof sketch, and no attribute:
  ```lean
  theorem headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
      ((List.ofFn f).drop i.val).headD d = f i
  ```
- It generalizes the Lamport reader from `Bool` with `d = false` to any type and any default. The `headD false` form
  is `headD_drop_ofFn f i false`. The proof is the Lamport proof unchanged.
- One new `## Main results` bullet.
- **Why this home.**
  - `BitLists` is the generic list and bit-vector file ("heads of suffixes" is in its scope). It depends on Mathlib
    only, and it already holds `headD_drop` and `headD_ofFn_one`.
  - It is already in both consumers' closures. `Lamport/MachineSpec` imports it directly. `Randomness/Learning/Random`
    (#313) reaches it through `Asymptotic.Adversary`. So **no import changes**, and there is no cycle, because
    `BitLists` imports no project module.
  - No open PR touches it. #313 touches only `Randomness/Learning*` and #314 only PRF `Defs` and ETT `Reduction`.
    Nor do prf-long's files (`Asymptotic/Defs`, `FromPRF*`, the `Functions` facade, `PrivateKey.lean`).
  - `Asymptotic/ReductionSupport.lean` is also in both closures, but it is further downstream and not Mathlib-only.

**`TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean`**
- `LamportFill.headD_drop_ofFn` is now `:= TCSlib.Cryptography.headD_drop_ofFn m i false` (proof only).
- Its name and statement are unchanged. Its docstring is unchanged except for one inserted sentence: "This is the
  published `TCSlib.Cryptography.headD_drop_ofFn` at `α = Bool` and `d = false`."
- Its use in `run_input` builds unchanged.

No other file changes.

### Checks
- **Statements.** decls2 against `dd98360d` shows 1 ADDED (the new theorem), 0 CHANGED and 0 REMOVED. All 23
  pre-existing declaration headers of the two files (14 in BitLists, 9 in MachineSpec) are byte-identical.
- **Build.** I built with `scripts/lean_check_tree.sh`, one module at a time, with no `lake`, on a tree at the
  `eff2dcd0` base.
  - The queue was 253 modules: the 2 changed files and their downstream (245 modules with them), plus the
    #303–#309, #311 and #312 base delta and its downstream (65), up to root `TCSlib`, `audits/garg-ch1-3/Checks` and
    `audits/pass-shelat/Checks`.
  - All 253 returned rc 0 with 0 errors.
  - The only sorries are the 24 pre-existing ones, including #312's two stated `SeedMajority` sorries.
  - BitLists has 0 warnings. MachineSpec has its 2 inherited warnings.
  - Each of the 249 modules with a same-source reference build produced a byte-identical olean. The 4 without one
    are the 2 edited files and the 2 #312 modules.
- **Axioms.** `TCSlib.Cryptography.headD_drop_ofFn` and `LamportFill.headD_drop_ofFn` depend on `[propext]`.
  `LamportFill.run_input` and `Authentication.lamport_oneTimeSecure` depend on `[propext, Classical.choice, Quot.sound]`.
- **Rule 10.** Seals A and B, strict and coe, pass for both changed files.
  - MachineSpec: 2088/2089 requests (strict) and 2087/2088 (coe).
  - BitLists: 0 requests in each variant, because its closure has no TCSlib module. Its seals are vacuous, and no
    control row can apply to it.
  - Paired controls for MachineSpec use the Lamport review rows: `padFin`, `ProbComp.expect`, `ProbComp.sample`,
    `OracleComp.bind`, `secretWord`, `signatureBlock`, `LamportMachine.u`, and `PolyExpr.eval` in B. The result is
    ALL_OK in both harnesses: 4 probes and 15 sealed negatives each.
- **Lint.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives 92 FAIL and 101 WARN at both the parent and
  the head, with identical FAIL and WARN lines. Max line width is 100 in both files, unchanged; no line is over 100.

Evidence: `dl-review/promote-headd/` (PROVENANCE.txt, SHA256SUMS), zipped as `dl-review/promote-headd-evidence.zip`.

### Follow-up
- #313 (learning landing edit, after this merges): re-derive `LearnPRF.firstBit_of_pos` as
  `rw [firstBit_eq]; simpa only [List.drop_zero] using TCSlib.Cryptography.headD_drop_ofFn y ⟨0, hn⟩ false`.
  This needs no import. The shape was checked by statement matching only, not run.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
