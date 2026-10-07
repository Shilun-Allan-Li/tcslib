# Chapter 2, Epoch 1, Batch C

**Complete: all six targets filled and verified in the prescribed order.**

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Base: `7494522e8826be6b54675307668435afc59c005d`.
- Final commit: `c585da049fbd1fa18883034f0397cbe9bfcf921b`.
- Work performed on `complexity/arora-barak-ch1`, as requested in the follow-up.
  The delivery alias `fill/ch2-e1-C` points to the same final commit; the working
  branch remains `complexity/arora-barak-ch1`.

## Targets versus the frozen sketches

| Target | Completed proof |
|---|---|
| `P_subset_NP` | Uses coefficient and degree zero and the original language as verifier; length zero forces the empty certificate, reducing the equivalence to identity. |
| `compl_mem_P` | Reads the decider pointwise as a singleton-indicator function, applies the fixed Boolean postprocessor through **timed** composition, and absorbs its explicit budget using `mem_P_of_dtime_le`. |
| `mem_coNP_iff_forall` | Negates the certificate quantifier and complements the verifier in both directions, preserving the same coefficient and degree. |
| `P_subset_NP_inter_coNP` | Combines the empty-certificate inclusion with complementation of the original polynomial-time language. |
| `NP_eq_coNP_of_P_eq_NP` | Proves both set inclusions by rewriting the assumed class equality and using complement closure; the reverse direction complements twice. |
| `P_subset_EXP` | Uses `Nat.lt_two_pow_self`, `DTIME.mono`, and absorption of the factor two into the existing time constant. |

## Declarations, requests, and scope

- New public declarations: **none**. New private declarations: **none**.
- Removed declarations: **none**. Requested shared lemmas: **none**.
- Campaign escalations: **none**. Sketch appendices: **none**.
- The diff touches exactly `ClassNP/NP.lean`, `ClassNP/CoNP.lean`, and
  `ClassNP/EXP.lean`: 73 inserted lines and six removed `sorry` lines.
- Restoring only the six target proof bodies reproduces each entire original
  file byte-for-byte. Thus all signatures, definitions, imports, option headers,
  docstrings, attributions, and other proofs are unchanged.
- The owned files retain exactly the three out-of-scope admissions:
  `mem_NP_iff_exists_length_le`, `NP_subset_EXP`, and `EXP_subset_NEXP`.
  Every other batch's sources are untouched.

## Verification

- Lean **4.25.0**, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib **029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e**; tracked dependency source is clean.
- Dependency setup used `lake exe cache get`, restricted after a slow full-cache
  attempt to all 25 direct Mathlib imports of the prescribed order list
  (912 transitive cached modules). The official compiler ran natively because
  the sandbox launcher failed to locate the application. No compiler or
  verification-script modifications were made; `lake build` was never invoked.
- Initial bootstrap: **53 successful module checks, zero `error:` lines,
  59 admission warnings**.
- Each target edit was checked with `scripts/lean_check_tree.sh`, followed by
  every later module in the prescribed order. Successful logs are included.
- Final sweep at the final commit: **53 successful checks, 53 fresh nonempty
  `.olean` files, zero `error:` lines**, using a previously nonexistent output
  directory. Exactly **53 admission warnings** remain: the original 59 minus
  these six targets, all outside this batch.
- All six axiom prints below came from that final output tree and contain
  exactly the required standard triple, with no `sorryAx`.
- Owned-file style lint: **zero FAIL, zero WARN**. `git diff --check` passes.
- The incremental git bundle verifies against the stated base. Replaying the
  format-patch series on the base's three files reproduces the committed and
  packaged sources byte-for-byte.

Final sweep tail:

```text
BEGIN TCSlib/Complexity/ClassP
PASS TCSlib/Complexity/ClassP
BEGIN TCSlib/Complexity/Uncomputability
PASS TCSlib/Complexity/Uncomputability
BEGIN TCSlib/Complexity/Formulas
PASS TCSlib/Complexity/Formulas
BEGIN TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
BEGIN TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
SWEEP COMPLETE: 53 modules
```

Complete axiom-print log:

```text
'Complexity.P_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.compl_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_coNP_iff_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_NP_inter_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NP_eq_coNP_of_P_eq_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_EXP' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Archive contents

`REPORT.md`; the three full sources under their repository-relative paths;
`patches/` containing the one-commit `git format-patch` series;
`fill-ch2-e1-C.bundle`; `logs/` containing the bootstrap, successful per-target
checks, final sweep, axiom prints, scope/style checks, and patch/bundle checks;
`verification/` containing the axiom-print input, 53-module order, and pins;
and `SHA256SUMS` covering every other archive member.

The bundle is incremental and requires the base commit listed above. The patch
series is ready for the campaign's `git am -3` integration. After extraction,
`sha256sum -c SHA256SUMS` verifies all packaged files.
