# Pairing `Group.lean` dedup (DW-11 follow-up) · report (commit 1)

Filed by the maintainer from the job's returned report (the harness refuses report-file writes by sub-jobs). A second
commit (`pow_val_mul_GT`, module docstring line) follows; this file and the evidence zip are updated when it lands.

- **PR:** draft #365, `fix/pairing-group-dedup` → `cryptography/pass-shelat-ch2-4`. Head `6fc5f49456507dab5901045356ea40acf42bdd67`
  (tree `ba10f0a2`), parent records tip `5aed99076d2bd4e5d6f831aed88739fc3ce475b6` (Lean = TS2 `13fc8060`). One commit,
  SSH-signed with the records key, trailers as required.
- **Mathlib search:** no exact statement; nearest `IsCyclic.unique_zpow_zmod` (an `∃!` in `ZMod (Fintype.card α)`),
  `zmodCyclicMulEquiv`, `finEquivPowers`, `finEquivZPowers` (different shapes).
- **New lemma** (public, in `TCSlib.Cryptography.Pairing`, before `namespace BilinearGroup`; formula docstring, glue note,
  sketch): `pow_val_bijective_of_prime_card {M} [Group M] [Fintype M] {p} [Fact p.Prime] (hM : Fintype.card M = p)
  {g : M} (hg : g ≠ 1) : Function.Bijective fun a : ZMod p => g ^ a.val`, from `orderOf_eq_prime`, `pow_card_eq_one`,
  `pow_injOn_Iio_orderOf` and a cardinality step.
- **Touched proofs (bodies only):** `pow_val_bijective` and `pow_val_bijective_of_ne_one` (one-liners from the new lemma);
  `pow_val_add` and `pow_val_mul` (`pow_mod_card x … , B.card_G`). +25/−17 in one file; all statements and docstrings
  byte-identical.
- **Checks:** decls2 1 ADDED / 0 / 0; replay on a `cp -al` copy of `olean-replay-cs1-s6` (`$SP/olean-replay-grpfix`): 22
  rebuilt / 1412 reused, all rc 0, 0 errors/sorry/warnings, state 1434/1434 OK, link count 1, parent and snapshot #6
  rehash 0/0/0, output map `5ada820f…`; only `Pairing/Group.olean` differs from the parent. Admissions 192 = 192 per
  module. Axioms: new lemma, the 4 touched, `bb1_sidSecure`, `jouxKeyIndist_of_dbdhAssumption` standard; empty `sorryAx`
  traces; all 83 `Pairing.Group` constants standard. coe-A on `Group.lean`: 567 requests base and head, 0 errors,
  identical rows and logs. Lint: 92 FAIL / 103 WARN, no new lines; `style_lint` 0.
- **Deviations:** a trial compile of an earlier draft and one standalone probe (`NeZero p` from `Fact p.Prime`); the first
  base axioms run lacked `lean-toolchain` (no Lean ran; rerun passed); the admissions census used a new script
  `censusderive.py` because older record sets under `$SP/g44/` had been deleted by the maintainer's disk cleanup.
- **Evidence:** `group-dedup-evidence.zip` (`2d4a8045…`, 162 files with inner SHA256SUMS; the diff is
  `run/group-dedup.diff.txt`, `da3ffe6c…`). Run 2026-11-17 18:20–18:45 UTC, job dir `$SP/grpfix-work`.
