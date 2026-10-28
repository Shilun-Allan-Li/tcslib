# Maintainer's notes on the cont1 review (2026-10-27)

**Spot checks of the review's claims** (the review is a sub-agent's): the landed file's freeze
against the base and the head (`out/28-land-checks.txt`: 22 → 22 public, no statement changed, the
22 body or docstring changes of E1–E4); E3's lemma `Nat.size_eq_bits_len` exists in the pinned
Mathlib (`Mathlib/Data/Nat/Size.lean:126`). Both confirmed.

**F14 (minor; found by the maintainer, not in the review).** The policy linter
(`scripts/style_lint.py`, the check "proofs > 20 lines have **Proof sketch.**", which counts the
statement with the proof) flags nine new privates of the landed file: `qy_hosted'` (line 521),
`qy_hosted_last` (563), `qy_copy` (641), `qy_copy_over` (671), `qy_clear` (745), `qy_writeConst`
(771), `qy_step` (965), `qy_rndP_le` (4315), `qy_not_scratch_tp` (4534). The review's lint line is the
campaign linter's (`campaign_style_lint.py`, 0 FAIL), which does not make this check; the worker's
`lint.log` is the same. Beside them, the size finding (5,390 lines) is expected (file size alone is not
a driver). **Fix (landing edit E5):** a one-paragraph `**Proof sketch.**` in each of the nine
docstrings, by the maintainer at landing; text only.
