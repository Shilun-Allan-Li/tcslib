# Gate 03l (the `Randomized/Build/` machine layer and the clean-module host): round 2 resolutions

- **Round:** findings `findings/gate03l-r2-findings.md`, SHA-256 `f62ddbf98aad38786f122cd7a51c1ad30e858bb0913eaffcde87fb923fe1574b`; pin `e28773ef`. **0 blockers, 1 major, 3 minors**; round 1's major repaired.
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| 1 | major | **Fixed** (#206, item B). `Turing.ModuleHost.Clean.envelope` (every work head within `B |arg|` of the origin at every time of a clean module's run), `host_call_envelope` (within `t` cells for all `v ≤ t`, from the call seam), `host_clean_envelope` (`host_clean`'s conclusion plus the envelope `B |arg|`). These are coarse bounds from the time bound, through `MultiTapeTM.workTapePos_step_le` and `workTapePos_runFrom_mem_Icc`; the docstrings say the contract gives nothing sharper. Registry row H14 lists them. No existing statement changes. |
| 2 | minor | **Fixed.** `evidence-repairs/03-batch/axioms-03l.log` prints the eight `simps`-generated equations and the three new lemmas; all standard. |
| 3 | minor | **Fixed.** The round 3 attestation names `campaign_style_lint.py --check8b` and its log. |
| 4 | minor | **Fixed (records).** DL-20's milestone is the `main` landing in both the ledger and `resolutions-03l-r1.md`. |
| 5–10 | note | No change. |
