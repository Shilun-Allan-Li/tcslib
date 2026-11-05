# Gate 97 (G5's consumer API: the zone step)

- 2026-11-05: decision G5-F1 ruled (API first). Branch `lean/zone-step-api`: `Contract.zero`
  (`Contract/Basic`), `ZoneRebalance`'s equations and the anchor's re-point, `Build/ZoneStep`.
  - The first head `6b989e08` had a private zero-time contract that the restricted screen paired
    with `ZoneRebalance`'s `zr_anchorContract` (99%). Homes first: the public `Contract.zero`
    replaced both. At the final head the screen finds no pair.
  - The chain, the seal (18 definitions, 36 controls), axioms, names, lint and freeze are in
    `evidence/`. The pack's PR, head, base and replay fields are filled at the push and the
    replay.
- 2026-11-05: pushed; #197 opened at `0a1b64d5` (rebased onto the campaign at `683e2adf`, records only since `a8b27271`). `replay-lzsa` written: 111 modules, the closure of `Contract/Basic`, precheck passed.
- 2026-11-05: `replay-lzsa` passed (111 modules, 0 failed; static 0 mismatches, the existing 45 `sorry`s). The changed-files screen (22 files) found no new pair. The pack is complete; the gate is staged.
