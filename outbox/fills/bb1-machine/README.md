# Claude fill `bb1-machine` (pairings T4 `exists_bb1_distinguisher`: finish from the in-house checkpoint)

Claude is the worker, a lead with up to 1 sub-agent (Seyoon's ruling, 2026-11-16: external Claude jobs for parallelism,
the T4 finish among them). The job proves T4 of
`TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` from the in-house checkpoint. It inserts
the seven frozen-file readers Seyoon approved (scope request, minimal form, 2026-11-16) and moves the ready glue into a
helper module. The readers land in the T4 PR as pure insertions; #331 is unchanged, and Gate 44 (Codex) checks they are
insertions only. T2/T3 (`bb1-sim`) are out of scope.

**Base.** `7c0a55e0239c14786612d0cd4462e64238543ca1`, the tip of `fill/pairings-bb1-machine` (pushed). It holds three
signed in-house checkpoint commits on #331's head `9e7a96481785d6cac4dea3b2e990c49ac278b060` (Gate 40 CLOSED). T4 is
still `sorry` there. The worker delivers a series on top of it.

**Checkpoint material.**
- On the records branch `cryptography/pass-shelat-ch2-4` at `99eae2c1550ee0b0485f115bca76b254dae25064` (or later):
  `briefs/pairings/fills/bb1-machine/inhouse-r1/`, with `REPORT.md`, `fill-bb1-machine-evidence.zip` (SHA-256
  `eeaa5c787187c977adb91617c577bb6d98987714138f282453590659b50a2580`) and `scope-request/`.
- On the exchange, this pack also carries `checkpoint/`, manifested by `checkpoint/SHA256SUMS`: the checkpoint's
  `REPORT.md`, the approved readers' source `BB1ReadersMin.lean.txt`, the T4 probe `MachineProbeMin.lean.txt`, and the
  checkpoint's tools (the zip's `tools-used/`, the drivers and the axioms probe).

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory, and on the exchange also with `shasum -a 256 -c SHA256SUMS` from
`checkpoint/`.

- [Build order](order.txt): 188 TCSlib modules, generated at the base, imports first. They are the upstream closure of
  the modules downstream of the owned files: `BonehBoyenSecurity` and the facades `IdentityBased` and
  `AdvancedEncryption`. The root `TCSlib` (the whole library, 1301 modules) is excluded, as in every fill of this
  campaign; the maintainer checks it at landing.
  - No extra import is authorized or needed: the probe's `Asymptotic.EnsemblesLemmas` is already upstream of
    `Reduction`.
- [Mathlib roots](roots.txt): 94.
- [Source hashes](SOURCE-SHA256SUMS) at the base.
- [Base admissions](base-sorries.txt): 57 declarations in 18 modules.
  - **The pairing campaign's are T1–T4:**
    - T1 `bdhAssumption_of_dbdhAssumption`, proved in #340 (`916afc25c21f5e52b4b01958186ad55d2f615fd1`) but **not on
      this base**;
    - T2 `bb1_sim_real` and T3 `bb1_sim_random`;
    - T4 `exists_bb1_distinguisher`.
  - The other 53 are upstream of the facades and out of scope: the 35 GSW statement targets (proved by #338/#339, not
    on this base) and 18 Complexity Turing-machine admissions.
  - The only change must be the removal of T4: 56 remain, in 17 modules.

Claude returns at least one checkpoint and the final payload only at `inbox/fills/bb1-machine/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
