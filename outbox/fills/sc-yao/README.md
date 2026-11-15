# Fill `sc-yao` (U3: Yao's protocol in the OT-hybrid model)

The job proves the last two core admissions of the secure-computation plan, in
`TCSlib/Cryptography/SecureComputation/Yao.lean`: `yaoHybrid_polyTime` (line 841; [PS10, Definition 155.1],
the efficiency clause) and `yaoHybrid_simulators` (line 907; [PS10, Theorem 163.7], with the one-active-key
simulator of [LP09]), both in the OT-hybrid model. With them the proved `yaoHybrid_hbcSecure` is Theorem 163.7 in
that model.

**The base is `6ce4658db08a1dc2a03a149987197660db078011`,
the head of `cryptography/pass-shelat-ch2-4`.** In it, sc-garble's `yaoSeed_good_whp` and
`sliceMultiMessageSecure_of_prfOut` are still `sorry`. The worker cites them as frozen statements, so the
simulators are proved modulo sc-garble, and `sc-yao` lands after it. `Yao.lean` is shared with sc-garble. The
worker owns only the two bodies, their sketch paragraphs, the `## Main results` bullet and one hub import line
(ruling SY-1), within a line budget (SY-2). Everything else goes into helpers under `SecureComputation/Yao/`.

**Rulings SY-1 to SY-6 are open** (the brief's last section; recommended options first). The brief is written for
the recommendations. The maintainer adds Seyoon's answers as `ruling-SY.md` and re-pins the dispatch prompts before
dispatch.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). On Seyoon's Mac, the
host addendum `outbox/fills/codex-host-2026-11-15/host-addendum.md` applies to this unit as it did to sc-garble
(single agent). Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 184 TCSlib modules, generated at the base. These are the upstream closure of the
  modules downstream of `Yao.lean`, and of the modules helpers may import (`Games/Efficiency`,
  `NonMalleability/Simulation/Generic`, `GraphIsomorphism/EfficiencyRep`, `CircuitComplexity/DAGCircuitSatLang`).
- [Mathlib roots](roots.txt): 76.
- [Source hashes](SOURCE-SHA256SUMS) at the base.
- [Base admissions](base-sorries.txt): 32 declarations in 15 modules. The only change must be the removal
  of the two targets (30 in 15 modules; a partial final 31).

The worker returns checkpoints and the final payload only at `inbox/fills/sc-yao/` on the exchange. Seyoon
dispatches.

**Ready to dispatch after rulings SY-1–SY-6**
