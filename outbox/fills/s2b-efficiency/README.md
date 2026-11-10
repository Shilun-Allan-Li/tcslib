# Shared reduction efficiency fill

Claude is the selected worker. The proof base is
`b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on `cryptography/pass-shelat-ch2-4`.
Read [the brief](brief.md) and [environment addendum](fill-environment-addendum.md).
Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt) lists 137 TCSlib modules with the GGM reduction
  dependency before `Games/Efficiency`.
- [Mathlib roots](roots.txt) lists the 68 direct Mathlib imports of that order.
- [Source hashes](SOURCE-SHA256SUMS) can be checked from the clean issue
  checkout before adding the GGM import or helper files.
- [Base admissions](base-sorries.txt) lists the source admissions in that order.
- `EfficiencyPrerequisites.lean` and `EfficiencyCostProbe.lean` are scratch
  route probes. Copy them to the issue checkout for replay through
  `scripts/lean_check_tree.sh`. Keep them outside the proof patch.

Claude returns checkpoints and the final payload only at
`inbox/fills/s2b-efficiency/` on the exchange. Seyoon dispatches.

**Ready to dispatch**
