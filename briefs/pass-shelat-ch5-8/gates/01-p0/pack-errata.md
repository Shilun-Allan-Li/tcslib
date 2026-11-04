# Gate 01: pack errata

The pack is shipped and is not edited; corrections are recorded here and carried into the
resolutions.

| # | Pack location | Erratum | Found |
|---|---|---|---|
| E1 | Attestation 5 ("No copy found") | Wrong. `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, present on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`, **not on `main`**) states `|∑ g ∈ T, (p g - q g)| ≤ statDist p q` for a test set `T`. That is the content of #183's `abs_probTrue_sub_le_statDist` (a test given as `D : α → Bool` instead of a `Finset`), with the same proof. The screen matched declaration names, not statements, so it missed this. `distAdv_le_statDist` in the same file is the coin-averaged form; it has no counterpart in #183. Not a copy on `main` today; it becomes one when the concrete layer lands on `main`. | 2026-11-04, by the maintainer, after dispatch |
