# #325 merge and snapshot adoption (2026-11-16)

Seyoon merged #325 (Ladner fill 7: target 6 `SAT_H_intermediate`) at `20394834d86a509ad5776c36dbbfccc33b023306`. This
completes Ladner's theorem [AB09, Theorem 3.3]: `Complexity.ladner : P ≠ NP → ∃ L ∈ NP, L ∉ P ∧ ¬NPComplete L` depends only
on `propext`, `Classical.choice` and `Quot.sound`, and `Diagonalization/Ladner.lean` has no admission. Outside `campaign/` the
merge equals the gate 141 replay's tree `c0d07c95`, so that replay's output becomes the campaign snapshot (`oleans-c2039`,
876 objects, each rehashed on disk against the replay's map). `oleans-cd811` is kept as the fallback. See `ADOPTION.json`.
