# The PAC layer (S3d layer 1, for `main`): evidence (2026-11-05)

- **The commit:** `44d27f39c233849a3a30a117bf15434610e485e9` on `cryptography/pass-shelat-ch5-8-pac`,
  one commit on `main` at `7d36bbc27dfabd4988ee1702bc342049a1f3e006`. It adds
  `InformationTheory/Samples.lean`, `LearningTheory/PAC/{Defs, Prediction}.lean` and the `PAC`
  facade, and exports them (6 files, 646 lines). Written by a worker; checked by the maintainer.
- **The checks** (`upstream.log`, `replay.log`): the upstream `InformationTheory` modules were built
  into a fresh olean tree. The five new or changed modules were then rechecked at the commit.
  **All pass, with 0 errors, 0 warnings and no `sorry`.** `replay-uncommitted.log` is the worker's
  run before committing.
- **The root facade** `TCSlib.lean` gains one import. It was not built, since its closure is the
  whole library. A search found no fully qualified name of the new files elsewhere on `main`.
  The matches by short name (`expect`, `label`, …) are in other namespaces.
- **Axioms** (`axioms.log`, run by the maintainer): all 38 theorems of the new files print within
  `propext`, `Classical.choice` and `Quot.sound`.
