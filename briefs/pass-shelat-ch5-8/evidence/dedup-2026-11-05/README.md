# The ch. 2–4 dedup (DL-2, DL-3, DL-4): evidence (2026-11-05)

- **The commit:** `c7d5a6e22dfd48b603e57fc2def3b470ba170249` on
  `cryptography/pass-shelat-ch2-4-dedup`, branched from `1f54a549f4ec13e8a72ed7e9f3786de981c5853f`
  (the ch. 2–4 head after the `main` merge). It changes 14 files. The working tree that was
  replayed is exactly that commit: the replay ran on the uncommitted changes, which were then
  committed with nothing else in the tree.
  - **DL-3:** one `Turing.pairEncode_ne_nil`, in `Encoding.lean`;
  - **DL-2:** one XOR-of-encodings lemma (`zipWith_xor_ofFn_add`);
  - **DL-4:** the new `StatClose`/`EpsClose` bridge, `Asymptotic/SamplingFinDist.lean`.

  No headline statement changes.
- **The replay** (`replay.log`, `replay-order.txt`): the 410 modules downstream of the changed
  files, with their upstream, 756 modules. Each was checked alone with
  `scripts/lean_check_tree.sh`, into a fresh olean tree. **756 of 756 pass, with 0 errors.** A
  container restart interrupted the run after module 537; it resumed from module 538 (the log marks
  the resumption).
- **The rest of the ch. 2–4 closure** (`closure-extra.log`): 8 of the 170 closure modules lie
  outside the replay, because they are neither downstream of a changed file nor upstream of one.
  They are three Garg-layer leaves and five facades. **All 8 pass.** The first pass ran them in
  alphabetical order, so four of them came before a module they import and failed on its missing
  `.olean`; the log's second pass reruns those four in dependency order. So all 170 closure modules
  are confirmed at this commit.
- **The `sorry` census of the closure:** 80 warnings.
  - **63 inherited ch. 2–4 sorries,** as in the base-repair census (Candidates 57,
    ThreeColoring 3, Universal and UniversalPadding 1 each, NonUniform 1).
  - **17 in `main`'s machine layer,** upstream of ch. 2–4 since the `main` merge:
    `Build/Loop` 5, `Build/Primitives` 3, `Composition` 3, `Build/Wrappers` 2, `TimeConstructible`
    2, `Encoding` 1, `Simulation` 1. The `Encoding` one predates the dedup; the dedup's diff adds
    no `sorry`.
- **Headline axioms** (`checks-axioms.log`): `audits/pass-shelat/Checks.lean` prints 291 headline
  theorems. 237 depend only on `propext`, `Classical.choice` and `Quot.sound`; 54 depend on
  `sorryAx`. **Declaration by declaration, this is identical to the base-repair print** (before
  the `main` merge). So none of `main`'s 17 machine-layer sorries reaches a ch. 2–4 headline: the
  open question of the merge record is closed.
