# Gate 96's copy-text screen (v3)

- **Base:** the campaign at `7a14e855` (Lean identical to the PR's base `4ef99963`), over the 17 files
  of `superseded-6134e5dd/population.txt`: `screen-base.txt`, 321 declarations, 64 pairs.
- **Head:** the PR head `89f4ebbc`, over `population.txt`: the same 17 files and the new
  `SavitchARM/Window.lean` (absent at base). `screen-head.txt`: 327 declarations, 65 pairs.
- **New at head** (`pairdiff.txt`, `pairdiff.py <head> <base>`): one pair,
  `Window.lean::NoEdge` reproduces `Recursion.lean::Rel` (67/79, 85%). The shared text is the
  codec's query layout `pairEncode x (pairEncode (Nat.bits u) … (Nat.bits s))`, which every
  decider question spells (23 files); `NoEdge` restates none of `Rel`'s meaning.
  **Disposition: idiom.**
- `superseded-6134e5dd/`: the screen at the eight-commit head before the window module (17 files,
  323 declarations, 64 pairs, no new pair); `round1-12files/`: the five-commit head.
- `status.txt`: each run's exit status, commit and time.
