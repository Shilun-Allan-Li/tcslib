# Gate 63 minor 4: the derived-name clash check, redone (maintainer, 2026-10-22)

The private rewind type `ss_RewindState` (`UniversalK`, `deriving DecidableEq, Fintype`) gives public instance names containing `Ss_RewindState`. Searched every `TCSlib/*.lean` file for `Ss_RewindState`, `instDecidableEqSs` and `instFintypeSs`:
- `origin/complexity/arora-barak-ch3-4` at `97299639f3a7b4e51f4f94127647cbb915158393`: 0 files
- `origin/lean/spaceused-api` at `3d0f80b5cbbd92344a02e81274281c203b1e8816`: 0 files

(#144, whose ref the review's `out/41` misnamed, merged at `0416ffea`, an ancestor of the campaign tip above.)
