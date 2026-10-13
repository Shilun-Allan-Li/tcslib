# CH34-D4: the three factorings (maintainer PR, 2026-10-12)

User ruling on `backlog.md` §1 CH34-D4: **factor before closing** the B5b gate. One maintainer
commit, `6c7e35bd`, drafted by a maintainer sub-agent in its own worktree and verified by the
maintainer.

| New public (namespace `Turing`) | Home | Effect |
|---|---|---|
| `bits_two_pow_mul` (`(2^j·m).bits = 0^j ++ m.bits`, `0 < m`), `bits_two_pow_eq_replicate` | `TuringMachine/Encoding` | ConfigGraph's `s1b_radius_bits` and EXPCOM's `expcom_bits_two_pow` deleted |
| `incFixed_replicate_true_append` | `Build/Convention` | EXPCOM's `expcom_inc_prefix` deleted; Catalog's `catalog_increment_value` keeps its statement, now derived from it |
| `incFixed_eq_none_iff_replicate` | `Build/Convention` | EXPCOM's `expcom_all_true` keeps its statement, now derived from it |

- **Homes.** `Build/Convention` cannot see `Nat.bits` without a new import. `Encoding` already
  imports `Mathlib.Data.Nat.Bits` and is upstream of every consumer, and CH34-D4 named both files.
  The prefix law, not `catalog_increment_value` made public, is the general form, and it sits
  where `incFixed` is defined.
- **Names.** `Separation` and the Meyer files `open Turing`, so the new names avoid their
  `bits_two_pow` and `incFixed_eq_none_iff`; neither file changes.

## Verification

- **Freeze** (`audits/logs/ch34-d4-freeze.log`):
  - no statement or import changed;
  - four publics added and three privates deleted;
  - the bodies changed are the two kept wrappers and the call sites (`expcom_front_triple`,
    `expcom_ok_iff`, `s1b_normalize_radius`);
  - the module headers of `Convention` and `Encoding` are updated (comment-only).
- **Elaboration before the replay.**
  - `Encoding` and `Convention`: in place, 0 errors.
  - `EXPCOM`, `ConfigGraph` and `Catalog`: scratch copies with the four lemmas inlined give
    0 errors and unchanged sorry warnings. Each copy differs from its edited file only by the
    inlined block.
- **Replay** (user-run; `audits/logs/ch34-d4-replay.log`, at `6c7e35bd`): the downstream closure
  of the five changed modules, 167 modules, **0 errors**. It includes the colleague-owned Meyer
  files and `Separation`. The sorry warnings are exactly the open rows: `EXPCOM`, `Catalog`,
  `Separation` and the Meyer files have none.
- **Axioms** (`audits/logs/ch34-d4-axioms.log`; probe `audits/evidence/ch34-d4/AxD4.lean.txt`): 171
  publics of `Encoding`, `Convention`, `Catalog`, `EXPCOM`, `ConfigGraph`, `Relativization` and
  `Codes2Tape`.
  - No non-standard axiom. The four new lemmas use at most `[propext, Classical.choice, Quot.sound]`.
  - Every admission walk is unchanged: the `EXPCOM` cluster and Baker–Gill–Solovay rest on the two
    §12.11 rows, and S1b's corollaries on `NSPACE_subset_exp_dtime`.
  - The private censuses find no `sorryAx`: EXPCOM 39 constants (was 41), ConfigGraph 56 (57),
    Catalog 1,555 (1,559).
- **Duplication** (`audits/logs/ch34-d4-screen-{before,after}.txt`; 25 files: B5b's population,
  the five touched files and two Meyer files):
  - 1,448 declarations and 1,422 pairs before; 1,447 and 1,422 after.
  - **Gone:** EXPCOM's `expcom_bits_two_pow` against Separation's `bits_two_pow` (94% / 84%), the
    pair CH34-D4 was opened for.
  - **New, disclosed:** `Convention.incFixed_eq_none_iff_replicate` against `MeyerTableau`'s public
    `incFixed_eq_none_iff`, 93/93 characters (100%). The colleague's theorem is the original. The
    new public copy is deliberate, because the criterion's home is where `incFixed` is defined, and
    `EXPCOM` cannot import `CircuitComplexity`. It retires when `MeyerTableau` cites
    `Convention`'s criterion, in the user's dedup window (backlog F6-1(j)). It needs the user's
    acknowledgement (`policy.md`, **Duplication**).
- The colleague-owned files `TimeHierarchy/Separation.lean` and `CircuitComplexity/*` are untouched.
