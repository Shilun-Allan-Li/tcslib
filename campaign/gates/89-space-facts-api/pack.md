# External audit pack — four space facts out of `Machines/ARMWidth` (PR #181, an API gate)

**Why this PR.** The space hierarchy's fill (B6's H, `SpaceComplexity/Hierarchy.lean`) needs
`logSpace n ≤ n + 1` and `L ⊆ PSPACE`. Both were public in `Machines/ARMWidth`, outside
`Hierarchy`'s imports, and `Constructible` re-proved the first inline twice (the ledger's LS-1
family, accepted debt scheduled for the dedup window). **The user ruled (2026-11-04): the lemma
moves first, by an API PR** (not a fifth import of `ARMWidth` into `Hierarchy`, and not one more
LS-1 copy), **and with it the other general space facts in `ARMWidth`**: `LOGSPACE_subset_PSPACE`,
`SPACE_succ_pow_subset_PSPACE` and `logSpace_le_of_le_mul_two_pow` ("I'd rather have good code now
and not have to make an extra PR much later"). `ARMWidth` (Hydroxyi's) keeps its register-machine
wrappers; the edit there is mechanical, within the standing exception for mechanical deduplication
edits to the ARM files (FYI to the author).

**The PR:** #181 on `lean/logspace-move`, head `50adf098dc94d2d4fed3eb6c46c0263c502fd975`: the
commit `124ba88c` (`evidence/patches/`) and the campaign after #176 merged in (no other Lean
change). Against the campaign, #181 changes exactly four files.

## What changed (verify)

| Class | Change |
|---|---|
| **Moved** to `SpaceComplexity/Basic` (beside `logSpace_eq`) | `Complexity.logSpace_le_succ (n : ℕ) : logSpace n ≤ n + 1` (new proof: `Nat.log_le_self` and `logSpace_eq`); `Complexity.logSpace_le_of_le_mul_two_pow {v A s : ℕ} (h : v ≤ A * 2 ^ s) (hs : 1 ≤ s) : logSpace v ≤ (A + 1) * s` (proof verbatim; `lemma` became `theorem`) |
| **Moved** to `SpaceComplexity/SpaceClasses` (beside `space_poly_subset_PSPACE`) | `Complexity.LOGSPACE_subset_PSPACE : LOGSPACE ⊆ PSPACE` (proof now reads `LOGSPACE` through `LOGSPACE_eq`, `simp only [pow_one]`); `Complexity.SPACE_succ_pow_subset_PSPACE (k : ℕ) : SPACE (fun n => (n + 1) ^ k) ⊆ PSPACE` (proof verbatim) |
| **Removed** from `Machines/ARMWidth` | the four, their docstrings, the module docstring's entries, and the empty `namespace Complexity` block they leave |
| **Re-pointed** in `Constructible` | `spaceConstructible_linear`'s dominance conjunct (`Nat.succ_le_succ (Nat.log_le_self 2 n)`, by reduction of `logSpace`) and `spaceConstructible_poly`'s inline `logSpace n ≤ n + 1` now cite `logSpace_le_succ`; `spaceConstructible_poly`'s sketch says so |
| **Import** | `SpaceClasses` imports `ClassP/P` (for `succ_pow_le`): one module (over `ClassP/DTIME`, already in), no new Mathlib root, no `@[simp]` lemma in `ClassP/P`, and every one of `SpaceClasses`' 81 downstream modules already imports `ClassP/P`, so no other module's environment changes |

Freeze (`evidence/freeze/`): `Basic` 17 → 19 public, `SpaceClasses` 7 → 9, `ARMWidth` 9 → 5,
`Constructible` 5 → 5 public, 23 → 23 private, two authorized body changes; every other
declaration unchanged. The four statements are text-identical at their new homes
(`moved-statements.txt`). Non-private constants, compiler auxiliaries included (`evidence/census/`,
per gate 88 round 2's minor 2): `Basic` 18 → 27 (the two theorems, six `_proof_*` auxiliaries,
and `logSpace.eq_1`, now realized in `Basic`); `SpaceClasses` 7 → 9; `ARMWidth` 38 → 28;
`Constructible` 15 → 13 (`logSpace.eq_1` realized upstream now; one proof auxiliary gone with the
inline step).

## Brief for the auditor

1. **Homes.** Is each declaration now in the file that owns its subject (`logSpace` in `Basic`;
   `PSPACE` and the definitional inclusions in `SpaceClasses`), and does `ARMWidth` lose nothing it
   should keep? Is `ClassP/P` the right source of `succ_pow_le` for `SpaceClasses`, and is the claim
   that the import changes no other module's environment right?
2. **Statements and users.** The four statements are unchanged; every user already imports the new
   homes (`ARMWidth`, `ARMWidthExample`, `NARMProof`, `SavitchARM/Reach`, `SavitchARM/Correct`,
   `TQBFARM/Correct`, `Logspace/ISCountGenCorrect`). Confirm, and that no name now resolves
   differently anywhere.
3. **Rule 10** (maintainer API proofs, scope of 2026-10-23), `evidence/rule10/`:
   - `SpaceClassesSealed`: the two moved proofs with `SPACE`, `LOGSPACE`, `logSpace` sealed and the
     four `@[simp]` TCSlib definitions erased: 0 diagnostics.
   - `ConstructibleSealed`: gate 86's seal of the same block (12 definitions, `logSpace` among
     them) at the head: 0 diagnostics.
   - `ConstructibleLinearSealed` / `…Base`: `spaceConstructible_linear` with `logSpace` sealed: the
     head elaborates; the base fails at `Nat.succ_le_succ (Nat.log_le_self 2 n)` ("has type
     `(Nat.log 2 n).succ ≤ n.succ` but is expected to have type `logSpace n ≤ (fun n => n + 1) n`").
     The re-point removes a reduction of another file's definition.
   - Controls (`SealControl_*`): unsealed 18 of 19 pass (the recursive `transduce`'s delta goal
     fails; its equation control passes); sealed all 19 fail.
   - `Basic`'s two reach no other-file TCSlib definition (`logSpace` is `Basic`'s own).
   Is anything else unfolded or closed by reduction? `spaceConstructible_linear`'s other steps
   (an anonymous constructor on `Constructible`'s own `SpaceConstructible`, `simpa [M, t]`) are
   unchanged from the base; is it acceptable to leave them as inherited?
4. **Duplication.** The screen (`evidence/screen/`, 14 files: the four, the seven users, `ClassP/P`,
   `NSPACE`, `Savitch`, `Hierarchy`), base at `711f5444`, head at `50adf098`: 85 → 85 declarations
   screened, 20 → 20 pairs, 3,278 characters both times; no pair new and none gone (`pairdiff.txt`).
   The moved declarations reproduce nothing and are reproduced by nothing. Is that right? The ledger's LS-1 entry is retired by this PR.
5. **API copies** (`api-copy-search.txt`, every origin ref with its object id): of 117 refs, 99
   (`main` among them) declare the four in `ARMWidth`, 17 (without an `ARMWidth`) declare none, and only this
   PR's branch declares them at the new homes; no ref declares any elsewhere. Does a later merge of
   the campaign into `main` raise any clash?
6. **Lint** (`evidence/lint/`): `SpaceComplexity` 0 FAIL, 83 WARN over 110 files at base and head,
   the same warnings; the policy linter 0 findings on `Basic`, `ARMWidth`, `Constructible`, and on
   `SpaceClasses` one at both base and head: a docstring line of `coNL`'s ("theorem ([AB09, …")
   read as a declaration, the parser false positive already on the deferred cleanup's list.

## Repository-side attestations (verify or challenge)

- **Elaboration chain** (`evidence/elab-chain/`, method in `scripts-note.txt`): the four files and
  the seven users, compiled in dependency order into a copy-on-write clone of `oleans-lnpc3`: 0
  diagnostics each. The axioms of the four and of the two re-pointed theorems:
  `[propext, Classical.choice, Quot.sound]` (`rule10/MovedAx.*`).
- **Replay:** `replay-lsm1.sh` (`evidence/merged-tree/`), the four files' downstream closure, 137
  modules, fresh `.olean`s from `oleans-leqc3` (the campaign tip after #176), pinning the four
  blobs. **Passed** (user, 2026-11-04): 137 of 137 at `50adf098`, 0 failed; the static sorry check
  equal (40, all pre-existing: `TQBF` 21, the `RAMSimulation` files 14, `Hierarchy` 4, `Savitch` 1)
  (`replay-lsm1.log`, `replay-lsm1-static.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/89-space-facts-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `space-facts-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
