# The review's edits to H's brief draft and its screen population, every replacement asserted
# (exactly one occurrence before, none of the old text after). Usage:
#   python3 -I apply_fixes.py <orig-dir> <edited-dir>
# Written with decision D1 (A) (the second import, ChoiceWords) and D2 (A) (the review's chain
# probe staged as an input) assumed.
import sys, os

src, dst = sys.argv[1], sys.argv[2]
D = 'h-fill-hierarchy.DRAFT.md'
P = 'screen-population.txt'
s = open(os.path.join(src, D), encoding='utf-8').read()
count = 0


def rep(old, new, tag):
    global s, count
    n = s.count(old)
    assert n == 1, (tag, n, old[:80])
    s = s.replace(old, new)
    assert s.count(old) == 0 or old in new, (tag, 'old text survives')
    count += 1


# F11: the comment's placeholder list
rep('''the screen base; the lint base). Then a review sub-agent, then issue. Remove this comment at
issue. -->''',
'''the screen base; the lint base; the staged review probes). Then a review sub-agent, then issue.
Remove this comment at issue. -->''', 'comment')

# F5: the base after #170 (merged during the review)
rep('''- **Your base's Lean content is ⟨BASE⟩** (at drafting: the campaign after #169, `94296486`). Lines''',
'''- **Your base's Lean content is ⟨BASE⟩** (at review: the campaign after #170, `ba2441f7`; the
  drafting pre-ship ran after #169, `94296486`). Lines''', 'base')
rep('''**The base
  sorry-warning set has 22 entries in 11 modules**. Yours is `NTimeHierarchy`'s one.''',
'''**The base
  sorry-warning set has ⟨21 entries in 10 modules⟩** (after #170). Yours is `NTimeHierarchy`'s
  one.''', 'sorry-set')
rep('''`ClassP/TimeConstructible`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives`); and
`CodeSimulator`'s `exists_uniformSimulator` (B5a).''',
'''`ClassP/TimeConstructible`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives`). `CodeSimulator`'s
`exists_uniformSimulator` is proved since #170.''', 'out-of-scope')

# F6: the addendum's version (banner and ancestor list)
rep('(cover brief ⟨…⟩; addendum v2.5, Part 3)', '(cover brief ⟨…⟩; addendum v2.6, Part 3)',
    'banner-v26')
rep('''  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.5**)''', '''  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**)''', 'ancestor-v26')

# F1/D1, F7, D2: the inputs
rep('''the overlay
    `NTimeHierarchyOverlay.lean.txt` (your file with region (a)'s import), the import probe, the
    route probe with its seal controls, the duplication probe and the screen population;''',
'''the overlay
    `NTimeHierarchyOverlay.lean.txt` (your file with region (a)'s two imports), the import probe,
    the route probe with its seal controls, the chain probe `HChainProbe.lean.txt` (the whole
    proof over the two contracts) with its seal controls, the duplication probes and the screen
    population;''', 'inputs')

# F1/D1: the overlay and its offset
rep('''- **Your first edit makes your file equal to the overlay**: one import,
  `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer`, after line 16 (region (a)). **Line
  numbers below are the base's; the overlay's are 1 more** (the target at 1723, overlay 1724).''',
'''- **Your first edit makes your file equal to the overlay**: two imports,
  `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer` and
  `import TCSlib.Complexity.TuringMachine.ChoiceWords`, after line 16 (region (a)). **Line numbers
  below are the base's; the overlay's are 2 more** (the target at 1723, overlay 1725).''',
    'overlay')

# F5: the in-flight list
rep('''- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT; at drafting: E-Q's fill
  (megafill D's partial, under review, and its continuation) in `NTimeDiagonalizer.lean`, which adds
  that file's imports and privates; it changes no statement you cite⟩. Cite nothing they add.''',
'''- **Merged since the drafting pre-ship, so in your base:** #170 (B5a's uniform simulator,
  `ba2441f7`): `CodeSimulator`, in your file's import closure, with `exists_uniformSimulator`
  proved and two new imports (already in the closure, but they reorder your order list); and
  `EXPCOM`, `Relativization` (in your order list through the `Diagonalization` facade only) and
  `Codes2Tape` (outside it). It changes no statement you cite.
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT; at review (2026-10-27),
  none of them touching your file or a statement you cite:
  - #171 (`Build/WordTests`): the new module enters your closure through `TMSAT`, which your file
    imports, and the re-points in `TMSAT`, `EXPCOM` and `ClassNP/Nondeterminism`;
  - E-Q's checkpoint-1 landing (after #171): `NTimeDiagonalizer`'s eight new imports (among them
    `Mathlib.Data.Nat.Log`, `Build/Contract/Catalog`, `Build/Contract/Seam`) and three `qy_`
    privates⟩. Cite nothing they add. If any of them merges before the issue commit, the order
    list, roots, base sorry set and screen base below are the ones re-measured there.''',
    'in-flight')

rep('''None in `NTimeHierarchy.lean`. E-Q runs on its own branch in `NTimeDiagonalizer.lean`; E-D follows
it there. Neither changes a statement you cite.''',
'''None in `NTimeHierarchy.lean`. In `NTimeDiagonalizer.lean`: E-Q's checkpoint-1 landing (a
maintainer PR) and its continuation (a separate fill); E-D follows there after E-Q. None changes a
statement you cite.''', 'parallel')

# F10: what the brief supersedes
rep('''**Your proof is the chain only**, over that
contract. Its inclusion half, its thresholds and its chain are the docstring's "the chain, for the
alleged decider" and "inclusion". Do not edit the docstring before (d): the maintainer rewrites
the sketch at integration.''',
'''**Your proof is the chain only**, over that
contract. Of the docstring, only the *inclusion* and the shape of "the chain, for the alleged
decider" survive: the middle equivalence (3.3), the top's flip (3.4) and the bottom's transfer.
Its arithmetic is superseded too (the constant `A*`, the core's prefix clause, the
`|bits (g n)|` term, `BF`'s cost against `K · (g n + 1)`): the thresholds below bind. Do not edit
the docstring before (d): the maintainer rewrites the sketch at integration.''', 'supersede')

# F15: the walk at the base
rep('''A complete delivery has no
admission of its own: the target's axiom walk reaches `sorryAx` only through those two.''',
'''A complete delivery has no
admission of its own: the target's axiom walk reaches `sorryAx` only through those two (at your
base `exists_diagonalizer` is a bare `sorry`, so `exists_queryTM` is not reached yet).''', 'walk')

# F1/D1, D2: read first
rep('''  `acceptsWithin_iff` and `AcceptsWithin.mono`, `NDTM.HaltsWithin`, `NDTM.runWith_of_halt`;
- `ntime_hierarchy_of_pos`, right after your target (it consumes it unchanged).''',
'''  `acceptsWithin_iff` and `AcceptsWithin.mono`, `NDTM.HaltsWithin` with `haltsWithin_iff`,
  `NDTM.runWith_append`, `NDTM.runWith_of_halt`, and the shared branch truncation
  `Turing.run_take_of_halted` (`TuringMachine/ChoiceWords`);
- `ntime_hierarchy_of_pos`, right after your target (it consumes it unchanged);
- the chain probe `HChainProbe.lean.txt`: the review's proof of the target's statement over the two
  contracts (`nh_target`), sealed, with `sorryAx` only through them.''', 'read-first')

# F1/D1, F7, D2: the pre-ship check
rep('''- **The overlay** elaborates with exactly your file's one sorry warning (overlay 1724). The
  import creates no cycle (`NTimeDiagonalizer`'s closure does not contain your file).
- **The import probe** (`HImportProbe.lean.txt`, **48 checks of 48 names**): 0 errors.''',
'''- **The overlay** elaborates with exactly your file's one sorry warning (overlay 1725). Neither
  import creates a cycle (`NTimeDiagonalizer`'s closure does not contain your file; `ChoiceWords`
  imports only Mathlib, three roots already among your 33).
- **The import probe** (`HImportProbe.lean.txt`, **⟨70⟩ checks of ⟨70⟩ names**, the two imports):
  0 errors.''', 'preship-overlay')
rep('''  (the three thresholds) and `nh_stage` (a late stage of a code), each within the standard three.
  They may be copied into your home as `nh_` privates.''',
'''  (the three thresholds) and `nh_stage` (a late stage of a code), each within the standard three.
  They may be copied into your home as `nh_` privates.
- **The chain probe** (`HChainProbe.lean.txt`, sealed over 12: the 4 above, `NDTM.runWith`,
  `NDTM.initCfg`, `NTimeDiag.ladder`, `budget`, `stage`, `stageCode`, `TimeConstructible`,
  `CodeNDTM.toFinNDTM`): the truncation `nh_accepts_of_halts`, its decider corollary
  `nh_mem_of_accepts`, and `nh_target`, the target's statement proved over the two contracts. Its
  axiom walk: `sorryAx` directly in exactly `exists_diagonalizer` and
  `exists_codeNDTM_accepts_linear`. In the home (both imports, the privates at (b), the body at
  (c)) the file elaborates with no diagnostic. You may copy all of it as `nh_` privates and the
  body; the checks, seals, screens and the report are still yours.''', 'preship-chain')
rep('''- **The seal controls** (`HSealControl.lean.txt`): every one closes unsealed and fails sealed.
- **The duplication probe** (`HDupProbe.lean.txt`): the chain, the absorption, the inclusion and the
  top threshold posed to `exact?`: 4 of 4 "could not close".''',
'''- **The seal controls** (`HSealControl.lean.txt`, 4; `HChainSealControl.lean.txt`, 8 more): every
  one closes unsealed and fails sealed.
- **The duplication probes:** `HDupProbe.lean.txt` poses the chain, the absorption, the inclusion
  and the top threshold to `exact?`: 4 of 4 "could not close"; `HChainDupProbe.lean.txt` the
  truncation, its corollary, the bottom and middle thresholds and the late stage: 5 of 5.''',
    'preship-seal-dup')

# F1/D1: region (a)
rep('''- **(a) the import**, as your first edit: exactly
  `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer`, after line 16. No other import.''',
'''- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer` and
  `import TCSlib.Complexity.TuringMachine.ChoiceWords`, after line 16. No other import.''',
    'region-a')

# F1, F13: hosts
rep('''- **The diagonalizer:** cite `exists_diagonalizer` with `c` from
  `Turing.exists_effectiveNDMachineCode` and `hBF := Turing.exists_ndAcceptsWithin_decider c`.''',
'''- **The diagonalizer:** cite `exists_diagonalizer` with `c` from
  `Turing.exists_effectiveNDMachineCode` (a `Nonempty`: `obtain ⟨c⟩`) and
  `hBF := Turing.exists_ndAcceptsWithin_decider c`.''', 'hosts-diag')
rep('''- **The normal form:** cite `exists_codeNDTM_accepts_linear`; the code `α` of its `M'` by the
  scheme's `decode_encode`.
- **Classes:** `mem_NTIME_iff`, `decidesInTime_iff`, `acceptLang_mem_NTIME`, `NTIME.mono`.
- **Leaves you may write:** the inclusion's finite absorption; the thresholds' arithmetic; the
  chain's induction; the two transfers (the middle's at `f (n + 1)`, the bottom's at `f a`). A
  further leaf is an escalation.''',
'''- **The normal form:** cite `exists_codeNDTM_accepts_linear`; the code `α = c.encode M'` of its
  `M'` by the scheme's `decode_encode` (`c.toNDMachineCode.decode_encode M'`).
- **Classes:** `mem_NTIME_iff`, `decidesInTime_iff`, `acceptsWithin_iff`, `haltsWithin_iff`,
  `AcceptsWithin.mono`, `acceptLang_mem_NTIME`, `NTIME.mono`; the strictness by
  `Set.ssubset_iff_of_subset`.
- **The truncation:** `Turing.run_take_of_halted` (`ChoiceWords`, the shared form), with the
  absorption `NDTM.runWith_append` and `NDTM.runWith_of_halt`.
- **Leaves you may write:** the inclusion's finite absorption and constant fold; the thresholds'
  arithmetic; the chain's induction; the truncation of an acceptance at `N`'s all-branch budget
  through `run_take_of_halted` (the chain probe's `nh_accepts_of_halts`, with `nh_mem_of_accepts`);
  the two transfers (the middle's at `f (n + 1)`, the bottom's at `f a`). A further leaf is an
  escalation.''', 'hosts-leaves')

# F16, F17: the thresholds
rep('''   - for every `n` with `ℓᵢ < n`: `C · (C₁ · (c₀ · f (n + 1) + 1) + 1) ≤ g n` (`hfg` at a constant
     `A` with `A · (f (n + 1) + 1) ≥ C · (C₁ · (c₀ · f (n + 1) + 1) + 1)`, and `n > ℓᵢ ≥ i + 2`);
   - `C · 2^{C · (T* + 1)} ≤ 2^{T*²}`, that is the top's hypothesis at `n = ℓᵢ₊₁`
     (`ladder_succ`);''',
'''   - for every `n` with `ℓᵢ < n`: `C · (C₁ · (c₀ · f (n + 1) + 1) + 1) ≤ g n` (`hfg` at a constant
     `A` with `A · (f (n + 1) + 1) ≥ C · (C₁ · (c₀ · f (n + 1) + 1) + 1)`, from some `N₁` on; and
     `n > ℓᵢ ≥ N₁`, `nh_stage`);
   - `C · 2^{C · (T* + 1)} ≤ 2^{T*²}`, that is the top's hypothesis at `n = ℓᵢ₊₁`
     (`ladder_succ`), from some `T₀` on; `T* ≥ ℓᵢ + 2` (`budget_eq`), so `ℓᵢ ≥ T₀` suffices;''',
    'thresholds')

# F1: the middle's forward step, the bottom
rep('''form's converse gives an accepting `N`-branch; `N`'s decision, with truncation to its
     all-branch budget (`NDTM.runWith_of_halt`, as in `NTIME.mono`'s proof), gives `1^{n+1} ∈ L`.''',
'''form's converse gives an accepting `N`-branch; `N`'s decision, with truncation to its
     all-branch budget (`nh_accepts_of_halts`, through `run_take_of_halted`), gives
     `1^{n+1} ∈ L`.''', 'middle-forward')
rep('''The bottom's transfer (the third
   threshold, `AcceptsWithin.mono`, the normal form's converse and `N`'s decision) gives''',
'''The bottom's transfer (the third
   threshold, `AcceptsWithin.mono`, the normal form's converse, the truncation and `N`'s
   decision) gives''', 'bottom')

# F13, F18: step 5 and the edge cases
rep('''the strict inclusion (`Set.ssubset_iff_subset_ne` or the definition of `⊂`).''',
'''the strict inclusion (`Set.ssubset_iff_of_subset`: the inclusion, then `L` as the witness).''',
    'step5')
rep('''`n < 3` and the lengths at or below the seed `ℓ₀ = 2` (the stages start above it);
   `C = 0` or `C₁ = 0` (take `max 1`); `N₀ = 0`.''',
'''`n < 3` and the lengths at or below the seed `ℓ₀ = 2` (the stages start above it);
   `C = 0` or `C₁ = 0` (no `max` is needed: every threshold holds at `0`); `N₀ = 0`.''', 'edges')

# F9: gate guidance, the addends
rep('''- **The P3.3 gate** (`campaign/gates/ch3-p33/`): the target's statement and the two declared addends
  of `hfg` (`f n` for the inclusion, `n + 1` for the middle's `1^{n+1}`).''',
'''- **The P3.3 gate** (`campaign/gates/ch3-p33/`): the target's statement and the declared addends of
  `hfg`: `f n` for the inclusion, `f (n + 1)` and the constant `1` for the middle's threshold. The
  `n` addend is unused by this route (it covered the old construction's startup costs, now inside
  `K`).''', 'gate-addends')

# F7: cited infrastructure
rep('''All in `HImportProbe.lean.txt` (48 names): the target and its neighbour `ntime_hierarchy_of_pos`;''',
'''All in `HImportProbe.lean.txt` (⟨70⟩ names): the target and its neighbour `ntime_hierarchy_of_pos`;''',
    'cited-count')
rep('''monotonicity; `runWith_of_halt`, `runWith_append`; and the core and Mathlib facts the route probe
uses.''',
'''monotonicity; `runWith_of_halt`, `runWith_append`, `run_take_of_halted`; and the core and Mathlib
facts the route and chain probes use.''', 'cited-list')

# F1/D1: ground rules 6, 7
rep('''6. **Imports.** Exactly the one of region (a).
7. **One proof per shared argument.** Never re-walk `NTIME.mono`'s truncation or
   `ntime_hierarchy_of_pos`'s rescaling; cite them or the lemmas they use.''',
'''6. **Imports.** Exactly the two of region (a).
7. **One proof per shared argument.** The truncation goes through `run_take_of_halted` (one
   private, `nh_accepts_of_halts`); never re-walk `NTIME.mono`'s `take`/`drop` argument inline.
   The constant fold of `nh_inclusion` (as in `ntime_hierarchy_of_pos`'s first step) has no
   published form: write it once, and disclose its in-file pair.''', 'rules-6-7')

# F7: rule 10's list and seal start
rep('''    `stageCode` through their laws. Core and Mathlib definitions may reduce in `rfl`, `decide` or
    `show`, but are never passed to `simp`, `rw` or `unfold`. **Self-check by a seal test with
    controls** (each sealed definition: a goal closing by `rfl` unsealed and failing sealed),
    starting from the pre-ship's list, and an inspection table of your `rw`/`simp` arguments.''',
'''    `stageCode` through their laws, `NDTM.runWith` through `runWith_append` and `runWith_of_halt`,
    `CodeNDTM.toFinNDTM` not at all. Core and Mathlib definitions may reduce in `rfl`, `decide` or
    `show`, but are never passed to `simp`, `rw` or `unfold`. **Self-check by a seal test with
    controls** (each sealed definition: a goal closing by `rfl` unsealed and failing sealed),
    starting from the chain probe's 12, and an inspection table of your `rw`/`simp` arguments.''',
    'rule-10')

# F3: duplication governance
rep('''- **The population** (`campaign/fills/h/inputs/h-fill-hierarchy/screen-population.txt`, 11 files):
  your file; `NTimeDiagonalizer`, `ClassNP/NTIME`, `ClassNP/NDNormalForm`, `NDCodes`,
  `Nondeterministic`; and the hazards `TimeHierarchy/Diagonal` (`time_hierarchy`'s absorption and
  chain), `SpaceComplexity/Hierarchy` (the space hierarchy's), `ClassP/DTIME`,
  `TimeHierarchy/Separation`.
- **The base** is `campaign/fills/h/logs/h-fill-hierarchy-screen-base.txt`: 102 declarations, 6
  pairs (MEASURED at your base; seconds). Your file has no pair.''',
'''- **The population** (`campaign/fills/h/inputs/h-fill-hierarchy/screen-population.txt`, 14 files):
  your file; `NTimeDiagonalizer`, `ClassNP/NTIME`, `ClassNP/NDNormalForm`, `NDCodes`,
  `Nondeterministic`, `ClassP/TimeConstructible`, `ChoiceWords`; and the hazards
  `TimeHierarchy/Diagonal` (`time_hierarchy`'s absorption and chain), `SpaceComplexity/Hierarchy`
  (the space hierarchy's), `ClassP/DTIME`, `TimeHierarchy/Separation`, `ClassNP/ExhaustiveReplay`
  and `ClassNP/Nondeterminism` (the truncation's two private copies).
- **The base** is `campaign/fills/h/logs/h-fill-hierarchy-screen-base.txt`: ⟨…⟩ declarations, ⟨…⟩
  pairs (MEASURED at your base on the 14 files; seconds). ⟨Your file has no pair.⟩''',
    'population')
rep('''- **No new cross-file pair** with an owned-file declaration on one side. **Known hazards:**
  `time_hierarchy`'s finite absorption (cite a published form if the pre-ship finds one);
  `NTIME.mono`'s truncation (cite).''',
'''- **No new cross-file pair** with an owned-file declaration on one side. **Known hazards:**
  `time_hierarchy`'s finite absorption (inline there, no published form: the pre-ship and the
  review found none); the truncation, of which `ClassNP/ExhaustiveReplay`'s
  `xr_accepts_iff_of_halts` and `ClassNP/Nondeterminism`'s `acceptsWithin_iff_of_halts` are private
  copies (write yours through `run_take_of_halted`, and justify any pair with them);
  `ntime_hierarchy_of_pos`'s constant fold (in-file).''', 'hazards')

# F1/D1, F5: environment (order list unchanged by ChoiceWords; the lint's size WARN)
rep('''- **Re-bootstrap** from `campaign/fills/h/orders/h-fill-hierarchy.txt` (**81 modules**, on the
  overlay) after your first edit, logging each module's time and maximum memory.''',
'''- **Re-bootstrap** from `campaign/fills/h/orders/h-fill-hierarchy.txt` (**⟨81⟩ modules**, on the
  overlay, in the order re-sorted at issue: since #170 `CodeSimulator` follows
  `Build/InterpreterStartup`; `ChoiceWords` is already among them) after your first edit, logging
  each module's time and maximum memory.''', 'bootstrap')
rep('''- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: 0 FAIL, 2 WARN over 5 files).''',
'''- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: 0 FAIL, 2 WARN over 5 files). The owned file's size WARN (over 1,000 lines) is expected
  and stays: file size alone is not a finding.''', 'lint')

# F15: the walk's method
rep('''- **Axiom prints** for the target and every new private: within the standard three plus
  `sorryAx` only through the two named contracts; show the walk.''',
'''- **Axiom prints** for the target and every new private: within the standard three plus
  `sorryAx` only through the two named contracts; show the walk (the chain probe's `rvSorryWalk`
  lists every reachable constant whose own type or value mentions `sorryAx`: exactly the two).''',
    'axioms')

# REPORT checklist
rep('''- [ ] Every new declaration with its role; the thresholds' constants; a proposed
      `**Implementation.**` paragraph for the target's docstring (public-facing).''',
'''- [ ] Every new declaration with its role; the thresholds' constants (`N₁`, `T₀`, the stage
      bound); what you copied from the route and chain probes and what you changed; a proposed
      `**Implementation.**` paragraph for the target's docstring (public-facing).''', 'report')

# F1, F12, F14: pitfalls
rep('''- **`N`'s acceptance at an unbounded time** (the normal form's converse) must be truncated to its
  all-branch budget before `N`'s decision applies: `NDTM.runWith_of_halt` (as `NTIME.mono`'s proof
  does).''',
'''- **`N`'s acceptance at an unbounded time** (the normal form's converse) must be truncated to its
  all-branch budget before `N`'s decision applies, in the middle's forward step and in the
  bottom's transfer: `nh_accepts_of_halts`, through `run_take_of_halted` (its run and halting
  predicate as `fun w => N.tm.runWith w (N.tm.initCfg x)` and `fun c => c.state = none`).
- **Membership in `L`** is `Language`'s own `∈`, not `Set`'s: `simp only [Set.mem_setOf_eq]`
  makes no progress on it. Read it with `show` (as `acceptLang_mem_NTIME` does, by `Iff.rfl`), then
  `List.length_replicate`.
- **The decoded code:** `rw [c.toNDMachineCode.decode_encode M'] at hC` turns the contract's
  `(c.decode α).toFinNDTM` into `M'.toFinNDTM` once `C` is obtained at `α = c.encode M'`.''',
    'pitfall-trunc')
rep('''- `omega` with products and powers as atoms (`ring` first); the exponential threshold through
  `Nat.lt_two_pow` and `Nat.pow_le_pow_right`.''',
'''- `omega` with products and powers as atoms (`ring` first); the exponential threshold through
  `Nat.lt_two_pow_self` (`Nat.lt_two_pow` does not exist at this pin) and `Nat.pow_le_pow_right`.''',
    'pitfall-pow')

os.makedirs(dst, exist_ok=True)
open(os.path.join(dst, D), 'w', encoding='utf-8').write(s)

# F3: the population
p = open(os.path.join(src, P), encoding='utf-8').read()
old = 'TCSlib/Complexity/TuringMachine/Nondeterministic.lean\n'
assert p.count(old) == 1
p = p.replace(old, old + 'TCSlib/Complexity/TuringMachine/ChoiceWords.lean\n')
old = 'TCSlib/Complexity/TimeHierarchy/Separation.lean\n'
assert p.count(old) == 1 and p.endswith(old)
p = p + 'TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean\nTCSlib/Complexity/ClassNP/Nondeterminism.lean\n'
assert sum(1 for l in p.splitlines() if l.startswith('TCSlib/')) == 14
open(os.path.join(dst, P), 'w', encoding='utf-8').write(p)
count += 1
print('replacements:', count)
