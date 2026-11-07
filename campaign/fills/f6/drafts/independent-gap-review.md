# Independent F6 interface review

Source inspection only, 2026-11-07. No Lean elaboration, seal, source edit, screen, or Git
mutation was performed for this review. The main reviewer owns the conversion controls.
F6 remains dependent on #229 merging.

**Verdict:** the direct hosted-startup argument lacks a public live-exit cut, but that does
not force a stronger ruler-host API. A halt-then-return assembly uses the existing host and
returning embedding, with one elementary private halting leaf. It stays within the selected
ruler-hosted suffix construction. The separate `CodeTM.toFinTM` conversion does need a
published reader; the abbreviation exception does not cover it.

## What the direct interface supplies

`Build/InputDevice.lean:1226`, `Turing.exists_rulerHostTM`, quantifies existentially over
`Q`, its finite/decidable instances, `H`, `inj : S → Bool → Q`, and a positive `C`. For each
valid ruler presentation, source configuration `c`, tag `b`, and time `t`, it supplies a
`t'` with `t ≤ t' ≤ C * (ℓ + 1) * t`, the complete endpoint, tape/head/output frames, and
visited-set bounds. Its entire control-avoidance clause is exactly:

```lean
((∀ u < t, (M.runFrom c u).state ≠ none) →
  ∀ u < t', (H.runFrom d u).state ≠ none)
```

There is no injectivity assertion for `inj`, no intermediate control-state correspondence,
and no stop-sensitive `Lockstep` witness in that public conclusion. The private proof's
`Lockstep` for `{none}` cannot be read by a consumer.

In contrast, `UniversalK.lean:1436`, `exists_selfStartupTMK`, supplies a native startup `R`
and live `exit`, an exact endpoint at input cell `1`, and:

```lean
∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit
```

`Build/UniversalParts.lean:370`, `startupLoopTM_runFrom`, and its space theorem at line 405
require the corresponding live-exit exclusion for the machine actually used as the left
component. The native cut is not a hosted cut. `seamCompTM_runFrom_right`
(`Build/Seam.lean:229`) also takes the cut as a premise. `seamReleaseTM_firstReturn`
(`Build/Seam.lean:776`) takes the positive-interior source cut as a premise; its fresh entry
only handles time zero. Ordinary state relabelling and tape embeddings transport known
runs/cuts. They do not reveal the missing intermediate host controls.

`Lockstep.cut` (`Build/Contract/Basic.lean:1351`) would supply it from a suitable stop-aware
lockstep, whose `inner` field excludes the target stop set during each block. H5 exports
neither that field nor such a lockstep.

**Contract counterexample (mathematical, not elaborated).** Take a zero-work-tape source
with two live states `a ≠ e`; every transition is stationary and silent, with successor `e`.
Take a one-ruler-tape host with a single stationary live state `q`, and let every
`inj s b = q`. Choose `C = 1` and `t' = t`. Every H5 endpoint, frame, visited-set and
none-liveness clause holds, for arbitrary valid presentations and arbitrary source starts
(halted starts remain halted). From source state `a` at input cell `1`, time `1` first
reaches `e`, but the host is already at `inj e false` at time zero. Thus H5's general
contract does not imply the proposed live-image first-return cut. This is not a claim that
the actual private host implementation violates that cut.

## Existing-host assembly that avoids the missing cut

Use the native startup's published exit cut before applying H5:

1. Define an elementary private leaf, on the same bank, with one state and action
   `⟨0, fun _ => (none, 0), none, none⟩`. Its single transition halts, preserving input
   position, all work tapes/heads, and output. Prove its full one-step endpoint in its home.
2. Let `A := seamCompTM R exit haltLeaf ()`. The public left/right seam lemmas, the native
   startup endpoint/cut, and the leaf's one-step equation give the same data endpoint with
   state `none` at `T + 2`: one seam dispatch and one halting step. Source liveness through
   `T` follows from the public `MultiTapeTM.runFrom_state_ne_none_of_le`; the seam then
   gives liveness before this halt. The visited-set seam theorem bounds the added stationary
   steps by the startup's existing visited cells.
3. Apply H5 to `A`, not directly to `R`. Its endpoint is now halted, and its exported
   none-liveness clause gives the first host halt at `t'`. All data and ruler frames remain
   the H5 frames. Its time bound is applied to `T + 2`.
4. Apply `embedEmitRetTM_run` (`Build/Embed.lean:877`) to that host run, using the identity
   tape selection, empty output prefix, and the same start configuration. Its exact premises
   are `hc : c.state ≠ none`, `hlive : ∀ t < t', ...state ≠ none`, and
   `hhalt : ...state = none`. Its endpoint is the embedded final data with fresh live
   control `some (Sum.inr ())`, and its last conclusion is precisely the strict earlier
   exclusion of that control. `embedEmitRetTM_visitedByTapeHead` at line 959 transfers every
   visited set, so the returning adapter adds no tape or space cost.

This is an assembly argument, not a pre-shipped fill proof. The brief must still elaborate
its leaf endpoint, exact configuration reconstruction, finite instances, bank indexing,
initial-control adjustment, and uniform prefix bounds. It must account for both added
steps and use the returned fresh anchor as the later seam exit. No new public ruler-host
API or replacement private ruler host is required by this argument. No extra route ruling
is indicated by this inspection.

## `CodeTM.toFinTM` conversion

`Encoding.lean:117` declares an ordinary **`def`**:

```lean
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm
```

The only nearby published projection reader is `CodeTM.toFinTM_k` (line 124). A repository
search found no `toFinTM_tm`, `toFinTM_State`, or whole-bundle equation. The existing
`EffectiveMachineCode.toK_machine` and `toK_toFinTM` equations expose different projections
of `toK`; they do not themselves publish the raw-machine projection of either bundled
conversion.

Consequently, treating `(decode α).toFinTM.tm` as `(decode α).tm` by `rfl`, `change`, or a
type annotation still reads this other-file definition. `policy.md`'s reducible-abbreviation
exception and `TEMPLATE.md`'s seal exception apply to `abbrev`, not this `def`.

A minimal robust reader is the whole-bundle equation beside the definition in
`Encoding.lean`, with a mathematical docstring and no `simp` attribute:

```lean
theorem CodeTM.toFinTM_eq (M : CodeTM) :
    M.toFinTM =
      { k := 1, State := Fin (M.numStates + 1), tm := M.tm } := rfl
```

This exposes the dependent state/tape types and the machine together, so a consumer can
rewrite explicitly rather than rely on hidden conversion. Its exact declaration and
consumer use remain subject to the main reviewer's elaboration/seal and the maintainer's
normal approval of a new public API. It belongs in `Encoding.lean`, not `Hierarchy.lean` or
`UniversalParts.lean`, because proving it reads `CodeTM.toFinTM`.
