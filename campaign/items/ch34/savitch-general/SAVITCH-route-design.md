# The general `savitch`: the route, before any brief (design note, maintainer, 2026-10-27)

**What this is for.** `Complexity.savitch (S) (hS : SpaceConstructible S) : NSPACE S ⊆ SPACE (S·S)`
(`SpaceComplexity/Savitch.lean:257`) is a stub. It was moved to the program route and paused with
stage 2 on 2026-10-14. **The user revived it (2026-10-27).** `PSPACE_eq_NPSPACE` is already proved,
through Hydroxyi's register-machine Savitch (`SpaceComplexity/SavitchARM/*`, over the configuration
codec `SpaceComplexity/Codec/*`). This note asks how far that proof stretches to a general `S`.

## What the proved route has (read at the tip `ed320a4b`)

- **The bridge to `SPACE S` is general.** `Complexity.LogProg.arm_decides_SPACE`
  (`Machines/ARMWidth.lean:198`): an abstract register machine with logspace subroutines whose
  registers hold `O(S |x|)` binary digits decides its language in `SPACE S`, for any
  `S ≥ logSpace`, with no monotonicity or constructibility. At `S·S` it covers Savitch's stack of
  `O(S)` frames of `O(S)` bits.
- **The reduction to reachability is general.** `SavitchARM.mem_iff_reach` (`Reach.lean:213`): if
  `N` decides `L` in space `sp`, then for every radius `s ≥ sp |x|` and code width `w` with
  `codeK N · (s + logSpace |x| + 1) ≤ w` and `configBound ≤ 2 ^ w`, `x ∈ L` iff some initial code
  reaches some accepting code by midpoint reachability at level `w`. The width is linear in the
  radius, so `s = O(S)` gives `w = O(S)` and registers of `w · w = O(S²)` digits.
- **The search is generic in `s`, `w` and the oracle, but stated for one program.** `outerU_run`
  and `outerV_run` (`Search.lean:106, 186`) run the search from `outerSt s w u 0 M` for any `s ≤ w`
  and any oracle `orc`, but they are statements about the program `A E` (`Machine.lean:574`), whose
  acceptance test is decider `2`.
- **Only the setup is polynomial.** `setup_run` (`Setup.lean:135`) computes `s = (n + 2) ^ E` and
  `w = (n + 2) ^ (2E)` by counting loops; `savitch_halts` composes it with `outerU_run`.
  `NSPACE_poly_subset_PSPACE` picks `E` large for the decider's polynomial bound.

**So the one gap is the radius:** a machine whose subroutines are logspace deciders must reach some
`s ≥ c · S |x|` without computing `S`. Space constructibility (`Constructible.lean:61`) gives a
machine writing `(S |x|).bits` in space `c · S`, but that is not a logspace subroutine.

## The routes

**(A) Iterative deepening on the radius, in the register-machine layer.** For `s = 1, 2, …`: set
`w` from `s` and `|x|`; if no configuration code at radius `s` with a work head at the window's
edge is reachable from an initial code, answer the main search at this `s`; otherwise grow `s`. It
stops by `s ≤ c · S |x| + 1`, because every branch of the decider stays within its space bound and
heads move one cell per step, so registers stay `O(S)`, and the stack `O(S²)`. Constructibility is
then used only for `S ≥ logSpace`. What it needs:
1. **A boundary language** (codes at radius `s` with a head at `±s`) and its `LOGSPACE`
   membership, in the codec's terms, beside `initLang`, `acceptLang` and `stepLang`
   (`Codec/Deciders`).
2. **Window exactness:** a per-input form of `mem_iff_codeChain` (`Codec/Bridge.lean:140`) that
   replaces `sp |x| ≤ s` by "no reachable code touches the edge".
3. **A deepening machine** that runs the search twice per radius (against the boundary language,
   then against the accepting language). `outerU_run` is stated for `A E` with decider `2`, so this
   needs either Hydroxyi's machine generalized (the search as a block over any acceptance decider,
   its lemmas stated for any program containing it), or a copy of about 1–2k lines of his search,
   which would be a duplication finding.

ESTIMATE: 1.5–3k lines, about half of it in or beside Hydroxyi's layer.

**(B) Run the constructibility witness first.** A machine-level composition: run `S`'s witness to
write `(S |x|).bits` (space `c · S`), then run a Savitch register machine whose setup reads that
radius. This needs a new bridge (a register machine started from a register written by a
space-`S` transducer) beside `arm_decides_SPACE` in `Machines/ARMWidth` and `Compile`, and a new
setup in place of `setup_run`. No boundary test, but the bridge goes into the compile layer's
proofs. ESTIMATE: 1.5–3k lines, most of it in Hydroxyi's layer.

**(C) A machine-level Savitch on the construction library** (the original B3 plan: a frame-stack
machine on the §12 library). It is independent of the register-machine layer, and the largest.
ESTIMATE: 3–6k lines.

## Decisions (the user's)

1. **The route.** (A) is recommended: it keeps the proved search and the general bridge, needs no
   new compile-layer bridge, and its new mathematics (the edge language, window exactness) is
   small and textbook.
2. **Hydroxyi.** (A) and (B) both change or extend his `SavitchARM`/`Machines` layer: (A)
   generalizes his search's acceptance decider and the statement of `outerU_run`. Consult him
   before any edit (the standing rule for his files), with the design of the generalized search.
3. **The queue.** After NF's API PR (#174) and E-D's brief; it does not touch their files.
