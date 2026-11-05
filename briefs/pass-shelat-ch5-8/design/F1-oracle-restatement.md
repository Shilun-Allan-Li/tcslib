# F-1: oracle adversaries restated at the root (design)

**Ruling (user, 2026-11-05):** one notion of oracle computation. The concrete layer's `QueryTree`
becomes the one-oracle `Games.OracleComp`, and PRF security is stated with the framework's
adversaries. Bridges B1 and B3 become the proofs that the meaning is unchanged. The work starts
after gate 02 closes (closed; #185 merged) and finishes before gate pack 03d is dispatched.

## The mechanism (probed in Lean, 2026-11-05)

A scratch probe (`design/probes/F1-QueryTreeAbbrev.lean.txt`, 0 errors against `Games/OracleComp` at `cdf78da1acc2f5814147b358dec9bf5325999d52`) checks
the following against `Games/OracleComp` as merged:

```lean
abbrev singleSpec (I O : Type) : OracleSpec Unit := ⟨fun _ => I, fun _ => O⟩
abbrev QueryTree (I O α : Type) : Type := OracleComp (singleSpec I O) α
@[match_pattern] abbrev QueryTree.ret (a : α) : QueryTree I O α := OracleComp.pure a
@[match_pattern] abbrev QueryTree.query (x : I) (k : O → QueryTree I O α) : QueryTree I O α :=
  OracleComp.query () x k
@[elab_as_elim] def QueryTree.induct {motive : QueryTree I O α → Sort _}
    (ret : ∀ a, motive (ret a)) (query : ∀ x k, (∀ o, motive (k o)) → motive (query x k)) :
    ∀ t, motive t
```

It shows four things:
- The old definitions by pattern matching on `ret`/`query` compile unchanged, including
  `BoundedBy`'s nested patterns and structural recursion.
- The old proofs need only `induction t using QueryTree.induct` in place of `induction t`.
- The old statements of `eval_simulate` and `BoundedBy.mono` compile unchanged.
- `match` on the old constructor names works.

## Changes, in dependency order

1. **`Games/OracleComp.lean`:** gains `singleSpec`, moved from S2b's `Bridges/QueryTree.lean`.
2. **`Pseudorandom/Functions/OracleAdversary.lean`** (the concrete layer):
   - `QueryTree` becomes the abbreviation above, with its constructors and `QueryTree.induct`.
   - `eval`, `BoundedBy` and `simulate` keep their definitions. Their links to the framework are
     proved here: `eval` is `OracleComp.evalFn`; `BoundedBy q` is `CostBoundedBy (fun _ => 1) · q`;
     `simulate π ans` is `Games.simulate` with a stateless implementation. These were B1's results.
     B1's bijection `treeEquiv` becomes the identity and is removed.
   - **Universe change:** from `Type u` to `Type`, a disclosed deviation. Every use in ch. 2–8 is at
     `Type`.
3. **Users** (`LazySampling`, `SubHybrids`, `GGM`; `Asymptotic/PRF`, `GGMReduction`,
   `GGMReductionEval`, `MultiMessage`, `MultiMessageLemmas`):
   - add `using QueryTree.induct` at about 26 `induction` sites;
   - `Type*` becomes `Type` where a binder feeds `QueryTree`;
   - no statement changes beyond the universe.
4. **`toOracleAdversary` becomes an instance by definition.**
   - S2b's generic decoder `NUPPT.toComp` (`Games/Machines.lean`, B3) moves below `PRF.lean`: it
     imports only the machine model and `Games`.
   - `PRF.lean` imports it and defines `NUPPT.toOracleAdversary` as `toComp` with the one-oracle
     codec. B3's `toComp_singleCodec` becomes its defining equation.
   - `OracleEnsemble.Indist` keeps its text: its adversaries are framework computations by
     construction, and B2 reads its `acceptProb`/`oracleDist` probabilities as games.

## Verification and gates

- A fresh replay of everything downstream of `Games/OracleComp` and `OracleAdversary`, with
  `Checks.lean`'s headline axioms. Its baseline is the base-repair census: 291 printed, 237
  axiom-clean, 63 `sorry`s. The census must not change.
- **Gates:**
  - pack 03d gains `Pseudorandom/Functions/{OracleAdversary, LazySampling}` (the restated
    concrete files);
  - the S2b gate audits the bridges as rewritten here.

## Order of work

1. The dedup PR (DL-2 to DL-4) merges.
2. S2b merges the new base, which already contains S2a.
3. This restatement lands on the S2b branch, with B1/B3 rewritten as above, and its replay is
   run.
4. Then the S2b PR, then pack 03d.
