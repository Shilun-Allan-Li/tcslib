# Landing source-review supplement: visited-set monotonicity

The initial bounded delivery review missed one exact published-API re-point. Root identified
the six-line subset proof in original f6_loop715–720: unfold membership by the published iff,
choose the same source time, and extend its inequality from t₀ to t. The existing public
contract in SpaceComplexity/ConfigCount.lean281 is exactly:

```lean
MultiTapeTM.visitedByTapeHead_mono (tm : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) {t t' : ℕ} (h : t ≤ t') (i : Fin k) :
  tm.visitedByTapeHead c t i ⊆ tm.visitedByTapeHead c t' i
```

The literal mapping is `tm := M`, `c := M.initCfg x`, `t := t₀`, `t' := t`,
`h := ht₀`, `i := 0`. Root replaced the reconstruction by
`MultiTapeTM.visitedByTapeHead_mono M (M.initCfg x) ht₀ 0`, retaining the local subset header,
all public/private headers, imports and controller data. This is a standing WORKFLOW§3
mechanical reuse fix, with no new API/import/design or debt ruling.

The fix is ACTUAL at clean head f72a807e2376a2b986675c992745d6affc23b96f, source SHA256
8a44b4b35010ac116e34880269b80d1121d2fdd86166e62da75efeffc984c031. Root's fresh owner compile
under the managed4.25/-j4/nice10 wrapper passed exit0/errors0/sorry0,15.116s, with exact source/
olean receipts in ../native1/. The fresh independent metadata in this folder imports that
completed owner object. It does not claim a separate whole-source elaboration by this agent.

A source-only sweep of all eighteen new helpers and the target searched visitedByTapeHead,
its membership iff/image/range forms, subset/cardinality extension, runFrom_add/of_halt,
Nat.find and the usual time-bound witness closings. Only the one local hmono block reconstructs
this time-monotonicity family. Other hits consume host/embedding visited equalities and
frame facts, supplied ledger subsets, spaceUsedByTape_le_spaceUsed, or Mathlib Finset.card
monotonicity. No second same-kind reconstruction was identified. This is bounded enumeration
plus inspection, not a global absence/optimality claim or an extension of acknowledged debt.
The original delivery review remains frozen, with this missed item and correction explicit.

ConfigCount is now an actual canonical proof citation, while the earlier identity comparison
cites Inclusions. Thus root's final screen/source union is23 files: the issued21 plus those
two full files. The original21-file producer results remain separately attributed history.
