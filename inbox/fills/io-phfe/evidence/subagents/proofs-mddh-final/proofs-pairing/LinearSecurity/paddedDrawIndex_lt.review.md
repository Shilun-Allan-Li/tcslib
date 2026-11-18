# Padded partial-garbling draw index bound

Exact live original frozen header/opening prose/sketch preserved. One tactic block,
no new helper/import/runtime definition, admission, sampler, dimension premise, or
efficiency hypothesis. No Lean/lake/Git command or live source edit was run.
Root native validation remains pending.

Read ONLY paddedDrawIndex_eq, then split its existing Sum.elim branches.
- For inl i, (PG.tCoord ... i).isLt bounds the actual auxiliary coordinate;
  PG.auxCount_add_one and mCount_le_mBound place it inside the padded maximum.
  The remaining conclusion is linear natural arithmetic, handled by omega.
- For inr j, the exact offset is PG.mBound.eval kappa and j.isLt gives the
  direct Nat.add_lt_add_left conclusion. No dimension expression needs unfolding: the
  frozen target/reader already exposes mBound.eval kappa+nprime.eval kappa numerically.

Both Fin-zero cases are total: an impossible zero-dimension coordinate supplies its
own contradictory isLt proof; no positivity assumption is inserted. The supplied
raw PG count laws are used at the ORIGINAL f,kappa,p, not an independent padded family.

Rule 10: paddedDrawIndex is read through its published equation theorem. Only the
Sum.elim constructor readers and public Fin bounds/PG structure laws are used. No
foreign definition is supplied to simp/rw/unfold and no indexing/count lemma is rederived.

Static exact APIs read: LinearSecurity/Data.lean:286 paddedDrawIndex_eq; current
frozen Theorems.paddedDrawIndex_lt; PartialGarbling.Raw.tCoord, auxCount_add_one
and mCount_le_mBound; Fin.isLt; Sum.elim_inl/inr and Nat.add_lt_add_left. No exact
other padded-index bound was found in current Wee20 sources. No new helper probe is
needed for this existing target. No mathematical obstruction found.
