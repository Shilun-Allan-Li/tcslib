# Gate 97: the inline-step sweep and the statement-shape grep (supplementary, before dispatch)

Run on 2026-11-05 by the cloud maintainer session, after gates 95 and 96 reported these two checks
missing from their evidence (gate 95 F5, gate 96 F6). The bundle is unchanged; this record is not
in it.

**Population:** the lines #197 adds to `.lean` files, `git diff -U0 683e2adf571e8b6a5c62280d4a3739ec89687546...0a1b64d59b707df679e66201496f2bced7197a98`
(416 added lines; `Build/ZoneStep`, `Build/ZoneRebalance`, `Build/Contract/Basic`, the facade).

**Inline-step sweep** (WORKFLOW §3's signs): `bufferTape_eq`/`bufferTape_nat`,
`List.getElem?_append|drop|eq_none`, `Nat.exists_eq_add_of_le`, `runFrom_add`,
`runFrom_of_halt`, `lt_trichotomy`, `Nat.find`, `Cfg.ext`, `∃ v, u = a + v` splits,
`unfold`, `simp [<Def>]`. **No hit** in proof text (one docstring line mentions "unfold").

**Reading the new proofs** (candidate enumeration plus inspection, not exhaustive):
- `exists_zoneTrackStepTM` composes the published rows with `Contract.branch`, `Contract.seq`
  and `Contract.zero`, and reads every endpoint through the published `simps` fields.
- `sum_two_pow_le_of_count` and `sum_cost_le_of_count` are new arithmetic. `geomSum` and an
  amortized sum occur nowhere else on the campaign or on any PR head (pr/158–pr/197); `Build/Zone`
  and `Build/ZoneRebalance` only say that the amortization belongs to the consumer.
- **One candidate:** the private `zs_rowPre_mapState` (the rows' precondition ignores the control
  state), read through the new `zoneRowPre_iff`. No published lemma states it.
  `ZoneRebalance` proves the same fact inline in `zoneRowPre`'s own home, by
  `simp only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` (lines
  1239, 2275, 2301 at the campaign tip, and the field forms at 831, 884). These are renaming
  conversions (RN-1's kind), so at most an accounting minor; a public `zoneRowPre_mapState` beside
  `zoneRowPre` would serve both files.

**Statement-shape grep** (the campaign and every PR head, pr/158–pr/197): `geomSum`,
`Contract.zero`/`Segment.zero`, `zoneTrackStep`/`trackStep`, `2 ^ idx`/amortization. Only #197
has the new shapes; `Segment.zero` is the existing anchor that `Contract.zero` packages.
