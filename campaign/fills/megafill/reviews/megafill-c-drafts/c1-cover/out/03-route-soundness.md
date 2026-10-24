# Check 3: the route's soundness, the seal, and feasibility

## The invariant

The target computes `α ↦ serializeK (c.decode α).tm.replayTM`; the scheme's canonizer computes
`α ↦ (c.decode α).serialize` (`canonizer_computes`, a structure field). So any `g` with
`g M.serialize = serializeK M.tm.replayTM` for every `M : CodeNDTM` gives
`g ∘ (fun α => (c.decode α).serialize) = target function` pointwise: the invariant is exactly what
the composition needs, and it is true for every `M` (not only decoded ones), since `rc_g` reads
only the serialization's own header. The brief states it as the binding contract `rc_g_serialize`
(line 195) with `rc_g_primrec` (line 196), and decomposes its proof (route item 3: the key list
`E`, the skip, the rounds, the header). It does not rest on the `#eval` evidence, which the brief
labels "by evaluation, not a proof" (lines 160–164).

## The layouts

- `serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)` (`serializeK_eq`), and
  `M.serialize = pairEncode (bits numStates) (unaryFin q₀ ++ (tableBitsK (fixChoice false).tr ++
  tableBitsK (fixChoice true).tr))` (`serialize_eq_tableBitsK`): same header, `n = numStates`,
  and `replayTM.q₀ = q₀` (`replayTM_q₀`). Keeping the header verbatim is right.
- `actionBitsK a = signBits a.inputTape ++ (finRange k).flatMap (optOptBoolBits w.1 ++ signBits
  w.2) ++ optBoolBits a.output ++ optStateBits a.state`: the first `2 + 4·2 = 10` bits of a
  two-tape record are the input move and the two work fields; the replay record (choice tape last,
  action `(none, 1)`) inserts `optOptBoolBits none ++ signBits 1 = [false, false, true, false]`
  there. `rc_widen r = r.take 10 ++ [f, f, t, f] ++ r.drop 10` matches.
- `workReadsK (k+1)` puts tape `0` outermost, so in `tableBitsK replay.tr` the choice read is
  innermost; `replayTM.tr q inp (Fin.snoc w c)` applies `N.tr (c.getD false) q inp w`: per key
  `(q, inp, w)` the replay table emits `widen rF ++ widen rF ++ widen rT`. Both source tables are
  over the same 27(n+1) keys in the same order, so the lockstep rounds are right.

## Re-runs (against `oleans-lslsk`, the base's Lean)

| Probe | Result | Output |
|---|---|---|
| `C1RCRouteProbe` (copied byte for byte) | 0 diagnostics; the seven axiom prints as recorded | `probe/C1RCRouteProbe.out` |
| `C1RCSealControl` | 15 errors, all `Type mismatch`, at lines 92–157 (the sealed section only); the unsealed section (11–82) closes | `probe/C1RCSealControl.out` |
| `C1RCDefsProbe` | `(true, 732, 1407)`, `(true, 1545, 2949)`, `([], [])` | `probe/C1RCDefsProbe.out` |

## Seal coverage

An elaborated-constant walk (a `#c1rc_walk` command appended to a copy of the route probe,
`probe/C1RCRouteProbeWalk.*`) lists the TCSlib definitions the route probe's declarations reach.
Apart from structure projections (`Action.*`, `NDTM.tr`, `CodeNDTM.tm`, the scheme's fields) they
are the 12 reached sealed definitions **and `optBoolBits`, `optStateBits`** (they ride inside
`actionBitsK_eq`'s right side), which the probe does not seal. Nothing closes through them, but the
drafting brief's §6.3 asks for every other-file definition touched, and the brief's rule-10 list
for the fill ("at least `codeSkipActionK`, `codeSkipRepeat`, `codeReadUnary`, `pairDecode`,
`codeBitsNat`") omits them too: finding F3.

## Feasibility: the review proves the target

`probe/C1RCReviewFeasibility.lean` (344 lines, 296 non-blank non-comment; definitions as the
brief recommends, renamed `rvc_`) proves, under a **21-definition seal** (the route probe's 14,
the brief's five, `optBoolBits`, `optStateBits`):

- `rvc_skip` (the skip, over any key list and record function), `rvc_round_step`, `rvc_rounds`
  (generalised over the accumulator and both suffixes), `rvc_workReads2_length`, `rvc_flat`,
  `rvc_keys_length` (`27 (n + 1)`), the route probe's record lemmas, `rvc_table_eq`;
- **`rvc_g_serialize : rvc_g M.serialize = serializeK M.tm.replayTM`** (the header by
  `pairDecode_pairEncode`, `unaryFin_eq`, `List.singleton_append`, `codeReadUnary_append`,
  `codeBitsNat_bits`, `pairEncode_eq`, `List.take_left`);
- `rvc_widen_primrec`, `rvc_body_primrec`, `rvc_round_primrec`, `rvc_table_primrec`,
  **`rvc_g_primrec : Primrec rvc_g`**, by exactly the decomposition the brief prescribes (nested
  `Primrec.option_casesOn` on `codePrimSkipActionK 2`; `codePrimRepeat` and `Primrec.nat_iterate`;
  `codePrimPair`, `codePrimUnary`, `codePrimPrefix`, `codePrimBitsNat`);
- **`rvc_target`**, the target's statement verbatim, by the brief's composition.

Output (`probe/C1RCReviewFeasibility.out`): no diagnostics; `rvc_target`, `rvc_g_serialize`,
`rvc_g_primrec`, `rvc_table_eq`, `rvc_widen_primrec` on `[propext, Classical.choice, Quot.sound]`.

- **Controls for the seven extra sealed definitions** (`probe/C1RCReviewSealControlX.*`): the
  seven `rfl` goals close unsealed (lines 11–21) and fail sealed (7 errors, lines 32–42, each at
  its own goal). The route probe's controls cover the other 14.
- **Walk** (`probe/C1RCReviewWalk.*`): the TCSlib definitions reached are 20, all sealed (the 21st,
  `MultiTapeTM.ComputesInTimeAndSpace`, is sealed but not reached); every cited TCSlib constant
  besides them is a theorem.
- **Inspection** (`probe/C1RCReviewFeasibility.inspection.tsv`, `scripts/rwargs.py`): every
  `rw`/`simp only`/`unfold` argument is a theorem, a local hypothesis or an `rvc_` definition;
  no core or Mathlib definition is passed to `rw`/`simp`/`unfold` (one `rw [Function.iterate_zero,
  id]` in the first draft was replaced by `Function.iterate_zero_apply`: a pitfall worth stating).
  Core definitions reduce only in `rfl` (`(workReadsK 2).length = 9` after the rewrites; the
  `Option.casesOn`/`match` closures of the `of_eq` steps), as the 2026-10-23 scope bullet allows.

Pitfalls met on the way (finding F5): the `codeReadUnary_append` form (`[false] ++ body` needs
`List.singleton_append`); `have h : Primrec fun a => (o a).casesOn …` fails to elaborate ("failed
to elaborate eliminator, expected type is not available"): let `have h := Primrec.option_casesOn
(α := …) (σ := …) …` infer it, then `of_eq` with `rintro` and `rcases` on the discriminants, closing
by `rfl`; the key list's length through `List.length_flatMap`, `List.map_const'`,
`List.sum_replicate_nat`.

**RESULT: PASS.** The route is sound, matches the published layouts, and is feasible with this
pin's Mathlib and `MathlibBridge` (no `Primrec.list_take` is needed). Seal coverage: two
definitions short (F3). Size: the review's proof is about 300 lines before house-style docstrings
and sketches, inside the report's 350–550 and well inside 3 hours.
