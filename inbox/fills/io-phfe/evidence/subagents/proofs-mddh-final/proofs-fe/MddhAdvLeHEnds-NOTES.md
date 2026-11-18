# mddhAdv_le local hEnds candidate

Status: isolated proof-only SCRATCH fragment, NOT natively checked. Root's serial full
freeze audit occupies the Lean slot; this child ran no Lean/lake/build/Git, live edit,
process operation, extra agent or native probe. Whole ladder typing remains root-owned.

Fragment: MddhAdvLeHEnds.proof.lean.inc (11 lines). Exactly one tactic block, by plus
four-space body. No placeholder/admission/new helper/algorithm or >100-column line.
All other MddhAdvLe.skeleton.lean.inc blocks remain unchanged.

Exact target is the existing hEnds:
  forall kappa,
    accept(hybrid kappa 0) = accept(G.mddhGame d ell D false kappa) AND
    accept(hybrid kappa (d.eval kappa)) = accept(G.mddhGame d ell D true kappa).
The source hybrid definition was reread exactly; it samples pp,M,S,U,D coins and encodes
response (fun a b => if b.val<i then (M*S)(a,b) else U(a,b)).

## Reused equation APIs

- Read the proof's OWN local hybrid let via dsimp only [hybrid]. No foreign definition
  is named for unfolding.
- accept_eq (:67 Games/Advantage.lean), G.mddhGame_eq and G.mddhSample_eq expose the
  actual game and its exact shared pp/M/S/U draws. Both theorem calls are explicitly
  instantiated at d/ell/D/Bool/kappa.
- prob_bind, expect_bind and expect_pure are the public semantic readers. They reassociate
  the game/sample bind sequence; foreign ProbComp.prob is never identified by defeq.
  No prob_eq_expect rewrite or broad expectation-of-a-constant matcher is used.
- For endpoint 0, Nat.not_lt_zero makes every response coordinate choose U. The closed
  false Bool branch also selects U in the published MDDH sample law.
- For endpoint d, the actual PUBLIC core theorem Fin.is_lt states b.val<d for b:Fin d,
  so each hybrid coordinate chooses M*S. The closed true Bool branch selects M*S in the
  published sample. Final function eta is core/Mathlib definitional equality only.

All original scalar draws are RETAINED in both experiments, including the unused S/U
branch coordinates. Consequently there is no need to count, remove a sample, or use
expect_const. The same exact identities cover d=0 or ell=0 without case assumptions.
No hPreScalar/ColumnLaws/advice/realisability/slack theorem is required for these endpoints.

## Actual static searches/readings

Read MddhAdvLe.skeleton.lean.inc:22-50 (exact hybrid and target); CURRENT MatrixDH/Defs.lean
MDDH sample/game readers around :201-233; Games/Probability.lean:116-137 and :208-229;
Games/Advantage.lean:67. Compared the existing narrow public-reader proof pattern in
Pairing/Linear.lean:dlinMatrixGame_real_accept (:356-358), without copying any algorithm.

rg searched Fin.is_lt/isLt and finite-index conditional-reader uses in core Fin, TCSlib
Pairing and FE; located and read the exact public theorem
  Init/Data/Fin/Lemmas.lean:32, @[simp] theorem is_lt (a : Fin n) : (a : Nat)<n := a.2.
This is the theorem used, NOT a guessed or explicitly unfolded Fin.isLt projection.
Nat.not_lt_zero was also located in a standard existing Fin zero-elimination use.

No new helper exists to probe. Native focus is the finite-index predicate simplification
and common probability/sample spine; no completed hEnds/main-proof or standard-only
status is asserted before root checks it.

## Root native correction (supersedes original candidate status)

Root verified Bool.true_eq_true does NOT exist and replaced it by the verified reduceIte
simproc; the corrected LIVE hEnds then passed natively. The original archived candidate
is marked SUPERSEDED and should not be integrated verbatim. This was a child reader-name
error, not a mathematical obstruction. Future drafts must not guess that Bool name.
