# GateHybridChain endpoint bound

GateHybridChain.endpoint_negligible combines one uniform nonnegative negligible bound on
actual selected-argument steps with unchanged-stage cases. For arbitrary input family Z n
and finite sampler tape σ n, it returns one negligible endpoint bound uniform over Z n.
Z n need not be finite or nonempty. The selected bound takes p:Fin(args.length) and hp:p.val<2;
b's stronger all-actual-p result feeds it by ignoring hp.

The hypotheses supply C n, size bound S, arity at most2, consistent wire values v n z,
sampler family H n z t, and a full-function congruence when stageBit families agree. The
proof reads size_eq to bound2*gatecount by(.mul(.const2)S).eval, uses GateStepCases.step_cases
for each step, and invokes the existing SliceReduction.chain_negligible unchanged. No
probability summation, semantic definition, machine, or arithmetic case proof is copied.
Reuse search and nearest public readers are recorded in SEARCH.md.

Normal01 PASS with0 errors/warnings/admissions. All4 complete-file A/B strict/coe seals
PASS, no exceptions, full imported TCSlib closure and -DmaxErrors=0. Both error: and
error(...) forms are counted. Every stored constant of the new module was traced: the
public theorem and both generated auxiliary proof constants,3 total, all empty sorry
closures and only propext/Classical.choice/Quot.sound. Style0,85lines/maxwidth90.

Exactly3 missing dependency modules were seeded from verified completed snapshots:
SelectedFields normal15 and GateStepCases normal03 API snapshots match their final c
archive sources byte-for-byte. SelectedSeed source matches b5 and its completed olean
matches b's current olean; own GateOccurrences source+olean already matched c. The exact
seed ledger is preserved. No dependency source was edited.

For the actual game, set Z n to the pair of input functions and H n z t=game n z.1 z.2 t.
GateHybrids.values_consistent supplies gate consistency; funext followed by
SelectedFields.sample_eq_of_stageBit_eq supplies hSameStage. Unwrap the resulting ∀n z
bound as fun n x y=>hBound n(x,y). No new semantic helper is needed.

Only this new helper source and its matching normal completed olean are handed off.
No frozen/root-owned edits, no commits/pushes/delivery. a10 skeleton remains immutable.
All own jobs completed normally and no live handle remains.
