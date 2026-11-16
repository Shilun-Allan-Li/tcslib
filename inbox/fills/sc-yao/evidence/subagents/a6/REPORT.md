# Generic OT-hybrid Bob-view shape

BobViewShape.encode_viewV_eq is parameterized by H : HybridProtocol otFunctionality,
first : Nat → word → word → word, two rounds, Alice-first, Bob's constant-zero coin
polynomial, and Alice's empty-history sender equation. It proves the actual encoded main
view on privA/privB equals View.encode of common unary input, Bob's input paired with
H.answersB, empty private tape, and the sole first message at n/xs/Alice's tape. Inputs xs/ys
are arbitrary raw words; r is the actual typed hybrid coin sample.

This is the requested extraction/generalization of the lead's checked BobViewGlue probe.
It imports neither Yao nor any Yao semantic definition. It consumes TwoMoveViews' existing
encoded view contract, using Bob's actual next function on a singleton history and its
reflexive reader. Thus there is no additional Bob reply or Alice echo hypothesis.

The zero-tape proof uses List.length_ofFn, Strategy.coinLen_eq and PolyExpr.eval_const.
Parameter-length normalization uses congrArg on the nondependent first-message word
function rather than rewriting a tape-dependent execution type. Hybrid private-input and
View encoding readers finish the calculation. No transcript/view machinery was re-proved,
and no new probability proof, machine, or host was introduced.

The lead seeded the unmodified TwoMoveViews source/olean; its source remains lead-owned.
No frozen or other agent-owned source was edited. The probe-specific calculation is now a
single generic exported declaration to reduce the frozen Yao body size.

Normal01 had zero errors and one unused-tactic warning inherited from the probe: in the
generic setting, the coinLen goal was already in the desired form. That no-op change line
was removed. Original source/logs and all first-run seal sources are retained. The final
clean source has a separate ordinary check, four full-file seals and full trace under
probe-runs/clean-01. Both error diagnostic forms are counted; maxErrors=0 and the full
imported TCSlib closure are used. Style lint has zero findings.

Final clean-source ordinary check and all four seal variants pass with zero errors and
zero normal warnings. Controls behave as expected (four positive passes, four deliberately
sealed negatives with exactly one error each). The complete sixteen-owned-module trace
covers 297 stored constants, including generated/private declarations, with no transitive
admissions and only standard axioms. All sixty-four final owned-module seal variants pass.
No own check remains live. No child commit or exchange delivery was performed.
