# Subagent c: generic Alice copying simulator

`HybridProof/AliceSimulator.lean` contains ten whole declarations: raw word
function/reader/all-input polynomial-time proof; uniform simulator/reader/coin
polynomial/uniformity/runAtL contracts; and generic real-ideal statistical and
distinguishing bounds. The machine depends only on its coin polynomial, before
any choice of functionality, inputs, bad event or distinguisher.

The coupling theorem takes an explicit coin equivalence and a nonempty
independent second tape, and an off-bad identity whose outer sample is
`pairEncode view.encode (List.ofFn fB)`. It does not see Yao definitions.

## Overlap and reuse

- The raw view word specializes `View.encode_mk`, with one prescribed received
  message, and uses the published NUPPT layout projections. The all-input
  polynomial-time proof composes these projections, empty constants and
  pairEncode. It reuses Strategy.encodeMsgs_cons/nil for the singleton history.
- The machine and its properties reuse NUPPT.ofPolyTimeUniform,
  ofPolyTimeUniform_uniform, coins_ofPolyTimeUniform, runAtL_ofPolyTimeUniform,
  advInput_eq, inParam_eq, inArg_eq and inCoins_eq. No machine is rebuilt.
- The ideal sample uses Functionality.idealA_eq, NUPPT.runAt_eq and the new
  simulator_runAtL contract. The probability proof reuses StatisticalSwitch,
  statClose_iff, uprob_fst, uprob_comp_equiv and distAdv_le_of_statClose.
- Closest unmerged source: #318 ObliviousTransfer/Simulators.lean:103
  `simAView` and :242 `simAView_layout` construct OT-specific simulated views
  with a generator index, two sampled words and a two-message history. This
  one-message copying simulator has a different input/output contract. No code
  was copied and no OT coin-segment utility was re-derived.
- sc-compose ComposeSecurity/Sim.lean:54 `simV` and related view assemblers
  simulate subprotocol runs and rebuild composed views. They are related uses
  of the same public encoding/machine APIs, not a reusable copying simulator.
  The search/declaration-index evidence is in search.log.

## Verified result

AliceSimulator-02 passed with zero errors. Its only repair made predicates for
uprob_fst and uprob_comp_equiv explicit. Axioms-01 covers all ten stored
constants, including the noncomputable simulator definition: only standard
axioms, and every constant closure reports sorried=[]. All four A/B by
strict/coe diagnostic whole-file seals pass, no source repair needed. The
subtree lint reports0FAIL/0WARN. Final source:150 lines, width at most100,
no sorry. The lead still reruns final merged verification.
