# Bob simulator constructor and efficiency handoff

Worker `/root/evaluation` proved the new `BobSimulator.lean` module (152 lines).
The raw polynomial-time function assembles exactly
`View.encode ⟨inParam, ⟨fst(inArg), activeAnswers⟩, [], [fakeMessage]⟩`.
The uniform machine takes two fixed polynomial-time raw leaf maps and a fixed coin
polynomial; no distinguisher appears in its parameters. The exact `runAtL` and typed
`runAt` contracts evaluate both leaves on the canonical
`NUPPT.layout (1^n) ⟨y,f⟩ [] r`. The `idealB_eq` reader pairs that simulated view with
Alice's actual `(F.f n x y).1`, while passing only Bob's prescribed `.2` to the leaves.
This constructs the generic simulator and its exact endpoint; the fake-garbling leaf
proofs and privacy hybrid are separate consumers.

## Reuse and overlap

Searches are recorded in `reuse-search.log`. No generic public View polynomial-time
builder was found. The nearest new-unit relative is
`HybridProof/AliceSimulator.lean:46` (`raw`) and `:59`
(`polyTimeComputable_raw`). Both use the pairing closure to build a view, but Alice's
copying constructor has empty OT answers, retains its tape and receives the supplied
output; it cannot represent Bob's two varying leaf maps, empty tape and fake message.
The new proof uses the public pairing and view-encoding contracts rather than copying
any private lemma or introducing a machine implementation.

The `simulator` wrapper directly reuses `NUPPT.ofPolyTimeUniform`. Its uniformity,
coin and run readers specialize the public factory readers in
`Randomized/PPT.lean:403`, `:412`, and `:429`. The typed run contract reuses
`NUPPT.runAt_eq` (`PPT.lean:241`). These specializations provide the required API for
the new public simulator definition. The endpoint reader specializes
`Functionality.idealB_eq` (`SecureComputation/Defs.lean:138`) with that run contract;
it rederives no probability identity. All view equations use `View.encode_mk`
(`ZeroKnowledge/Interaction.lean:302`) and the public message-list readers.

No unmerged sc-garble, #318 or sc-compose declaration is rederived. No frozen file or
existing helper was edited. No new host is introduced: all control and machine
construction is supplied by the existing PPT factory.

## Verification

The development check `bobsimulator-01.log` passes with no diagnostics. All four
whole-file A/B strict/coe seals pass with zero errors and `-DmaxErrors=0` over the full
imported TCSlib closure. The file is absent at the issue base. All ten stored constants
have printed signatures, only the standard `propext`, `Classical.choice`, `Quot.sound`
axioms, and empty transitive sorry closures. The identical seal preamble reuses the
paired controls already delivered in immutable evidence `b/`.

The source has no width/size violation, admission or explicit unfold/delta. Every Lean
command used the shared three-slot wrapper, tag `sc-yao-b`, with the worker's own
`.lake/sc-yao-oleans`. No child commit or delivery push was made.
