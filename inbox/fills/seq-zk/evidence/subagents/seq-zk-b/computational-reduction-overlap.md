# Computational reduction search and overlap disclosure

Worker: seq-zk-b. Source SHA256: 32d8ef575f769772b7e8b4b309ddf55d3e52c605c0f09c7fdc98cdbec11e6bb3.

Searches are retained verbatim in computational-reduction-searches.log. No existing generic
metadata-driven normalized one-phase/simulated-suffix reduction was found. The nearest
concrete reductions are ThreeColoring/ColZKMachine.lean exists_colHidingRed (commitment
hiding with advice) and SimulatorLemmas.lean exists_hybRed_ge (commitment-coordinate hybrid).
They do not implement this sequential-protocol continuation; no proof body was copied.

Direct reuse: Complexity/Randomized/Closure.lean exists_comp, exists_seq, exists_withAdvice;
public NUPPT uniform constructor, input/layout and activation readers; WrappedVerifier
phaseAux_eq/phaseAux_poly; PhaseView normalization PT reader; SuffixMachine phaseSuffix_poly;
EncodingMachines unary arithmetic; public pair/encoded-message readers. No new host or
hand-built control machine was introduced. Raw prefix advice decodes totally, including
malformed words, without testing witness or reachability.

phaseContinuation repeats the normalized-candidate append expression of phaseStep and the
local phasePrefix_poly assembly. Its candidate is supplied externally, while phaseStep
computes it by activating S, so phaseStep_poly cannot directly instantiate this function.
The PT leaf is re-derived from the published normalization/pair/append readers, then the
published arbitrary-start/prefix suffix theorem is applied. A later extraction could share
that candidate-append PT leaf. This overlap and reuse were explicitly approved by the lead.

The uniform continuation sampler is nearest exists_phaseSimulator, but it reads arbitrary
advised metadata/current raw candidate rather than constructing a whole repetition from an
empty prefix. Both use the same published uniform constructor, not duplicated hosts.
All additions stay within the approved helper scope; no frozen source or Mathlib root changed.
