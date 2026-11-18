# Linear draft inventory and source findings

Draft: /private/tmp/io-phfe-drafts/Pairing/Linear.lean.
347 lines; maximum width 97; 14 term equation/iff readers; 7 substantive admissions.
No tactic blocks, Lean/lake/proof checks, git mutations, or custom finite-type instances.
Lead-only exact?/apply? and elaboration checks remain pending.

## Sources actually inspected

The lead verified all five dispatch SHA-256 values before authorizing PDF reading.
Each PDF was read in place in the supplied `sources/` folder; no PDF was copied.
Text extraction was navigation only; the following complete page PNGs were inspected:

- JLS26 PDF page 3 (printed 1:3), section 1.1: DLIN has random tuple
  (g^a,g^b,g^(ar),g^(bs),g^t), not a fully random three-coordinate response.
  Zero a,b,r,s,t are permitted. The fixed canonical generator is public through the group.
- JLS26 PDF pages 7-8 (printed 1:7-1:8), section 1.4: symmetric DLIN gives public-key PHFE
  by Wee, for constant-degree public and degree-two private computation.
- JLS26 PDF page 21 (printed 1:21), Theorem 5.1: bilateral DLIN on asymmetric groups is
  implied by symmetric DLIN; the theorem consumes the PHFE pipeline through GJLS21.
- GJLS21 PDF page 21 (printed 17), section 3: DLIN_p samples a,b uniformly and outputs
  A=((a,0),(0,b),(1,1)).
- GJLS21 PDF page 22 (printed 18), Definition 3.3: real challenge gives [A],[Ar] in both
  source groups; random challenge gives [A],[u] with u FULLY uniform in F_p^3.

The JLS26 printed page numbers include an article prefix `1:`; citations use the dispatch's
short page convention, e.g. p.3, and section/theorem locators.

## Newly explicit presentation discrepancy

The canonical JLS26 and GJLS21 matrix real responses agree exactly. Their random responses
are not exactly identical when a=0 or b=0. Conditional on a,b nonzero, multiplication by
a and b bijects r,s to uniform response coordinates; the random t is independent. Thus the
probability of the exceptional event is exactly 2/p - 1/p^2. The draft exposes this slack
and does not assert a false random-game identity. The lead approved canonical JLS26 tuple
DLIN as primary and an explicit matrix comparison before this draft was finalized.

The averaged slack is `BilinearGen.dlinMatrixSlack`. Any MatrixDH reduction using the fully
uniform GJLS21 response must include this correction when composed with primary dlinAdv.

## Shared public parameters, not duplicated framework scaffolding

Imports the lead's new `Pairing/MatrixDH/Parameters.lean` exactly as written.
`BilinearGen.DLINChallenge G k` stores:

- `pp : PublicParams G k`;
- five group points over `G.group k pp.description.val`.

It does not store generator coins. PublicParams already carries the actual reachable
GroupDescription and nonidentity generator. This permits dlinEnc_injective even when
different generator coin strings produce equal public descriptions. Proof irrelevance
removes the two proposition witnesses. Honest samples begin with `publicParamsGen G k`,
whose published reader states the sequential group-coin/nonidentity-generator draws.

No decoding algorithm or choice of scalar witnesses from group points is introduced.
`dlinEnc` has the required shape `forall k, DLINChallenge G k -> List Bool` for RealizesOn.
Its exact length is `2*descLen(k)+11*wG(k)+12`, from six nested pair encodings.

## Definitions and readers

All BilinearGen names have explicit `G` as their first argument.

- Pairing.dlinStr / dlinStr_eq: nested public tuple string.
- Pairing.dlinMatrix / dlinMatrix_eq: the 3-by-2 scalar matrix.
- BilinearGen.DLINChallenge: shared parameters plus five source-group points.
- BilinearGen.dlinChallenge / dlinChallenge_eq: public record constructor.
- BilinearGen.dlinEnc / dlinEnc_eq, dlinEnc_dlinChallenge: public input encoding.
- BilinearGen.dlinSample / dlinSample_eq: canonical JLS26 challenge law.
- BilinearGen.dlinGame / dlinGame_eq: independent NUPPT coin draw and verdict.
- BilinearGen.dlinAdv / dlinAdv_eq: two-experiment advantage.
- BilinearGen.DLINAssumption / dlinAssumption_iff: non-uniform PPT negligibility.
- BilinearGen.SubexpDLIN / subexpDLIN_iff: existing SubexpHard API, not a new notion.
- BilinearGen.dlinMatrixSample / dlinMatrixSample_eq: literal matrix challenge law.
- BilinearGen.dlinMatrixGame / dlinMatrixGame_eq: matrix law plus machine coins.
- BilinearGen.dlinMatrixAdv / dlinMatrixAdv_eq: matrix-form advantage.
- BilinearGen.dlinMatrixSlack / dlinMatrixSlack_eq: averaged zero-diagonal correction.

Substantive statements:

- length_dlinStr: reuse Turing.length_pairEncode, not a new pairing-length lemma.
- dlinMatrix_mulVec: transport the displayed matrix rows through Mathlib.mulVec.
- dlinEnc_injective: reuse Turing.pairEncode_injective, List.ofFn_injective, encG_injective.
- length_dlinEnc: reuse length_dlinStr and BilinearGen.length_desc with reachability.
- dlinMatrixGame_real_accept: equality of acceptance laws, not free-oracle syntax;
  unused random scalar versus random-vector draws are integrated by expect_const.
- dlinMatrixGame_random_gap_le: nonzero-scalar coordinate bijections via
  ProbComp.expect_sample_equiv, explicit exceptional event.
- dlinMatrixAdv_le: triangle inequality using shared advantage/accept readers.

## Exact reuse searches and nearby declarations

Working tree read:
/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange

1. Names:
   rg -n 'dlinStr|dlinMatrix|DLINChallenge|dlinChallenge|dlinEnc|dlinSample|dlinGame|dlinAdv|DLINAssumption|SubexpDLIN' \
     TCSlib .lake/packages/mathlib/Mathlib
   No matches before creating this scratch draft.
2. Conclusion shapes:
   rg -n 'a \* r.*b \* s|r \+ s|2 /.*order.*1 /|responseSum' \
     TCSlib/Cryptography/Pairing .lake/packages/mathlib/Mathlib/Data/ZMod
   No matches.
3. Pairing serialization:
   rg -n 'length_pairEncode|theorem pairEncode_injective|def pairEncode' \
     TCSlib/Complexity/TuringMachine
   Exact public definitions/readers: TuringMachine/Encoding.lean:136,173,220.
4. Probability:
   rg -n 'prob_sample|expect_sample_equiv|expect_const|expect_sample' \
     TCSlib/Cryptography/Games/Probability.lean
   Reuse expect_const:174, expect_sample:147, expect_sample_equiv:304, and binding readers.
5. Exceptional-event machinery:
   Read Games/Hopping.lean:77 prob_split and the nearby public event/expectation readers;
   no local general-purpose probability lemma was introduced.
6. Existing assumption pattern:
   Read Pairing/Assumptions.lean:79-92 (tupleStr),225-270 (dbdhGame,dbdhAdv,DBDHAssumption).
   That file is not imported or edited. Pattern reuse only; no private declaration copied.
7. NUPPT verdict:
   Read Asymptotic/Adversary.lean:381-388, distinguisherL and distinguisherL_eq.
8. Subexponential predicates:
   Read Foundations/Subexponential.lean:274-279, SubexpHard and subexpHard_iff.
9. Coin-dependent instance precedent:
   Read IdentityBased/Defs.lean _onSpec readers and sidGame:529-543. The new draft needs no
   oracle subtype coercion: publicParamsGen is sequenced before its field-dependent samples.
10. Scalar matrix notation:
   Verified precise import Mathlib.Data.Fin.VecNotation and its vecCons macro at line 68;
   nested vector literals represent the matrix rows. An initial lookup for
   Mathlib.Data.Matrix.Notation found no such file and was replaced by this smaller import.

No duplicate DLIN or matrix-DLIN definition was found. The wire format parallels public
`tupleStr`, with six source-group entries rather than four source/one target entries;
this representation-near-copy is disclosed here. All substantive exact?/apply? probes and
full-name clash validation are deferred to the lead before a checkpoint is claimed.
