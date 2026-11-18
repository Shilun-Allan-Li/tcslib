# Targets and pure assembly handoff

Draft paths are for Wee20/Targets/*.lean and Wee20/Targets.lean, not the FE root.
No Lean, lake, build, Git mutation, machine construction, sampler implementation or
additional agent was used. These are source-independent specifications around the live
algorithms, plus pure assembly and a shared realisation-API proof. Root must elaborate.

## Public API

- `SchemeTargets G ℓ n d`: five explicit fields `pubGen_eff`, `setup_eff`, `enc_eff`,
  `keyGen_eff`, `dec_eff`, with `schemeTargets_iff`.
- `SimTargets G ℓ n d`: `sim_setup_eff`, `sim_enc_eff`, `sim_key_eff`,
  `sa_setup_eff`, `sa_enc_eff`, `sa_key_eff`, with `simTargets_iff`.
- `PGTargets ℓ n' d`: `lgen_eff`, `rec_eff`, with `pgTargets_iff`.
- `LinearEfficient G`: one `FinTM Bool` and `PolyExpr`, before every numeric ℓ,n,d,κ
  and all other encryption inputs. Uses `FinTM.ComputesInTime` directly, not a new
  time predicate. Reader `linearEfficient_iff` and actual `PHFE.linearEncInput_eq`.
- `MddhPreTargets G`: p,hp,d,ℓ,D then one uniform PC witness, before κ, scalar advice
  and challenge. Reader `mddhPreTargets_iff`.
- `mddhRealizable_of_preTarget`: direct term proof through the shared
  `exists_realizesOn_of_preTarget_id`, existing advice length bound and `congr` reader.
- `Targets G ℓ n d`: `scheme`, `simulators`, `garbling`, `linear`, `mddh` fields;
  `targets_iff` is their conjunction.
- Pure assembly `layeredPG ℓ n' d hT`, `wee20PHFE G ℓ n d hT`,
  `wee20Sim G ℓ n d hT`, `wee20SASim G ℓ n d hT` takes the matching subtarget Prop.
  Each has a term-proved `_toRaw` reader. The combined target gives these proofs via
  projections. Simulators live over the raw scheme (equivalent to the efficient
  scheme's `.toRaw` by `wee20PHFE_toRaw`), avoiding an unnecessary scheme-target arg.
- Exact width readers `wee20PHFE_mpkLen_eval` and `wee20PHFE_ctLen_eval` are term proofs
  from assembly readers and raw width readers, with no foreign raw bundle unfolding.

## Refinements and source fidelity

The public generator draw is an extra honest target approved by the user, because PPGen
now attaches a uniform nonidentity g after drawing the group description. The existing
uniform group generator is reused. Each target still uses one complete draw type; no
product-of-samplers construction is asserted.

Both simulator interfaces have three targets independently. The committed targets use
full Omega/state/index encodings; the SA targets use only state,x and state,x,f,µ. The
canonical class scalar codec is retained. Generic raw `.toSim` does not supply an
unpublished efficient parameter-preprocessing closure.

PG target witnesses precede both κ and arbitrary positive p. The actual input includes
binary p/dimensions/function data. PG has deterministic targets only. Its structural
mBound field is independent of these targets, and no raw correctness/security theorem
has any target hypothesis.

`LinearEfficient` strengthens GJLS21 Def 4.6's circuit/supported-key formulation to a
single uniform finite Turing machine and all typed keys. The explicit input contains
numeric ℓ,n, unary κ, pp, pk, x, y, complete draw; it never computes the public modulus.
There is one q(κ), independent of numeric dimensions and degree. The bound is
(ℓ+n)*q(κ) on 0<ℓ+n. Width of each scalar is absorbed in q. Raw algorithms remain total
for zero dimensions; they are outside this positive-size efficiency target. No degree
header is needed, since the encryption core does not use degree or a function description.
This is an explicitly disclosed source reading and required strengthening.

The public key is exactly (16+24n+8ℓ)wG+10 bits in the actual nested-pair encoding. The
ciphertext is exactly (6n+5)wG, excluding public x, independent of ℓ and degree. Both widths
reuse the existing numeric readers; no new arithmetic proof is invented.

The MDDH preprocessing target's D quantifier is intentionally retained as requested,
although the preprocessor itself is independent of D. It permits the Phase B witness to
be chosen for a fixed D. It is uniform in κ and every scalar advice/challenge pair. The
preprocessing proof reads the shared RealizesOn contract via published APIs and imposes
only the library's encoded-challenge/layout-length-coin requirement.

## Anticipated parent additions

- Assembly expects `wee20PHFE_raw_mpkLen G ℓ n d PG`, which root agreed to publish as rfl.
  The raw ctLen reader already existed.
- Sim/Assembly import `PHFE.CommittedSimulator`, added by root and inspected in place;
  `wee20Sim_raw G ℓ n d PG := (wee20SASim_raw G ℓ n d PG).toSim`.
- All imports use Wee20/Targets/ module paths. Parent should avoid overwriting existing
  elaboration fixes in shared FE and SA modules when copying these independent drafts.

## Reuse/search evidence

Searches/read-only inspections in live worktree:

- Definitions/Efficient: all five exact field specs, including dependent EncDraw/KeyDraw.
- Definitions/Simulator and SemiAdaptive/Simulator: exact shared sampler target inputs,
  draw encodings, encoded pair outputs and cores; no local copy of the contract.
- PartialGarbling/Defs and /Layered: lgenInput/recInput/encLgen/encRec and layeredPG_raw.
- PHFE/{Data,Core,Widths,Encodings,Raw,Simulator,CommittedSimulator}: literal outer
  algorithms, codecs, input dependency, scalar value conversion and exact widths.
- MatrixDH/SelfReduction: mddhPre, mddhAdviceEnc, mddhAdviceLen,
  length_mddhAdviceEnc_le, dlinToMddh_eq, mddhRealizable_iff.
- Asymptotic/Realization lines 155-161, 233-250: RealizesOn.congr and
  exists_realizesOn_of_preTarget_id.
- TuringMachine/Finite lines 275-291: ComputesInTime/ComputesFunInTime; the former
  is precisely the pointwise typed input/output/time target needed here.
- `rg` by intended target/helper names across TCSlib found no existing target or
  dimension-uniform PHFE encryption input specification.
- No exact?/apply? probes were run because agent build/Lean use is forbidden.

Source review for the linear target: complete existing PNG
`/private/tmp/io-phfe-source-review/lead/gjls21-26.png` was inspected, and extracted text
around Def 4.6 read. Printed p.22 = PDF p.26. The source defines circuit size
(|x|+|y|)*poly(λ), all pp in PPGen support and keys in Setup support. Other citations reuse
previously inspected verified sources and existing root public-interface source tags.

## Static verification

See static-checks.txt, declarations.tsv, admissions.tsv. All targets are actual named Props,
not admitted theorems; every `_iff` and algorithm/assembly reader has a term proof. No sorry
occurs in the six Lean files. No file approaches 600 lines. No tactic blocks were used.

The drafting generator was removed after review so it cannot overwrite the final
static fixes or the added width readers. Only reviewed .lean files should be copied.
