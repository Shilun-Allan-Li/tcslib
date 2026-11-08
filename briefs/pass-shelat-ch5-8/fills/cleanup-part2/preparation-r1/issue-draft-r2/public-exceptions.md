# Cleanup part 2: permitted public-surface exceptions

**ISSUE CANDIDATE r2 — paired with `brief.md`, not independently issued.** Source ancestor: `1aa5506f58f77c215e56d24311ec33bd931cacf1`. This is the exhaustive exception policy, interpreted with the exact named targets/roles/raw baselines in the input manifests. It does not grant general API redesign. New names below are work targets, not existing-API attestations.

## General freeze and representation discipline

Every existing public statement retains all inputs, universes, hypotheses, explicit costs, codomains, visibility and attributes unless a row below expressly permits a source-header change. Every existing public non-theorem body remains frozen except the exact helper aliases/moves here and the three J/N definitions in `inputs/public-definition-freeze.json`. Security/correctness/sampler/collection/protocol/efficiency claims are unchanged. No new admission, axiom, unsafe proof, simp attribute, general host, algorithm, cost model or assumption is permitted.

A named copied theorem may be removed after every user migrates, or kept as a one-line theorem alias with its old header. An approved helper definition may become a semantically identical one-line Mathlib/canonical alias; this is not permission to edit unrelated public data definitions that reference it. Keep a load-bearing alias when necessary to preserve such a body verbatim. Record actual old→new names, owners, full headers/bodies and reader routes, including every affected block-family statement in Gate03h/i/k. Do not hide removed public keys behind an aggregate header count.

For a copied/relocated ordinary helper, complete owner-side readers accompany it. A function gets forward/inverse/case equations as appropriate; a predicate gets iff; a structure gets every data-field equation; a machine gets public run/coin/field contracts, not a raw machine-body alias. No consumer may acquire a foreign body conversion because a definition moved. Prefer Mathlib/core equivalence terms or the canonical published reader to converting through a foreign TCSlib alias.

## X1 — generic blocks and Bool/inverse aliases (DL9/G13)

Canonical existing low owner: **`TCSlib/Cryptography/Asymptotic/Adversary.lean`**. Relocate the generic construction with its existing generic signature, using the Mathlib fin-product/curry construction:

```lean
-- Namespace TCSlib.Cryptography; exact existing generic codomain is retained.
def blocksEquivX (q ℓ : ℕ) (X : Type*) :
    (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X)
```

The Bool form retains its existing full name/type; it may move to the same low owner as a specialization/one-line alias:

```lean
-- Namespace TCSlib.Cryptography.FunFamily
def blocks (q ℓ : ℕ) :
    (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
```

Provide ordinary generic/Bool forward and inverse readers there, preserving the existing formulas: forward `(i,j)` reads `finProdFinEquiv (i,j)`; inverse flat index reads its `divNat`/`modNat` coordinates. Preserve multiplication/index order, all q/ℓ=0 cases and universes. Do not replace `Type*` by Bool, strengthen positivity, reorder coordinates or make the backward equivalence forward.

The following existing copied data keys may be retired or replaced by one-line compatibility aliases to these exact specializations:

| Source | Existing full key / form |
|---|---|
| `Asymptotic/OneWay.lean` | `TCSlib.Cryptography.FunFamily.blocks` (canonical Bool form retained; move/alias only). |
| `Asymptotic/HardCoreGL.lean` | `TCSlib.Cryptography.blocksEquivX` (canonical generic form retained; same-signature relocation). |
| `Asymptotic/OneWayYao.lean` | `TCSlib.Cryptography.OneWay.blocksE`. |
| `Asymptotic/HardCoreLoops.lean` | `TCSlib.Cryptography.blocksEquiv`. |
| `Asymptotic/EnsemblesLemmas.lean` | `TCSlib.Cryptography.EnsembleLemmas.blocks`. |
| `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean` | `TCSlib.Cryptography.GI.blocksEquiv`, **reverse** type `(Fin m → Fin c → Bool) ≃ (Fin (m*c) → Bool)`. |
| `Asymptotic/Ensembles.lean` | Private `TCSlib.Cryptography.Ensemble.blocks`; retire the construction or keep only a load-bearing private alias to preserve `Ensemble.copies`' frozen body. |
| `Candidates/Factoring.lean` | Private `fac_chunkEquiv`, only its named same block-equivalence representation. |

Their named same-family reader/slice theorem headers may substitute the canonical blocks/aliases, with old→new full-header mapping. Specifically consolidate `MultiMsg.take_drop_ofFn_blocks` with `EnsembleLemmas.take_drop_ofFn_blocks`; retain old-header aliases where needed. The named G13 window lemmas in Concrete/ColZKLemmas/ColRepSound/Factoring/OneWay/Primality/EnsemblesLemmas/MultiMessageLemmas may become corollaries. A same-contract relocation of existing `ColZK.ofFn_drop_take` to existing CollectionsHelpers is allowed if it is genuinely needed by the named windows; preserve its old public header by alias and do not introduce a second independent proof. New general window claims outside those exact existing contracts are E-API.

`Complexity.Randomized` RandomBits.blocksEquiv into `Fin (2^b)` is different and excluded. Other public data bodies, including product/copy/sampler constructions, are not authorized for broad rewrites merely because they mention a block helper.

## X2 — applied composition/congruence duplicate theorem retirements (DL10)

Use existing `Complexity.PolyTimeComputable.comp'` and `.congr`; their headers/bodies are not redesigned. Named copied proof keys may be deleted after migrating users or kept as one-line same-header aliases:

- Private `Complexity.NUPPT.ptc_comp` in Closure; private Collection.ptc_comp, EnsembleLemmas.ptc_comp and the separate file-private TCSlib.Cryptography.ptc_comp identities in Universal/UniversalLemmas.
- Public `TCSlib.Cryptography.ColMachines.ptc_comp` and `TCSlib.Cryptography.ptcComp` in HardCoreLoops.
- Public `GI.ptc_congr`, `ColMachines.ptc_congr`, `ColSimMachine.ptc_congr`; private `GIZK.ptc_congr`.

Private identities remain file-qualified in the report. For the four old congr proofs, preserve the reversed pointwise-equality premise by symmetry rather than changing a consumer theorem's hypothesis. No new composition definition/theorem family.

## X3 — stateFind and fixed-round theorem sharing (DL11/G22)

`TCSlib.Cryptography.GI.stateFind` and `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_stateFind` may be removed or made same-header aliases to `Complexity.polyTimeComputable_stateFind`. Their user proof bodies may be repointed, not their claims.

Move the existing generic fixed-round theorem from HardCoreLoops into **Repetition after `Complexity.polyTimeComputable_iterate`**, with canonical fullname **`Complexity.StateLoop.polyTimeComputable_stateIterate`** and exactly this existing logical type:

```lean
theorem polyTimeComputable_stateIterate {start step out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hout : PolyTimeComputable out) (B : PolyExpr) :
    PolyTimeComputable fun x =>
      out ((gstep step B)^[(pairEncode x (start x)).length]
        (pairEncode x (start x)))
```

Here `gstep` is `Complexity.StateLoop.gstep`; qualified spelling may reflect the destination namespace. An optional old `TCSlib.Cryptography.polyTimeComputable_stateIterate` theorem alias retains its exact old header. The private dlb specialization may be removed/rederived. Do not generalize the round schedule, orbit guard or output; no new loop host. The existing **data** `GGMRed.stateLoopFun` and its existing evaluation statement remain frozen: a computability proposition is not a function replacement. Owner readers/proof repairs are allowed within its role.

## X4 — zero probability, probability-one and decoder theorem copies (DL13–15)

- Remove public `TCSlib.Cryptography.negligible_const_zero` from ZeroKnowledge/Defs after its user migrates to `negligible_zero`; do not change PerfectZK/StatZK claims.
- Reuse public `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` and retire Adversary's private copy. Use the existing public theorem through a precise acyclic import. No new foundational relocation or generic probability theorem is commissioned by this row, and no Nonempty assumption is added.
- Publish one `TCSlib.Cryptography.decodeFin_eq_some_iff` in Adversary with the existing GGM contract `decodeFin ℓ w = some x ↔ w = List.ofFn x`, all natural ℓ/arbitrary w/x. Retire/repoint private FunFamily.decodeFin_eq_some_iff in Collections and public GGMRed.decodeFin_eq_some_iff, keeping an old-header alias if load-bearing. Existing `ofFn_of_decodeFin_eq_some` retains its reversed conclusion `List.ofFn x = w`; its proof becomes a corollary. BitCodec's private eq_ofFn_of_decodeFin may retire. No decoder implementation, fallback or empty-width behavior changes.

## X5 — DL17 theorem retirements

Only these public `Complexity.StateLoop` duplicate theorem keys may be removed after users migrate: `headBit_poly`, `tail_poly`, `isNil_poly`, `not_poly`, `or_poly`, `xor_poly`, `length_pairFstD_add_pairSndD_le`. Do not remove `cons_poly`; do not change their consumers' headers or the underlying primitives. Exact List.tail/drop1 representation conversions belong in proofs through public lemmas.

## X6 — complete `decodeOracleMove` reading interface (D)

Add a public total equation and/or a complete case partition beside `decodeOracleMove` in PRF, preserving its existing definition and OracleMove type. Existing public pairEncode-false and true-two lemmas remain. Equal-length/wrong-length query corollaries and the precisely complementary malformed-word branch may be published; all inputs including ℓ=0 are covered, with no new hypothesis. Private decodeOracleMove_eq may be folded into the public interface. Its existing GGM query/verdict relationship retains its mathematical claim. No oracle codec, malformed default or reduction-game algorithm change.

## X7 — named unchanged-header numerical/restriction/count corollaries (G7/G10/G23)

The attached named G7/G10/G23 theorem proofs may become corollaries or load-bearing aliases of the existing public bounds/restriction/count APIs. Preserve all old theorem headers. In particular retain both `two_pow_size_le` and `two_pow_size_le_two_mul_succ` public claims while one independent proof is removed. Retain the old empty-codomain branch of pushesUniform_comp_injective; do not add Nonempty O. The private dlb_cut representation may be replaced only as needed for its named restriction specialization, not a new algorithm. No arbitrary move of public number-theory predicates or count functions is allowed.

## X8 — exact shared average-switch theorem (G18)

In **`TCSlib/Cryptography/Asymptotic/Sampling.lean`**, publish `TCSlib.Cryptography.uexp_le_of_statClose` by promoting the exact contract of current private Candidates.rabin_uexp_le (`Rabin.lean:1641–1644`):

```lean
theorem uexp_le_of_statClose {σ τ γ : Type*}
    [Fintype σ] [Fintype τ] [Fintype γ] [DecidableEq γ]
    {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
    (Aux : γ → Type) [∀ c, Fintype (Aux c)] [∀ c, Nonempty (Aux c)]
    (Q : ∀ c, Aux c → Prop) :
    uexp (fun s => uprob (Q (X s))) ≤
      uexp (fun t => uprob (Q (Y t))) + δ
```

This is an implementation target; it does not yet exist at the ancestor. Preserve `Aux : γ → Type`, the dependent family, all listed instances, orientation/δ bound and empty σ/τ cases. Do not silently turn it into an arbitrary-real-expectation theorem or add Nonempty σ/τ. The named Rabin theorem and RSA.rsa_uprob_pi_eval/rsa_step_ii become corollaries/application routes, with their existing consumer claims unchanged.

At most one auxiliary general lemma is permitted if it avoids duplicating the proof's coordinate argument: an exact uniform-coordinate identity, in the same owner, that for finite γ with DecidableEq, finite/nonempty every Aux c, chosen c and predicate Q, `uprob (fun ω : ∀ c', Aux c' => Q (ω c)) = uprob Q`. State all existing needed assumptions explicitly, give its formula/sketch and record its exact new fullname/header. It is a lemma, not a new sampler/helper definition or host. If no helper is needed, do not add one.

## X9 — acyclic efficient-strategy-next sharing (G25)

Move the current ColZKMachine generic proof down to **SimulatorMachine before reply_poly**. Canonical new fullname: **`TCSlib.Cryptography.ColSimMachine.polyTimeComputable_next`**. Its type is unchanged:

```lean
theorem polyTimeComputable_next {V' : Strategy} (hV' : V'.Efficient)
    {X Z R C : List Bool → List Bool}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hR : PolyTimeComputable R) (hC : PolyTimeComputable C) :
    PolyTimeComputable fun w => V'.next (X w) (Z w) (R w) [C w]
```

Retain existing `TCSlib.Cryptography.ColZK.polyTimeComputable_next` at ColZKMachine as an exact old-header theorem alias. Repoint `ColSimMachine.reply_poly` through the generic theorem; repair both proofs through public interfaces rather than copied predicate destructuring. **SimulatorMachine must not import ColZKMachine.** ColZKMachine's existing import of SimulatorMachine remains the acyclic direction. `field_encodeMsgs` is already an alias and `distAdv_seed_to_coins` is not commissioned. The separately observed distAdv_sunglassRed proof may use existing distAdv_def, but sunglassRed's definition/body is frozen.

## X10 — the three J/N public-definition exceptions

The exact source/header/body/field baselines in `inputs/public-definition-freeze.json` bind these rows. These are not a license for other public non-theorem body changes.

| Existing full name | Permitted change | Invariants |
|---|---|---|
| `Complexity.PPT.toNUPPT` in NonUniform | Relocate to existing PPT owner. | Identical full name, header, visibility and body `A.1`; same subtype data. Publish the owner reader. |
| `Complexity.PPT.ofPolyTime` in NonUniform | Relocate to existing PPT owner. | Identical full name/header/visibility/body, same chosen NUPPT and uniformity proof contract. Publish owner field/run readers. |
| `Complexity.NUPPT.ofPolyTime` in PPT | Reexpress choose-proof access through an owner API instead of reducing foreign PolyTimeComputable. | Same header, chosen M/Ct/ct witnesses, coins/adv/advice, advice bound, halting/observable output/run contract and costs. No new choice witness or algorithm. |

Reader theorems may be placed beside these owning definitions with the same old headers or added ordinary reader headers as required. If proof reexpression changes source spelling of a field RHS, show that it names the **same** original witness/field for every input; merely constructing another machine with the same asymptotic behavior is insufficient. All original public machine contracts remain valid with identical logical claims. An ordinary predicate reader at its permitted upstream owner is allowed; a missing non-reader/general host is E-API.

## X11 — closed Mathlib replacements (M)

Seven exact keys are included:

| Existing key, namespace `TCSlib.Cryptography` | File | Permission |
|---|---|---|
| `NumberTheory.units_val_mem` | NumberTheory/Units | Proof shortening only. |
| Private `NumberTheory.two_mul_card_le_of_ne_top` | NumberTheory/Primality | Proof shortening only. |
| Private `NumberTheory.powOneSubgroup` | NumberTheory/Primality | Replace its subgroup construction by the exact Mathlib `(powMonoidHom m).ker` alias. |
| Private `NumberTheory.mem_powOneSubgroup` | NumberTheory/Primality | Derive its same-header iff from public kernel membership. |
| `NumberTheory.card_QR_prime` | NumberTheory/QuadraticResidues | Proof shortening only. |
| `NumberTheory.sq_pow_div_four_succ` | NumberTheory/QuadraticResidues | Proof shortening only. |
| `Candidates.fmultNat_eq_mul_prime` | Candidates/Factoring | Proof shortening of the key argument only. |

Keep every theorem header, and preserve the private alias's carrier/operation semantics and its membership reader. No new number theory, changed hypothesis, future Mathlib bump, Chebyshev/Korselt/BlumDensity discharge or optional RSA/domain rewrite.

## X12 — ordinary provider readers and named docs/imports

Within the exact finite permitted provider-only paths, add **only** ordinary function equations, complete case lemmas, predicate iff, data-field equations or machine run/coin/contract readers beside their existing owners. Each formula must expose the existing definition rather than a stronger proposition/new host. No automatic simp attributes. All original source/proofs/statements in provider-only files remain frozen; the expressly named existing-definition moves/repairs occur in consumer owners, not provider-only files. Publish new shared mathematical results only for the explicit block/window, state-iteration, decoder, average and strategy-next targets in this document; provider-only permission does not authorize arbitrary general lemmas. A needed ordinary owner reader for a definition already present at the issue ancestor may be independently implemented and checked under this permission even if unmerged PR #232 has a counterpart. Prefer a matching fullname/formula where appropriate and record that counterpart for maintainer reconciliation. This is no claim of availability and permits no reliance on unmerged code, prong-only statement/repair-patch copying or new Gate06 dependency.

Precise imports may change in editable files when needed by these routes and remain acyclic. E/F/K/L permit only the named import/proof/doc changes in the brief. In particular K/L's named doc-only theorem headers/proofs stay byte-identical. The completed col_zk/S2 sketches are not a new editing window.

## Evidence and admissions attached to every exception

For each removal/move/alias/new reader: keep the original complete source/header/body/attributes and new counterpart, fullnames and actual Name identities when elaborated, owner/import changes, scope reason, public reader path and quantitative/empty-case justification. Verify through complete final native/axiom/Rule10/source-list checks. Newly foreign reads caused by moving a definition are repairs, even if a consuming block stayed byte-identical.

Baseline admissions remain immutable per exact original owner/name. No direct sorry/admit/axiom may be added, filled, transferred or hidden by a removed helper. An approved new theorem alias/reader that necessarily inherits an unchanged baseline admitted dependency must name that subject and exact old→new dependency relation; it does not become standard-only by renaming. No other existing claim may gain an admitted dependency.

Outside these exceptions, report the smallest exact E-FREEZE/E-API requirement and continue independent work. No exception here authorizes Gate06-only source, efficiency/security proof filling, worker campaign pushes or a new external job. The separately pinned PFR environment bootstrap changes no mathematical role, public exception or source ownership: package sources remain immutable, and its adapter PATH is restricted to the 31 PFR checks as specified in brief.md.

**Not yet clear to merge — candidate exception contract awaiting final input/workflow review and user dispatch.**
