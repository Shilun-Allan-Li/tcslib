# sc-garble · checkpoint 2

This is a partial checkpoint, with six of seven requested admissions proved. B1's
`sliceMultiMessageSecure_of_prfOut` remains for the final stage. The complete source series
is based on the exact PR #315 head `fbd37f447596d4207c8d08b7ef7602f57fe95198`; it is proved
modulo #315's merge. The issued exchange pack is pinned at
`7d85785c2e98f0bfdec081a875a9343f06043a8a`. Both issued checksum packs passed.
The local proof head is `fb7971f883839c4b02805eea79fa16acd325c5c2`. The unsigned format-patch series and complete identity/date
rows in `patches/COMMITS.tsv` reproduce every commit hash in an isolated scratch clone.
The proof branch remains local; only this assigned delivery path is pushed.

## Target status

| Target | Status |
|---|---|
| `spDecStr_wrongKey` | Proved; standard axioms only |
| `specialScheme_wrongKey` | Proved; standard axioms only |
| `specialScheme_multiMessageSecure` | Proved directly from D4; standard axioms only |
| `nestedSpecial_wrongKeyBot` | Proved; standard axioms only |
| `uprob_not_good_le` | Proved by averaging B2 |
| `yaoSeed_good_whp` | Proved using the stronger B2 seed law and disjoint blocks |
| `sliceMultiMessageSecure_of_prfOut` | Pending B1 post-map and maximizing advice |
| Required `uprob_not_good_le_of_perm` | Published and proved with the prescribed statement |

The source scan is exactly 32 → 26 admissions, removing precisely these six targets and
adding none. The remaining 26 admissions are in 12 modules; the final requirement is 25 in 11.

## B2 and the Yao proof

`good_of_no_crossOpening` reduces goodness to failure of all distinct-assignment row openings.
`uprob_crossOpening_le_of_perm` restricts the independent vertex-key table to distinct argument
vertices and a different output vertex, reads independent row coins, and averages `WrongKeyBot`
over the output key. Each gate has at most four assignments and three different assignments
per row, so existing finite union bounds give twelve events per gate.

The shared theorem `uprob_not_good_le_of_uniform_data` is stronger than B2's requested seed
law: permutations may depend on the raw seed. No bad-row event reads a permutation, so the
joint key/row-coin marginal alone must be uniform. `uprob_not_good_le_of_perm` is its exact
fixed-permutation corollary; the old uniform-permutation target averages that corollary.
This is a mathematical strengthening, not a weakened statement or additional hypothesis on B2.

Yao's key blocks `b*S+v` and row-half blocks `2*S+2*(4*i+idx(a))+b` are distinct and below
`10*S`. Binary assignment indices are injective below four for arities zero, one and two.
Restriction along the block/bit injection, followed only by standard equivalences, proves the
full uniform key/row-coin marginal. The unused `2*S` shift bits need no further law because
the stronger B2 seed theorem permits every seed-dependent permutation family.

The output collision corollary, located downstream in `GarblingSecurity/NestedBounds.lean`,
reuses `MultiMsg.uprob_eq_pair` and the output union bound. Output vertices may repeat.
`δ(n) = 12*S(n)*δ₀(n) + outLen(n)*(2⁻¹)^n` is negligible. Zero-length blocks, zero gates,
constant gates, and the one-position and two-position cases are included by the statements.
The output-collision helper has `[Nonempty ρ]`; Yao's pair of bit-vector coin spaces satisfies
it. The prescribed B2 theorem itself has no extra nonemptiness hypothesis.

The checkpoint-1 wrong-key and direct D4 proofs are unchanged. Their detailed rationale and
all original overlap disclosures are retained in `evidence/history/checkpoint1-REPORT.md`.

## Files and sketches

Every delivered source line has at most 100 Python characters, and every file at most 1000
lines. Yao has 970 lines. Its only changes are the permitted target body, its sketch and the
main-results bullet split. The circuit file differs by exactly the nine approved reader lines.
No new simp attribute is added.

| Repository path | Base lines | Checkpoint lines |
|---|---:|---:|
| `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` | 627 | 636 |
| `TCSlib/Cryptography/SecureComputation/Garbling.lean` | 427 | 659 |
| `TCSlib/Cryptography/SecureComputation/Garbling/CoinBlocks.lean` | 0 | 206 |
| `TCSlib/Cryptography/SecureComputation/Garbling/Probability.lean` | 0 | 113 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean` | 87 | 111 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity/CoinMarginals.lean` | 0 | 58 |
| `TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean` | 0 | 210 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean` | 325 | 283 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean` | 157 | 332 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/Pad.lean` | 0 | 56 |
| `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean` | 0 | 222 |
| `TCSlib/Cryptography/SecureComputation/Yao.lean` | 942 | 970 |

The target sketches describe the implemented arguments. The new long helper proofs include
formula docstrings, sketches and step comments where appropriate. Garbling's module title,
results and contents now describe the proved B2 APIs and its two definition-free helpers.

## Gate 27 hand-off

1. Maximizing slice advice and the empty-fit convention: pending B1.
2. Slice post-processor: pending B1; the shared zero-prefix mask identity is already proved.
3. Random-function slice law: D2/D4 provide full uniform pads; B1 will identify its use of
   their windows, without repeating that random-function proof.
4. Triangle/collision bound: inside D4, already consumed by the direct scheme proof.
5. Frozen scheme multi-message theorem: proved directly from D4; its downstream joint
   corollary remains proved through the SG-1 public relabelling readers.
6. B2: complete (`uprob_not_good_le_of_perm`), with both required corollaries proved.

## Overlap and reuse

All checkpoint-1 overlap disclosures remain binding and are included verbatim in the historical
report under `evidence/history/`. In particular, SG-1 replaces exactly six private readers,
the surviving private XOR lemma is unchanged, the scheme theorem consumes D4 directly, and
the inline nested-ciphertext length specialization is disclosed for promotion.

New statement-shape searches are captured in `evidence/reuse/checkpoint2-searches.log`; the
pre-implementation searches are also in chat and the original search log.

- `findSome_eq_some_of_dichotomy` combines Mathlib's `List.findSome?_eq_none_iff` and
  `List.exists_of_findSome?_eq_some`; it does not re-prove either list law.
- Output/argument marginals compose `HardcoreBit.pushesUniform_restrict` (Basic:220),
  `pushesUniform_eval` (250), product maps, and sum/product equivalences. The dependent row
  marginal uses `Equiv.piCurry` (Mathlib Logic/Equiv/Basic:170) and uniform evaluation.
- `wrongKeyBot_nonneg` is the one-position nonnegativity consequence of the published
  `MultiEnc.wrongKeyBot_iff` and `uprob_nonneg`; no probability identity is re-proved.
- The cross-opening bound averages the published wrong-key property with `uprob_prod`,
  `OneWay.uexp_mono` and `OneWay.uexp_const` (OneWayFunctions/Basic:69).
- The two nested finite union bounds use `uprob_exists_le` (Foundations/Probability:137),
  Finset sums and cardinality readers. The inline count specializes `2^arity*(2^arity-1) ≤ 12`
  to arities at most two; this is arithmetic bookkeeping, not a new union-bound proof.
- The old uniform-seed theorem uses `uprob_comp_equiv`, Fubini and constant expectation.
- `assignmentFold_small` packages the existing Yao binary fold's arity-zero/one/two facts.
  No public bound/injection theorem for `assignIdx` existed at the base; the helper is generic
  and definition-free and Yao supplies its own `assignIdx_eq` reader.
- `pushesUniform_bits_of_blocks` specializes uniform restriction to disjoint bit blocks and
  curries the selected table. Nearest relative: the block injection `dla_blockPos` and its
  injectivity proof in `Candidates/Concrete.lean:831–856`; that proof concerns a different
  candidate layout outside the issued order. Standard `finProdFinEquiv` and restriction are
  reused rather than any imported candidate construction.
- `key_row_blocks_injective` is arithmetic for this concrete layout; no probability law is
  repeated. `pushesUniform_key_row_blocks` composes it with the general block restriction and
  standard `sumArrowEquivProdArrow`, curry, `boolArrowEquivProd` and `piCurry` equivalences.
- Output collisions reuse `MultiMsg.uprob_eq_pair` (FromPRF/HybridLemmas:111), which itself
  supplies the Fubini/point-probability proof. The inline marginal merely composes uniform
  projection, evaluation and `pushesUniform_eval_pair` (HardcoreBit/Basic:263).
- The approved `DAGCircuit.isFaninTwo_iff` is an `Iff.rfl` reader of the existing definition.
  It is not an alternate circuit predicate or a re-proof of well-formedness.

Promotion requests: the generic option-complement bound, dependent row-coin marginal,
first-success dichotomy and bit-block restriction can move to shared probability/list layers;
the nested-string length reader can move beside `nestedSpecial`. No such frozen-file move
is made here. The circuit predicate reader was separately approved and is included.

## Scope requests and exceptions

Seyoon approved the exact circuit reader: “Approve the reader addition”. The original request,
patch, answer, and a byte comparison proving that deleting exactly those nine added lines
restores the entire frozen base file are delivered. No other frozen-file edit is used.

Seyoon authorized best judgment on exceptions while asleep and full disclosure, and messages
coordinating the Mac's shared resources. That instruction is preserved verbatim. The stronger
B2 seed law justifies avoiding a separate shift-block conditioning proof while proving all
requested conclusions. This route change is disclosed above.

Complete Rule-10 A/B seals (strict and coe), paired controls, the explicit-unfold scan and the
final 166-module sweep remain deferred to final proof stabilization. They are mandatory final
checks, not waived. The original base bootstrap and pilot seal evidence are retained.

Two own drivers were accidentally queued simultaneously during B2 development. The issued host
wrapper serialized their actual Lean runs; there were no concurrent writers to this olean tree.
Their queue-time source snapshots were too early. The original snapshots and the correction
are retained, and an authoritative serialized rerun passed. Future drivers have a local
nonblocking guard and capture source after acquiring a host slot. Full details and timings
are in `evidence/coordination/source-snapshot-correction.md`.

One own collision proof check was interrupted after increasing memory/time. A bounded diagnostic
localized a missing nonempty marginal hypothesis and an inference hotspot. Explicit finite
marginals fixed it; the final unrestricted proof checks pass in seconds. No other worker's
native process or lock was touched.

Automatic approval review initially rejected the checkpoint-1 combined pull/push based on the
general README rule. The explicit task §4 and host §5 override were then supplied; the same
direct scoped push was approved and succeeded. The exact event is recorded in
`evidence/coordination/checkpoint1-push-review.md`. No permission remained blocked.

## Host resources and evidence

Every own Lean/Lake/check command uses the issued wrapper, tag `sc-garble`, shared default
`~/.lean-slots`, cap three. Own checks are serial. The narrowed cache uses `-k 3`; there is
no lake build, unfiltered cache request or copied package tree. All Python runs use `python3 -I`.
The original Mac preflight, fresh own-package revisions, cache counts and exact issued pack
verification are retained from checkpoint 1. No dependency revision or base branch was advanced.

Authorized peer messages coordinated wrapper use and short dispatcher boundary gaps. Additional
checks queued behind other workers' cache or native jobs. Scoped slot traffic and resource
notes are delivered; another worker's locks or native process were never edited or killed.

Checkpoint checks cover all changed modules/helpers through the development logs, final owned
modules, YaoReal and the facade, all stored constants of every changed/new module, and signatures.
The six targets, B2 and `garbling_good_whp` are standard-only. The remaining B1 admission and
Yao's `yaoHybrid_polyTime`/`yaoHybrid_simulators` retain sorryAx; the Yao end-to-end consumers
still depend on those two outside-unit admissions. Raw base/final consumer axiom logs are included.

Frozen headers cover all 139 base declarations with exactly six expected SG-1 removals and
zero other differences. Both freeze controls detect exactly one violation. The name scan covers
1,275 base files and 29,518 explicit resolved names: 35 additions, two SG-1 replacements,
zero clashes. The full final sweep will additionally check generated descendants. Lint remains
92 FAIL / 101 WARN with identical line sets. Manifests name exactly all delivered paths and
have been verified with shasum. Every raw diagnostic source/log, including failures, is retained.

## New declarations: signatures

The complete Lean-elaborated signatures, including implicit parameters, are authoritative in
`evidence/logs/checkpoint2-check/`; the inventory is also provided as text below.

```lean
BoolCircuit.DAGCircuit.isFaninTwo_iff {n : ℕ} (C : BoolCircuit.DAGCircuit n) :
  C.IsFaninTwo ↔
    (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = BoolCircuit.GateKind.not → g.args.length = 1)) ∧
      ∀ g ∈ C.gates, g.args.length ≤ 2
TCSlib.Cryptography.SecureComputation.good_of_no_crossOpening {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) (hdec : M.DecCorrect)
  (hC : Cc.IsFaninTwo) (s : TCSlib.Cryptography.SecureComputation.GarbleSeed Cc K ρ)
  (hcross :
    ∀ (i : Fin Cc.gates.length) (a a' : Fin Cc.gates[i].args.length → Bool),
      a ≠ a' →
        M.dec (TCSlib.Cryptography.SecureComputation.argKeys Cc s i a')
            (TCSlib.Cryptography.SecureComputation.garbledRow M Cc s i a) =
          none) :
  TCSlib.Cryptography.SecureComputation.Good M Cc s
TCSlib.Cryptography.SecureComputation.wrongKeyBot_nonneg {K C ρ : Type} [Inhabited K]
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) [Fintype K] [Fintype ρ] {δ : ℝ} (hδ : M.WrongKeyBot δ) :
  0 ≤ δ
TCSlib.Cryptography.SecureComputation.uprob_crossOpening_le_of_perm {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
  (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin Cc.gates[i].args.length → Bool)) (i : Fin Cc.gates.length)
  (a a' : Fin Cc.gates[i].args.length → Bool) (hne : a ≠ a') :
  (TCSlib.Cryptography.uprob fun t =>
      (M.dec (TCSlib.Cryptography.SecureComputation.argKeys Cc (t.1, t.2, π) i a')
            (TCSlib.Cryptography.SecureComputation.garbledRow M Cc (t.1, t.2, π) i a)).isSome =
        true) ≤
    δ
TCSlib.Cryptography.SecureComputation.uprob_not_good_le_of_uniform_data {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) {Ω : Type} [Fintype Ω]
  (d : Ω → (Fin Cc.size → Bool → K) × ((i : Fin Cc.gates.length) → (Fin Cc.gates[i].args.length → Bool) → ρ))
  (hd : TCSlib.Cryptography.HardcoreBit.PushesUniform d)
  (π : Ω → (i : Fin Cc.gates.length) → Equiv.Perm (Fin Cc.gates[i].args.length → Bool)) :
  (TCSlib.Cryptography.uprob fun w => ¬TCSlib.Cryptography.SecureComputation.Good M Cc ((d w).1, (d w).2, π w)) ≤
    12 * ↑Cc.gates.length * δ
TCSlib.Cryptography.SecureComputation.uprob_not_good_le_of_perm {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
  (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin Cc.gates[i].args.length → Bool)) :
  (TCSlib.Cryptography.uprob fun t => ¬TCSlib.Cryptography.SecureComputation.Good M Cc (t.1, t.2, π)) ≤
    12 * ↑Cc.gates.length * δ
TCSlib.Cryptography.SecureComputation.GarblingProbability.assignmentFold_small (len : ℕ) (hlen : len ≤ 2) :
  (∀ (a : Fin len → Bool), List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a) < 4) ∧
    Function.Injective fun a => List.foldr (fun b k => b.toNat + 2 * k) 0 (List.ofFn a)
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_bits_of_blocks {I : Type} [Fintype I]
  [DecidableEq I] {B n tail : ℕ} (c : I → Fin B) (hinj : Function.Injective c) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun r i t => (List.ofFn r).getD (↑(c i) * n + ↑t) false
TCSlib.Cryptography.SecureComputation.GarblingProbability.key_row_blocks_injective {S V G : ℕ} (hV : V ≤ S) (hG : G ≤ S)
  {A : Fin G → Type} (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ (i : Fin G) (a : A i), idx i a < 4)
  (hinj : ∀ (i : Fin G), Function.Injective (idx i)) :
  have c :=
    Sum.elim (fun p => p.2.toNat * S + ↑p.1) fun p => 2 * S + (4 * ↑p.1.fst + idx p.1.fst p.1.snd) * 2 + p.2.toNat;
  (∀ (p : Fin V × Bool ⊕ ((i : Fin G) × A i) × Bool), c p < 10 * S) ∧ Function.Injective c
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_key_row_blocks {S V G n : ℕ} (hV : V ≤ S)
  (hG : G ≤ S) {A : Fin G → Type} [(i : Fin G) → Fintype (A i)] [(i : Fin G) → DecidableEq (A i)]
  (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ (i : Fin G) (a : A i), idx i a < 4)
  (hinj : ∀ (i : Fin G), Function.Injective (idx i)) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun r =>
    (fun v b t => (List.ofFn r).getD ((b.toNat * S + ↑v) * n + ↑t) false, fun i a =>
      (fun t => (List.ofFn r).getD (2 * S * n + (4 * ↑i + idx i a) * (2 * n) + ↑t) false, fun t =>
        (List.ofFn r).getD (2 * S * n + (4 * ↑i + idx i a) * (2 * n) + n + ↑t) false))
TCSlib.Cryptography.SecureComputation.GarblingProbability.findSome_eq_some_of_dichotomy {α β : Type} (l : List α)
  (f : α → Option β) (b : β) (hex : ∃ a ∈ l, f a = some b) (hall : ∀ a ∈ l, f a = none ∨ f a = some b) :
  List.findSome? f l = some b
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_output_argKeys {I J K : Type} [Fintype I]
  [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K] (arg : J → I) (hinj : Function.Injective arg)
  (out : I) (hne : ∀ (j : J), arg j ≠ out) (b : Bool) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun ks => (ks out b, fun j => ks (arg j))
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_rowCoin {I : Type} [Fintype I] [DecidableEq I]
  {A : I → Type} [(i : I) → Fintype (A i)] [(i : I) → DecidableEq (A i)] {ρ : Type} [Fintype ρ] (i : I) (a : A i) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun r => r i a
TCSlib.Cryptography.SecureComputation.GarblingProbability.pushesUniform_output_argKeys_row {I J K R ρ : Type}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [Nonempty K] [Fintype R] [Fintype ρ] (arg : J → I)
  (hinj : Function.Injective arg) (out : I) (hne : ∀ (j : J), arg j ≠ out) (b : Bool) (coin : R → ρ)
  (hcoin : TCSlib.Cryptography.HardcoreBit.PushesUniform coin) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun t => (t.1 out b, fun j => t.1 (arg j), coin t.2)
TCSlib.Cryptography.SecureComputation.GarblingCoins.pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
  {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
  TCSlib.Cryptography.HardcoreBit.PushesUniform fun t => (t.1 j b, t.1 j b', if c = true then t.2.2 else t.2.1)
TCSlib.Cryptography.SecureComputation.GarblingCoins.uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
  (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < TCSlib.Cryptography.uprob fun t => X t = none) :
  (TCSlib.Cryptography.uprob fun t => (X t).isSome = true) < ε
TCSlib.Cryptography.SecureComputation.GarblingCoins.length_nestedInner
  {G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool} {E : List Bool → List Bool}
  (hGE : ∀ (n : ℕ) (k r : Fin n → Bool), E (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (G n k r))
  (n : ℕ) (k m r : Fin n → Bool) :
  (TCSlib.Cryptography.SecureComputation.spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)).length =
    TCSlib.Cryptography.SecureComputation.innerLen.eval n
TCSlib.Cryptography.SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds
  (G₁ : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool)
  (G₂ :
    (n : ℕ) →
      (Fin n → Bool) →
        (Fin n → Bool) →
          Fin ((Complexity.PolyExpr.var.add TCSlib.Cryptography.SecureComputation.innerLen).eval n) → Bool)
  (E₁ E₂ : List Bool → List Bool)
  (hGE₁ : ∀ (n : ℕ) (k r : Fin n → Bool), E₁ (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (G₁ n k r))
  (hGE₂ : ∀ (n : ℕ) (k r : Fin n → Bool), E₂ (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (G₂ n k r))
  (n : ℕ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
  (h₁ :
    ∀ (m : Fin n → Bool),
      (TCSlib.Cryptography.uprob fun t =>
          (TCSlib.Cryptography.SecureComputation.spDecStr E₁ n n (List.ofFn t.2.1)
                (TCSlib.Cryptography.SecureComputation.spEncStr E₁ (List.ofFn t.1) (List.ofFn m)
                  (List.ofFn t.2.2))).isSome =
            true) ≤
        ε₁)
  (h₂ :
    ∀ (m : Fin (TCSlib.Cryptography.SecureComputation.innerLen.eval n) → Bool),
      (TCSlib.Cryptography.uprob fun t =>
          (TCSlib.Cryptography.SecureComputation.spDecStr E₂ n (TCSlib.Cryptography.SecureComputation.innerLen.eval n)
                (List.ofFn t.2.1)
                (TCSlib.Cryptography.SecureComputation.spEncStr E₂ (List.ofFn t.1) (List.ofFn m)
                  (List.ofFn t.2.2))).isSome =
            true) ≤
        ε₂) :
  (TCSlib.Cryptography.SecureComputation.nestedSpecial E₁ E₂ n).WrongKeyBot (ε₁ + ε₂)
TCSlib.Cryptography.SecureComputation.uprob_not_good_distinct_le_of_uniform_data {K C ρ : Type} [Inhabited K] {n : ℕ}
  (M : TCSlib.Cryptography.SecureComputation.MultiEnc K C ρ) (Cc : BoolCircuit.DAGCircuit n) [Fintype K] [Fintype ρ]
  [Nonempty ρ] (hdec : M.DecCorrect) {δ : ℝ} (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) {Ω : Type} [Fintype Ω]
  (s : Ω → TCSlib.Cryptography.SecureComputation.GarbleSeed Cc K ρ)
  (hs : TCSlib.Cryptography.HardcoreBit.PushesUniform fun w => ((s w).1, (s w).2.1)) {m : ℕ} (out : Fin m → ℕ)
  (hout : ∀ (j : Fin m), out j < Cc.size) :
  (TCSlib.Cryptography.uprob fun w =>
      ¬(TCSlib.Cryptography.SecureComputation.Good M Cc (s w) ∧
          ∀ (j : Fin m),
            TCSlib.Cryptography.SecureComputation.keyAt Cc (s w) (out j) false ≠
              TCSlib.Cryptography.SecureComputation.keyAt Cc (s w) (out j) true)) ≤
    12 * ↑Cc.gates.length * δ + ↑m * (1 / ↑(Fintype.card K))
TCSlib.Cryptography.SecureComputation.specialScheme_gen_runAt
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (rg : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.Coins n) :
  (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.runAt n [] rg = List.ofFn rg
TCSlib.Cryptography.SecureComputation.specialScheme_enc_runAt
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (k m : List Bool) (re : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.Coins n) :
  (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.runAt n (Turing.pairEncode k m) re =
    TCSlib.Cryptography.SecureComputation.spEncStr E k m (List.ofFn re)
TCSlib.Cryptography.SecureComputation.specialScheme_dec_runAt
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (k c : List Bool) (rd : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).dec.Coins n) :
  (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).dec.runAt n (Turing.pairEncode k c) rd =
    (TCSlib.Cryptography.SecureComputation.spDecStr E n n k c).getD (true :: List.replicate n true)
TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.Coins n ≃ (Fin n → Bool)
TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv_eq
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) :
  TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv G E hE hGE n =
    (Complexity.NUPPT.coinsCongr ⋯ n).trans
      ((Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform Complexity.polyTimeComputable_pairSndD Complexity.PolyExpr.var
            n).trans
        ((finCongr ⋯).arrowCongr (Equiv.refl Bool)))
TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv_ofFn
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (rg : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).gen.Coins n) :
  List.ofFn ((TCSlib.Cryptography.SecureComputation.specialScheme_keyCoinsEquiv G E hE hGE n) rg) = List.ofFn rg
TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.Coins n ≃ (Fin n → Bool)
TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv_eq
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) :
  TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv G E hE hGE n =
    (Complexity.NUPPT.coinsCongr ⋯ n).trans
      ((Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform ⋯ Complexity.PolyExpr.var n).trans
        ((finCongr ⋯).arrowCongr (Equiv.refl Bool)))
TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv_ofFn
  (G : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin (n + n) → Bool) (E : List Bool → List Bool)
  (hE : Complexity.PolyTimeComputable E)
  (hGE : ∀ (n : ℕ) (s x : Fin n → Bool), E (Turing.pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (G n s x))
  (n : ℕ) (re : (TCSlib.Cryptography.SecureComputation.specialScheme G E hE hGE).enc.Coins n) :
  List.ofFn ((TCSlib.Cryptography.SecureComputation.specialScheme_nonceCoinsEquiv G E hE hGE n) re) = List.ofFn re
TCSlib.Cryptography.SecureComputation.spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
  (hp : r.length + m.length ≤ (E (Turing.pairEncode k r)).length) :
  TCSlib.Cryptography.SecureComputation.spEncStr E k m r =
    Turing.pairEncode r (List.zipWith xor (List.replicate r.length false ++ m) (E (Turing.pairEncode k r)))
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest (E : List Bool → List Bool) (z : List Bool) : List Bool
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest_eq (E : List Bool → List Bool) (z : List Bool) :
  TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest E z =
    [decide
        (List.take (Complexity.NUPPT.inParam z).length (Complexity.pairSndD (Complexity.NUPPT.inArg z)) =
          List.take (Complexity.NUPPT.inParam z).length
            (E (Turing.pairEncode (Complexity.NUPPT.inCoins z) (Complexity.pairFstD (Complexity.NUPPT.inArg z)))))]
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.polyTimeComputable_prefixTest {E : List Bool → List Bool}
  (hE : Complexity.PolyTimeComputable E) :
  Complexity.PolyTimeComputable (TCSlib.Cryptography.SecureComputation.SpecialWrongKey.prefixTest E)
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.uprob_random_prefix {n L : ℕ} (h : n ≤ L) (r v : Fin n → Bool) :
  (TCSlib.Cryptography.uprob fun R => List.take n (List.ofFn (R r)) = List.ofFn v) = 2⁻¹ ^ n
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision (ℓ : Complexity.PolyExpr)
  (F : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Fin ((Complexity.PolyExpr.var.add ℓ).eval n) → Bool)
  (E : List Bool → List Bool) (hE : Complexity.PolyTimeComputable E)
  (hFE : ∀ (n : ℕ) (k r : Fin n → Bool), E (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F n k r))
  (hF :
    (TCSlib.Cryptography.OracleEnsemble.keyed F).Indist
      (TCSlib.Cryptography.OracleEnsemble.random Complexity.PolyExpr.var (Complexity.PolyExpr.var.add ℓ))) :
  ∃ ε,
    TCSlib.Cryptography.Negligible ε ∧
      ∀ (n : ℕ),
        (TCSlib.Cryptography.uprob fun t =>
            List.take n (List.ofFn (F n t.1 t.2.2)) = List.take n (List.ofFn (F n t.2.1 t.2.2))) ≤
          ε n
TCSlib.Cryptography.SecureComputation.SpecialWrongKey.spDecStr_none_iff_prefix_ne {n l : ℕ}
  (F : (Fin n → Bool) → (Fin n → Bool) → Fin (n + l) → Bool) (E : List Bool → List Bool)
  (hFE : ∀ (k r : Fin n → Bool), E (Turing.pairEncode (List.ofFn k) (List.ofFn r)) = List.ofFn (F k r))
  (k k' r : Fin n → Bool) (m : Fin l → Bool) :
  TCSlib.Cryptography.SecureComputation.spDecStr E n l (List.ofFn k')
        (TCSlib.Cryptography.SecureComputation.spEncStr E (List.ofFn k) (List.ofFn m) (List.ofFn r)) =
      none ↔
    List.take n (List.ofFn (F k r)) ≠ List.take n (List.ofFn (F k' r))
```
