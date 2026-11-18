# EF-H11 · Secret sharing and BGW with efficiency

**Unit** `ef-h11-sharing-bgw` · **Route** Claude fill (lead, up to 2 sub-agents on disjoint files) ·
**Base** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (needs `CoinSampling` for the dealer's coins) ·
**Size** 1,800–3,500 new Lean lines (±40%): Shamir 600–1,000, BGW 1,200–2,500 ·
**Rulings** Q7 **B** ("Retrofit secret sharing and BGW now (EF-H11), not exempt"), Q11 A (file-disjoint from
Stage 2, so it starts now), rule 15.

Read `../COMMON.md` first; it is part of this brief.

## Scope

`SecretSharing.Scheme` (`SecretSharing/Defs.lean:86`), Shamir's `scheme` (`SecretSharing/Shamir.lean:101`),
`BGW.Resharer` (`MPC/BGW/Protocol.lean:67`) and `bgwEval` (`:101`) carry no efficiency (audit N15, N16;
`Defs.lean:82–84`: "efficiency is not modelled here, since the security notions are information-theoretic").
Ruling Q7 B retrofits them now. The existing files stay frozen (they are correct and their perfect-security
theorems are reused). This job adds, beside them:

1. **An efficient secret-sharing interface** (rule 15: efficiency in the definition). Over an abstract field
   `F` with **all** of `F \ {0}` as parties, the existing `Scheme` has exponentially many shares, so the
   efficient form is parametric: public parameters `π` (a prime `p`, a threshold `k`, a party count `n` with
   `k ≤ n < p`, written as a parameter word) and parties `1, …, n`. Its fields: the share map of **one**
   party `⟨π, sec, coins, i⟩ ↦ share`, polynomial-time; reconstruction from a **listed** set of parties and
   their shares, polynomial-time; the dealer's coins drawn in the `CoinSampling.SamplesEfficiently` form
   (failure at most `2^{-κ}`, exact law on success); and the link to the abstract `Scheme` (the typed maps
   are the existing ones, restricted to the listed parties).
2. **Shamir over `ZMod p`** as an instance, with correctness and perfect privacy **transferred** from the
   existing `Shamir.correct` and `Shamir.perfectPrivacy` (restricted to parties `1..n`), not re-proved.
3. **BGW efficiency**: an efficient `Resharer` (Shamir resharing with explicit coins, its coins drawn as in
   1), and polynomial-time per-party local steps for every gate kind (input, constant, addition, scalar
   multiplication, multiplication followed by `degreeReduce` on the received re-sharings), with their
   agreement with `bgwEval`'s clauses. The **whole-circuit evaluator** (party `j`'s output share from an
   encoded `Circuit F ι`) is in scope only on a registered host (Q-H11-1).

## Targets (proposed; the worker may refine with disclosure)

Namespaces follow the existing files: `TCSlib.SecretSharing`, `TCSlib.Shamir`, `TCSlib.MPC.BGW`.

**File A** `SecretSharing/Efficient.lean`:
- `structure ShamirParams` (or a general `Pub` type in the interface): `p k n : ℕ`, `p.Prime`,
  `0 < k ≤ n < p`; `ShamirParams.encode` (a parameter word: `p` as a numeral, `k`, `n` in unary or
  binary; disclose) with readers.
- `structure EfficientScheme` (name may change): the typed maps, the encodings, and the fields
  `share_poly : ∃ f, PolyTimeComputable f ∧ ∀ π sec r i, f ⟨encPub π, ⟨encSecret sec, ⟨encRand r, encParty i⟩⟩⟩ = encShare (share π sec r i)`,
  `reconstruct_poly` (on the listed shares of a set `A`), `dealer_efficient : CoinSampling.SamplesEfficiently …`;
  and the predicates `EfficientScheme.Correct`, `EfficientScheme.PerfectPrivacy` defined **through** the
  existing `Scheme.Correct`/`Scheme.PerfectPrivacy` on the restricted scheme (no second definition of
  either notion).

**File B** `SecretSharing/ShamirEfficient.lean`:
- `def shamirEfficient : EfficientScheme` over `ZMod p`, with `shamirEfficient_correct`,
  `shamirEfficient_perfectPrivacy` from `Shamir.correct`, `Shamir.localReconstruct`, `Shamir.perfectPrivacy`
  (and `Scheme.PerfectPrivacy.card_view_eq` if a counting form is stated).
- The coefficient draw: `k − 1` residues mod `p`. `CoinSampling` has no product of draws
  (`Contract.lean`, "Products of draws"); acceptable routes: one bucket draw over `Fin (p^{k−1})` decoded
  to base-`p` digits by a polynomial-time core (`bucketSampler`, `CoreComputable.map`), or a product
  sampler built on `CoinSampler.pi` with a polynomial-time coin splitter, stated publicly. Disclose the
  route; no private sampler.
- Polynomial evaluation and Lagrange recombination mod `p` on `BinArith` (`mul`, `add`, `mod`; inverses per
  Q-H11-2), with the registered loops.

**File C** `MPC/BGW/Efficient.lean`:
- `def shamirResharer (π) (coins) : Resharer (ZMod p) d` (or the resharer with explicit coins and a
  polynomial-time share map) and `theorem polyTimeComputable_reshare…`.
- Per-gate local step maps and their agreement lemmas with `bgwEval_input`, `bgwEval_const`,
  `bgwEval_add`, `bgwEval_smul`, `bgwEval_mul` and `degreeReduce` (`Protocol.lean:77`), each
  `PolyTimeComputable`.
- Under Q-H11-1 A, and only if a registered host fits: the whole-circuit evaluator with
  `polyTimeComputable_…` and its agreement with `bgwEval`. Otherwise report the host contract you need
  (**E-SCOPE**) and stop that line.

## Sources

The existing files cite, and this job cites exactly as they do (none of these is ingested under
`blueprint/src/references/`; add no excerpt and no new anchor):
- [Sha79] A. Shamir, *How to share a secret*, CACM 22(11), 1979, §2–3; [Bei11] A. Beimel, *Secret-sharing
  schemes: a survey*, IWCC 2011, §1, §2.1;
- [PS10] §6.1.2–§6.1.3 (Definition 152.1: `Share` and `Recon` probabilistic polynomial-time; Lemma 153.2,
  Fact 153.3, Protocol 154.4, Proposition 154.5);
- [BGW88] Ben-Or, Goldwasser, Wigderson, STOC 1988, §3; [AL17] Asharov, Lindell, J. Cryptology 30(1), 2017,
  §3–4.
[PS10, Definition 152.1]'s efficiency clause is the requirement this job formalizes: say so in the
docstrings (it was the recorded deviation at `Defs.lean:82–84`).

## Must reuse

- `Scheme`, `Scheme.Correct`, `LocalReconstruct`, `PerfectPrivacy`, `PerfectPrivacy.card_view_eq`;
  `Shamir.poly`, `poly_eval`, `scheme`, `scheme_share`, `correct`, `localReconstruct`, `perfectPrivacy`,
  `natCard_coins_view`; `vecScheme` and its theorems (`SecretSharing/Vector.lean`) if vector secrets are
  used; `IsSharing`, `isSharing_share`, `recombineCoeff`, `recombine`, `recombine_eq_reconstruct`
  (`SecretSharing/Sharing.lean`); `Resharer`, `degreeReduce`, `isSharing_degreeReduce`, `bgwEval` and its
  equations, `bgwEval_isSharing`, `bgwEval_recombine`, `Circuit`, `Circuit.eval`.
- `CoinSampling`: `SamplesEfficiently` and readers, `bucketSampler`, `samplesEfficiently_residue`,
  `CoreComputable.map`/`pair`, `CoinSampler.pi`, `fail_pi_le`.
- `BinArith` (`add`, `mul`, `mod`, `powMod`, `lt`/`le`/`beq`), `polyTimeComputable_iterate`, `forLoop`,
  `getW` and the `Words` loops; `Encoding.BinaryArith` adapters; `NUPPT.ofPolyTimeUniform` for any honest
  machine.

## Duplication sweep (maintainer, static)

- No efficiency statement exists for any secret-sharing or MPC object (`grep PolyTimeComputable` in
  `SecretSharing/` and `MPC/`: 0 hits).
- Modular polynomial evaluation / Lagrange interpolation machines: none in TCSlib. `BinaryArith/DetMod`
  (determinant over `ZMod p`, Gaussian elimination) already takes Fermat inverses `x^{p−2} mod p` inline
  through `powMod` and `sub` (`DetMod.lean:197`, `:275`, `:300`), with no public inverse map: that is the
  precedent for Q-H11-2 A. Compose `powMod` the same way; if you state a public `invModPrime` map, say it
  is the first public one and cite `DetMod` as the inline relative.
- Modular inverse: EF-H1 is proving `Candidates.xgcdStr` polynomial-time **in parallel** (general modulus);
  do not prove `xgcdStr`'s efficiency here (Q-H11-2).
- Product samplers: none public (`Contract.lean`, "Products of draws"); `CoinSampler.pi`
  (`CoinSampling/Basic.lean:322`) is the coin-level product.
- Name check: `EfficientScheme`, `ShamirParams`, `shamirEfficient`, `shamirResharer`: unused on all 280
  remote heads.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/SecretSharing/Efficient.lean` | new |
| `TCSlib/Cryptography/SecretSharing/ShamirEfficient.lean` | new |
| `TCSlib/Cryptography/MPC/BGW/Efficient.lean` | new |
| `TCSlib/Cryptography/SecretSharing.lean` | facade: two imports and `## Contents` entries |
| `TCSlib/Cryptography/MPC/BGW.lean` | facade: one import and its `## Contents` entry |

**Disjointness check (maintainer, mechanical).** None of the five paths is an owner file of
`scope.tsv`/`s2a-items.tsv`, changed on `cleanup/stage2-s2a`, touched by #376/#377, or under any
Arora–Barak/Ladner branch. No Stage 2 row touches `SecretSharing/` or `MPC/` (audit §5.2).

**Lint note.** `SecretSharing/` (9 FAIL / 3 WARN) and `MPC/` (10 FAIL / 3 WARN) carry pre-existing lint
lines at both bases; the new files must add none (C8).

## Checks and evidence (in addition to COMMON C1–C13)

- **H11-P1**: `shamirEfficient` at `p = 7`, `k = 2`, `n = 3`: `#eval` shares and reconstruction from every
  2-set, against `Shamir.scheme` on `ZMod 7`.
- **H11-P2**: a BGW multiplication gate at `p = 7`, `d = 1`, three parties: the local step and
  `degreeReduce` against `bgwEval_mul`.
- **H11-P3**: `#print axioms` of the instance and its correctness/privacy theorems: standard only.
- `REPORT.md` records whether the whole-circuit evaluator was built, and on which host; or the host
  contract requested.

## Size

Interface 200–350; Shamir instance with sampler and Lagrange machines 400–650; BGW resharer and gate steps
600–1,200; whole-circuit evaluator 600–1,300 (only on a registered host).

## Questions for Seyoon

**Q-H11-1. BGW scope in this job.**
- **A (recommended).** Shamir, the efficient resharer and every gate step now; the whole-circuit
  evaluator only on a registered host, else an escalation with the host contract (a host is a statement
  item of its own, policy §1).
- **B.** Shamir only now; BGW in wave 2.

**Q-H11-2. Modular inverses for Lagrange recombination.**
- **A (recommended).** Fermat, `x^{p−2} mod p` with `BinArith.powMod`: exact here, because `p` is prime by
  the public parameters' validity; disclosed as a near-relative of EF-H1's general `xgcdStr`.
- **B.** Wait for EF-H1 to land and use `Candidates.xgcdStr` (reconstruction becomes a later series).
