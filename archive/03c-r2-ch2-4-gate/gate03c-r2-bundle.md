## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03c-pack-r2.md =====

# Gate 03c ([PS10] ch. 2–4, hard-core bits and PRGs), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 1 major (#1), 5 minors and 5 notes**; after the review, 2 majors (#3 raised) (`gate03c-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03c repair commit (G3-2: the expansion cost declared; G3-7 (b): Thm 75.4 without `0 < ℓ(n)`; minors and notes 4–11; the collection section split off into `HardCoreCollection.lean`), merged in #201; G3-7 (c) (`glPad`'s `henc` cost) is #198's. The full delta is `evidence-r2/03c/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03c-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03c-review.md` (in the bundle).
- **The deliverable:** **`gate03c-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03c-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03c/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** **Thm 75.4** (`Ensemble.NextBitUnpredictable.pseudorandom`) no longer takes `hℓ : ∀ n, 0 < ℓ.eval n` (strengthened to the source's statement). `PRG` declares a second Deviation (expansion at every `n`, `n = 0` included).
- **New public declarations:**
- `prgAdv_eq_zero_of_length_eq_zero` (`NextBit.lean`: no advantage on `{0,1}^0`);
- the reading lemmas `PRG.easy_iff` (`Pseudorandom.lean`), `hardCore_iff`, `PRG.oneBit_stretch`,
  `PRG.oneBit_G`, `owpPredictorSnoc_eq`, `oneBitStep_eq`, `expandRed_eq` (`HardCore.lean`),
  `Collection.glBit_eq` (`HardCoreCollection.lean`);
- `HardCoreCollection.lean`: 17 declarations moved unchanged from `HardCore.lean` (names and
  statements as before; `HardCore.lean` imports it).


## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03c-findings.md`, `review/gate03c-review.md`, `resolutions-03c-r1.md`, `evidence-r2/03c/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/Asymptotic/{Pseudorandom, NextBit, HardCore, HardCoreClaims, HardCoreCollection}.lean` |
| Context | `03c-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/c2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/c2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 95 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   18 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 76 prints of every public theorem and lemma in this pack's files:
   76 use only the standard axioms, and 0 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes (`evidence-repairs/03ac/replay.log`); each line of `replay.log` is the
newest check of its module, and the Lean files at the pin equal #201's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03c-findings.md =====

# Gate 03c findings: [PS10] ch. 2–4, hard-core bits and PRGs (external statement audit)

**Audited:** `TCSlib/Cryptography/Asymptotic/{Pseudorandom, NextBit, HardCore, HardCoreClaims}.lean` at
`a3c5fa8b72e50939822f22364647dc844a3914a0`, as reproduced in `gate03c-bundle.md`. I followed the brief of
pack 03c, which imports pack 03a's brief and severity guide.

**Verdict:** **the pack does not close.** It has **0 blockers, 1 major, 5 minors and 5 notes**. The major
finding (#1) is that the `PRG` interface cannot express a length-doubling generator. It becomes a blocker
if a downstream statement already relies on such a generator (see the fix column).

**Source caveat.** The request names `Pass–Shelat.pdf` as attached, but only the bundle was uploaded, and
this session's network policy blocks downloading the PDF. I made the source-fidelity checks against the
bundle's chapter-3 inventory, which quotes [PS10] item by item, and against my own reading of the
3rd edition. Two points (marked *PDF check*) need confirmation from the page itself.

---

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `Pseudorandom.lean` · `PRG.expands`; `HardCore.lean` · `PRG.expand`, `prg_expand` (hypothesis `hℓ`) | Expansion is required at **every** `n`, including `n = 0` (`∀ n, n < stretch.eval n`, and the same `hℓ` in `PRG.expand`/`prg_expand`). Because the stretch is a polynomial, this forces `stretch(0) ≥ 1` (and `ℓ(1) ≥ 2` for `prg_expand`). As a result, **no generator with stretch `2n`, `3n`, `n²` or `n^c` can be a `PRG`**, and `prg_expand` cannot target such an `ℓ`. The text's own length-doubling PRGs cannot be expressed: Alg 92.1's `G : {0,1}^n → {0,1}^{2n}`, and Thm 97.3 with Cor-97.a's "WLOG `g` is length-doubling". Lemma 80.5 is stated "for any polynomial ℓ" (*PDF check*). Neither the PRG Deviation notes nor DESIGN §5 record this cost. | **Length-doubling stretch.** `stretch := .mul (.const 2) .var` needs `expands 0 : 0 < 0`, which is false. A polynomial with `p(n) = 2n` for all `n ≥ 1` equals `2n`, so `p(0) = 0`; no `PolyExpr` stretch is length-doubling. **Square stretch.** `ℓ := .pow .var 2` fails `hℓ 1 : 1 < 1`. **The planners expected 2n.** Inventory §4.4 requires "`n < ℓ n`" and in the same bullet plans "GGM … use `2n`; Alg 92.1 uses key `n`, message `2n`". **The source's letter.** The literal "\|G(x)\| > \|x\|" fails the same way at `x = ε`, but the text's usage (Lem 80.5, Thm 97.3) shows `n = 0` is not intended. **Risk.** Any downstream statement over `P : PRG` with `P.stretch = 2n` (or `P.stretch.eval n = 2 * n`) is **vacuously true**. | Require expansion only for `n ≥ 1` (`expands : ∀ n, 0 < n → n < stretch.eval n`), or only eventually (`∃ n₀, ∀ n ≥ n₀, …`), which also admits `n²`. Make the same change to `PRG.expand`/`prg_expand`'s `hℓ` and to `PRG.stretch_pos`, and record it in DESIGN §5. Before closing, search every consumer of `PRG` (`Encryption.lean` Alg 92.1/Thm 92.2, `PRF.lean` Cor-97.a/Thm 97.3, ch. 5–8) for stretch hypotheses that are now unsatisfiable. **Escalate to blocker if one exists.** |
| 2 | minor | `NextBit.lean` · `Ensemble.NextBitUnpredictable.pseudorandom`; `Pseudorandom.lean` · `PRG.stretch_pos` (docstring) | Thm 75.4 carries an extra hypothesis `hℓ : ∀ n, 0 < ℓ.eval n` that the source does not have. The docstring mentions it ("with ℓ(n) > 0") but does not mark it as a Deviation (policy §2). It excludes every ensemble with `ℓ(0) = 0`, such as `ℓ = n`, `2n` or `n²`, so completeness cannot be applied to an ensemble over `{0,1}^n`. The docstring of `stretch_pos` calls `0 < ℓ(n)` "the hypothesis … of [PS10, Theorem 75.4]"; the source has no such hypothesis. | The hypothesis can be removed. At any `n` with `ℓ(n) = 0`, both `X_n` and `U_0` are the point mass on the empty string, so `prgAdv = 0` for every `D`. The proof only uses the `n` in the infinite set where `1/p(n) ≤ prgAdv`, and `ℓ(n) > 0` there. The theorem is therefore true but weaker than the source. | Drop `hℓ`. At `n` with `ℓ(n) = 0` there is no position and `prgAdv = 0`, so choose `i_n` only where `ℓ(n) > 0`. That requires stating the identity of `exists_nextBitPredMachine` for every position `i : Fin (ℓ.eval n)` instead of a chosen `i : ∀ n, Fin (ℓ.eval n)`, which cannot exist when `ℓ(n) = 0`; the machine already reads the position off the prefix length. Otherwise keep `hℓ` and add a Deviation line. Fix the attribution in `stretch_pos`. |
| 3 | minor | `HardCore.lean` · `Collection.glPad` (`henc`), `Collection.OneWay.glPad(_hardCore)`, `goldreich_levin_coll`, `TrapdoorCollection.OneWay.glPad_hardCore` (docstring) | The Deviation says `henc : ∀ n r x, \|encD_{index n r} x\| = m(n)` is what "the text's `\|x\| = \|r\|` presupposes". It is stronger than that: for **every** coin string, it ties the encoding length at each generated index to the parameter `n`. The TDP docstring also claims that Thm 104.4's hypothesis is "satisfiable from trapdoor permutations alone"; that holds only for TDPs that satisfy `henc`. | Suppose the generator emits one index `i₀` at two parameters `a ≠ b`, on any coin strings. Then `henc` forces `m(a) = m(b)`. An ℕ-coefficient polynomial that takes the same value at two points is constant, so every generated index must have one fixed encoding length forever. The theorems are then vacuous for any collection whose encodings grow with `n`. Example: `expCollection` outputs the fixed `dlDefaultIndex` at every `n < n₀` (DESIGN §5.18), so this applies whenever `n₀ ≥ 2`. The text's `\|r\| = \|x\|` only needs encodings of fixed length at each index. | Weaken to regularity at each index: `∀ i x, \|encD_i x\| = \|encD_i default\|` and `\|encD_{index n r} default\| ≤ m(n)`. The sampler then reads `L_i` off the length of the sampled element's encoding and keeps `L_i` of its `m(n)` padding coins. Otherwise, state the cost in the Deviation, in DESIGN §5.18 and in the TDP docstring. Either way, confirm that the RSA/Rabin trapdoor instances meant for Thm 104.4 discharge `henc`. |
| 4 | minor | `HardCore.lean` · `prg_expand` (signature); DESIGN §2.12 | The frozen shape is `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (… stretch ℓ).Secure`. The code instead takes a raw one-bit-stretch `G` with `(PRG.oneBit G).Secure`. That is faithful to Lem 80.5, but it departs from the frozen record without a §5 entry. A consumer holding a general `P : PRG` with stretch `> n + 1` (ch. 5–8 cite `PRG`, `PRG.Secure`, `prg_expand`) must first truncate to `n + 1` bits, and no truncation lemma is in this pack. | `theorem prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ) (hℓ) (h : (PRG.oneBit G).Secure)` versus DESIGN §2.12. The inventory places the truncation step (Cor-97.a) in `PRF.lean`, outside this pack. | Add `PRG.truncSucc` (the first `n + 1` output bits) with `PRG.Secure.truncSucc` (post-processing by a projection, via `distAdv_comp`/`Indist.push`), plus a `PRG`-level corollary of `prg_expand`. Update DESIGN §2.12, or record the signature change. |
| 5 | minor | `NextBit.lean` · `nextBitProb_nextBitPred_false` (proof sketch); docstring of `uprob_split_bit` ("run-3 audit P2-3") | The sketch says the proof uses "the bijection `(b, (s, u), c) ↦ (s, (update u i (xor b (X s i)), c))`". That map is 2-to-1, which is exactly the error that `uprob_split_bit`'s docstring says was repaired. The proof in fact rewrites with `uprob_split_bit`, so the sketch describes a proof the code does not perform (policy §3, Synchronization). The repair id "P2-3" also does not appear in `run3-audit-summary.md`, which lists only P2-1 and P2-2. | The domain `Bool × σ × {0,1}^ℓ × ρ` is twice the size of the codomain `σ × {0,1}^ℓ × ρ`, because the original `u_i` is lost. The code reads `rw [uprob_split_bit i (fun s => X s i) …]`. The mathematics is fine: the involution `ψ` of `uprob_split_bit` is a genuine bijection (`ψ ∘ ψ = id`). | Rewrite the sketch around `uprob_split_bit` and its involution. Record P2-3 in the run-3 summary or the decision log, and correct inventory Thm-75.4.2, which has the same "bijection". |
| 6 | minor | `evidence/c/axioms.log`: no prints for `HardCoreClaims.lean` (all 8 declarations), `not_hardCore_const`, `Ensemble.uniform_nextBitUnpredictable`, `PermCollection.OneWay.glPad_hardCore` | The axiom evidence covers 22 declarations and none of `HardCoreClaims.lean`, the file question 6 asks about. It also omits this pack's two non-vacuity theorems, which DESIGN §4 requires to be printed in `Checks.lean`. Nothing in the evidence shows these declarations are free of `sorryAx`, and the closure contains 22 sorried declarations. | The `axioms.log` names do not include `fact_88_4`, `thm_87_3_*`, `not_hardCore_const` or `uniform_nextBitUnpredictable`. `replay.log` shows sorries in `Build/Loop` (5), `Build/RecordTable` (4), `Build/Primitives` (3), `Composition` (3) and others. | Append `#print axioms` lines for these declarations to `audits/pass-shelat/Checks.lean` and re-attest. |
| 7 | note | `HardCoreClaims.lean` · module docstring, `thm_87_3_6`, `thm_87_3_8` | The module docstring says each claim is "the family-level instance (`FunFamily.glPad`, …)". In fact `fact_88_4` and `thm_87_3_6/7/8` are stated at the concrete level, for an arbitrary `f : (Fin n → Bool) → β`. `thm_87_3_6` quotes the text's bound as `1/(mε'²)`; the inventory row quotes `1/(4mε'²)`, which with `ε' = ε/2` is exactly the formal `1/(ε²m)` (*PDF check*). It also takes `m = 2^k − 1`, while `thm_87_3_8` takes `m = 2^k`. | Signatures of the four declarations; inventory row Thm-87.3.6. | Docstring edits only. |
| 8 | note | `Collections.lean` (03b) · `Collection.HardCore` (inventory Def-78.3.coll) | Def-78.3.coll is in this pack's inventory scope, but it is defined in `Collections.lean`, and DESIGN §2.10 elides its body ("`…`"). I could not audit it. The hard-core half of `goldreich_levin_coll` and of the trapdoor corollaries is only as good as this definition. | Bundle line for DESIGN §2.10: `def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …`. | Confirm that pack 03b audited Def-78.3.coll, or add its body to this bundle. |
| 9 | note | `HardCore.lean` · `goldreich_levin`, the "(OWP)" route → `HardCorePermutation.lean` (pack 03i) | The route from "OWPs exist" to "PRGs exist" (Thm 87.3's OWP clause as a `PermFamily`, then `owp_hardcore_prg` and `cor_81_7`) goes through `OneWayPermutation.glHalf`. That module is not in this pack's closure. Run 3 recorded it, `exists_owp_hardCore` and `exists_securePRG_of_owp` as depending on `sorryAx`, and this pack's evidence cannot show their status at `a3c5fa8b`. Any ch. 5–8 consumer of `PRG.Secure` that starts from a OWP depends on them. | `replay.log` has no `HardCorePermutation` line. `run3-audit-summary.md` §4 lists the new `sorryAx` prints. | Pack 03i should confirm with axiom prints. |
| 10 | note | Inventory rows Claim-67.a, Constr-77.a, Claim-78.a, Claim-78.b, Claim-79.a, Claim-107.c, Constr-82.a | None of these is formalized. That is consistent with DESIGN §6.2 (optional or deferred). However, the inventory's instruction to record Shamir's generator and Claims 78.a/78.b "as remarks in `HardCore.lean`'s module docstring if not formalized" was not followed. Claim-107.c (a PRG is a OWF) is cheap and would document what `PRG.Secure` buys. | `HardCore.lean`'s module docstring does not mention Shamir, 78.a or 78.b. | Add the remarks. Consider formalizing Claim-107.c. |
| 11 | note | Policy hygiene | `PRG.ensemble_X` carries `@[simp]`, which policy §1 allows only with gate approval. The predicates `PRG.Easy` and `HardCore` have no `_iff` lemma (only the projections `.easy` and `.hard`). `oneBitStep`, `expandRed`, `PRG.oneBit`, `owpPredictorSnoc` and `Collection.glBit` have no equation lemma. `NextBit.lean` (about 915 lines) and `HardCore.lean` (about 982 lines) exceed the 600-line target and are near the 1000-line cap. | Bundle line 3570, and the file extents in the bundle. | Remove `@[simp]` or record approval; add the lemmas; split the two files. |

---

## Answers to the specific questions

**1. Pseudorandomness and PRGs (Defs 74.1, 77.1).**
- **Is `PRG.Secure` the right notion?** Yes. `PRG.Secure P` holds when `P.Easy` holds and, for every `D : NUPPT`, the function `n ↦ |Pr[D(1^n, G(U_n)) = 1] − Pr[D(1^n, U_{ℓ(n)}) = 1]|` is negligible. The condition `ℓ(n) > n` is the structure field `expands`.
- **Does giving `1^n` to `D` matter?** No. It is the declared D5 deviation, and for a PRG it changes nothing. Every PRG stretch is a non-constant polynomial with coefficients in ℕ, since `n < ℓ(n)` for all `n`. Such a polynomial is strictly increasing, hence injective, so `Indist` and `IndistLit` coincide here (`Ensemble.IndistLit.toIndist`, pack 03a).
- **Are the length conditions for every `n` or only eventually, and does it matter?** They are stated for every `n`, and it matters: see finding #1. The same literal reading of `n = 0` also produces finding #2.

**2. Next-bit unpredictability (Def 75.2, Thm 75.4).**
- **Is the position `i` handled as in the source?** Yes. As in the text, `i` is universally quantified and not chosen by the predictor (`∀ A ∃ ε ∀ n ∀ i < ℓ(n)`), and the predictor learns `i` from the prefix length. In the completeness proof the reduction picks `i_n` non-uniformly, for each `n`, as the text does. The machine reads the position off `|t|`, and only the sign is hard-wired into the advice. So the per-`n` choice is the source's, and no advice is spent on `i`.
- **Are both directions stated, and at what loss?** Both are stated.
  - **Completeness:** `NextBitUnpredictable.pseudorandom`. Concretely, `exists_nextBitPred` gives predictor success `≥ 1/2 + ε/ℓ`, the text's `1/(p(n)ℓ(n))` loss. It carries the removable extra hypothesis of finding #2.
  - **Soundness:** `Pseudorandom.nextBitUnpredictable`, with the exact identity `prgAdv (nextBitDist i A) = |nextBitProb − 1/2|`, so there is no loss.

**3. Expansion (Lem 80.5, Cor 81.7, `prg_expand`).**
- **Composition: right.** `PRG.expand_G` (by `rfl`) gives output bit `i = last(G(X_i))` with `X_{i+1} = init(G(X_i))`. That is the text's `X_{i+1} ‖ b_{i+1} ← G(X_i)`, seed first and bit last, with the final seed dropped. `iterPRG_eq_expand` checks Cor 81.7's closed form `h(f^i(x))` against it.
- **Loss: right.** Concretely it is `ε/ℓ(n)` (`exists_expandRed_ge`), and asymptotically the factor is absorbed by `Negligible.polyExpr_mul`.
- **"Any polynomial stretch": no.** Only stretches with `ℓ(n) > n` at every `n` are allowed (finding #1). The input must also be exactly a one-bit-stretch `G`, with no route from a general `PRG` (finding #4).

**4. Hard-core predicates (Def 78.3, Thm 79.4).**
- **Is "hard-core" stated as the source states it?** Yes. For every `A : NUPPT`, there is a negligible `ε` with `Pr[x ← U_{inLen n} : A(1^n, f_n(x)) = h_n(x)] ≤ 1/2 + ε(n)` for all `n`, plus a deterministic poly-time evaluator for `h` on `⟨1^n, x⟩`. The text's `k`/`n` mix-up is resolved as `k = n`, which is declared.
- **Collection form:** see note #8.
- **Does Thm 79.4 use the permutation property where it needs it?** Yes. Bijectivity is used exactly once, in `exists_owpPredictorSnoc`, to identify `f(U_n) ‖ σ` with `U_{n+1}`, and it is built into `PermFamily` (`≃`). Of `hP : OneWayPermutation P`, `owp_hardcore_prg` uses only `hP.easy`. The hardness clause is redundant, since an efficiently computable permutation with a hard-core predicate is automatically one-way. The hypothesis is still the source's, so no change is needed.

**5. Goldreich–Levin (Thm 87.3 and the collection form).**
- **Single function: yes, at the source's strength.** `goldreich_levin` concludes `𝓕.glPad.StrongOneWay ∧ HardCore 𝓕.glPad 𝓕.glBit` for every strong one-way `FunFamily`. It uses `g(x‖r) = f(x)‖r` with `|x| = |r| = inLen(n)` and `h = ⟨x, r⟩`, and it is hard-core for `g`, which corrects the text's "for `f`" (declared). The final concrete bound `ε/(4·2^k)` is stronger than the text's `ε³/(32n)` (declared).
- **The "(OWP)" clause:** this pack has it only as bijectivity at each `n` (`glPad_f_bijective`). The `PermFamily` form is pack 03i's (note #9).
- **Collection form:** faithful up to the over-strong `henc` (finding #3) and the unaudited `Collection.HardCore` (note #8).

**6. `HardCoreClaims.lean`.** None of its 8 declarations has a sorry, and it elaborates. Its axioms are not printed (finding #6). Each declaration re-exports a proved concrete lemma of the frozen `HardcoreBit/*` layer.

| Declaration | What it claims | True? | Attribution |
|---|---|---|---|
| `fact_88_4` | `⟨a, b⊕c⟩ = ⟨a,b⟩ ⊕ ⟨a,c⟩` | yes | Fact 88.4 ✓ |
| `thm_87_3_1` | prediction probability 1 ⇒ the `e_i`-query inverter inverts `g` with probability 1 | yes | §3.4.3 oversimplified case ✓ |
| `thm_87_3_2` | `3/4 + ε` prediction and `inLen ≤ 2ε²T` ⇒ the majority inverter (Alg 88.5) inverts `g` with probability `≥ ε/4` | yes (good set `ε/2`; each guess correct with probability `≥ 1/2 + ε`; Chebyshev; union bound `≤ 1/2`) | less simplified case ✓ (Chebyshev in place of Chernoff, declared) |
| `thm_87_3_3` | `c + ε ≤` prediction ⇒ `Pr_x[secProb ≥ c + ε/2] ≥ ε/2`, for any `c, ε ≥ 0` | yes (averaging; if `c + ε/2 > 1` the hypothesis is false) | good set ✓ (generalizes `c ∈ {3/4, 1/2}`) |
| `thm_87_3_6` | for a good `x` and `k ≥ 1`, each bit of the ideal recovery is wrong with probability `≤ 1/(ε²(2^k−1))` | yes (pairwise-independent Chebyshev with `δ = ε/2`) | ✓, but the docstring misquotes the text's constant (note #7) |
| `thm_87_3_7` | subset sums over nonempty `L ⊆ [k]` are uniform and pairwise independent | yes | "show this!" ✓ |
| `thm_87_3_8` | the `k` guessed bits are all right with probability `2^{−k}`, and then guessed recovery equals ideal recovery | yes | ✓ |
| `thm_87_3_9` | `1/2 + ε` prediction and `2·inLen ≤ ε²(2^k−1)` ⇒ inversion `≥ ε/(4·2^k)`; adding `ε²2^k ≤ 4·inLen` gives `≥ ε³/(16·inLen)` | yes (`ε/(4·2^k) ≥ ε³/(16n)` under the second hypothesis) | ✓ (stronger than the text's `ε³/(32n)`, declared) |

The declaration names encode inventory ids (Thm-87.3.x), not [PS10] numbers; the docstrings say so.

---

## Inventory check (rows of `inventory-ch3.md` whose location is this pack)

| Row | Formal | Verdict |
|---|---|---|
| Claim-67.a | — | Not formalized (optional; note #10). |
| Def-74.1 | `Ensemble.Pseudorandom` (03a), `pseudorandom_iff_prgAdv`, `uniform_pseudorandom` | Faithful. `1^n` is the declared D5 deviation and is equivalent for injective `ℓ`. |
| Def-75.2 | `Ensemble.NextBitUnpredictable`, `nextBitProb` | Faithful. Declared deviations: `i < ℓ(n)` (corrects the source error), `≤` vs `<` (proved equivalent in `nextBitUnpredictable_iff_lt`). |
| Rem-75.3 | `A.predictor n i` (receives `1^n`) | Faithful. |
| Thm-75.4 | `NextBitUnpredictable.pseudorandom` | True, but weaker than the source (extra `hℓ`, finding #2). |
| Thm-75.4.conv | `Pseudorandom.nextBitUnpredictable`, `prgAdv_nextBitDist` | Faithful, with an exact identity. Lives in `NextBit.lean`, not `Pseudorandom.lean` as the inventory proposed. |
| Thm-75.4.c | `exists_nextBitPred` | Faithful (`1/2 + ε/ℓ`). |
| Thm-75.4.1 | `nextBitHybrid`, `acceptProb_nextBitHybrid_zero/self` | Faithful (`H^0 = U_ℓ`, `H^ℓ = X`). |
| Thm-75.4.2 | `acceptProb_nextBitHybrid_mix` | Faithful. The sketch of its consumer is stale (finding #5). |
| Alg-76.5 | `nextBitPred` | Faithful. Drawing `ℓ` coins instead of `ℓ − i` is declared and benign (unused coins). |
| Def-77.1 | `PRG`, `PRG.Easy`, `PRG.ensemble`, `PRG.Secure` | Faithful except at `n = 0` (finding #1). The length-regular form and the deterministic evaluator are declared and benign. |
| Claim-107.c | — | Not formalized (optional; note #10). |
| Constr-77.a, Claim-78.a, Claim-78.b | — | Not formalized and not recorded as remarks (note #10). |
| Def-78.3 | `HardCore` | Faithful. Declared deviations: `k = n`, typed domain, deterministic evaluator, `[true]` verdict; all benign. |
| Def-78.3.coll | `Collection.HardCore` (`Collections.lean`) | Not auditable from the bundle (note #8). |
| Thm-79.4 | `owp_hardcore_prg`, `exists_owpPredictorSnoc` | Faithful. The direct reduction with an exact `1/2 + ε` replaces the text's next-bit route; declared and benign. |
| Claim-79.a | — | Not formalized; not needed on the formal route (declared). |
| Lem-80.5 | `PRG.expand`, `prg_expand`, `exists_expandRed_ge` | The construction and the loss are faithful. The `∀ n` expansion hypothesis (finding #1) and the signature drift (finding #4) remain. |
| Cor-81.7 | `PermFamily.iterPRG`, `iterPRG_eq_expand`, `cor_81_7` | Faithful (`ℓ(n) + 1` bits, `n ≤ ℓ(n)`; source error 38 declared). |
| Constr-82.a | — | Not formalized (deferred). |
| Thm-87.3 | `goldreich_levin` | Faithful for `g`. The OWP clause appears only as bijectivity (note #9). |
| Thm-87.3.a | `FunFamily.StrongOneWay.glPad`, `glPad_f_bijective` | Faithful. |
| Thm-87.3.b | `FunFamily.StrongOneWay.glPad_hardCore` | Faithful. |
| Thm-87.3.coll | `Collection.OneWay.glPad(_hardCore)`, `goldreich_levin_coll`, Perm/Trapdoor variants | Faithful up to `henc` (finding #3) and the unaudited Def-78.3.coll (note #8). |

---

## Every definition, restated in my own words before reading its docstring

Every docstring agrees with my restatement (there is no gap between the stated formula and the Lean
body). The fidelity column compares each definition with the source.

| Definition | My restatement | Fidelity to the source |
|---|---|---|
| `PRG` | A syntactic polynomial `ℓ` and, for each `n`, a map `{0,1}^n → {0,1}^{ℓ(n)}`, with `n < ℓ(n)` for **every** `n ∈ ℕ`. | Over-restrictive at `n = 0` (#1). |
| `PRG.Easy` | One deterministic poly-time string function sends each seed `s` (as a list) to `G_{\|s\|}(s)`. | Declared deviation; equivalent to "PPT, correct with probability 1". |
| `PRG.ensemble` | `n ↦` the law of `G_n(s)` for `s` uniform in `{0,1}^n`. | Faithful. |
| `PRG.Secure` | `Easy`, and `{G_n(U_n)} ≈ {U_{ℓ(n)}}` against non-uniform PPT distinguishers given `1^n`. | Faithful (see Q1). |
| `nextBitProb X i A` | Over a uniform seed `s` and coins `r`, the probability that `A(first i bits of X(s); r)` equals bit `i` (0-indexed) of `X(s)`. | Faithful. |
| `NextBitUnpredictable` | For every non-uniform PPT `A` there is one negligible `ε` such that, for all `n` and positions `i < ℓ(n)`, `A` run at parameter `n` on `(1^n, prefix)` succeeds with probability `≤ 1/2 + ε(n)`. | Faithful. |
| `prefixOf`, `completePrefix` | The first `i` bits of a string; a prefix `t` followed by bits `i…ℓ−1` of `u`. | Faithful. |
| `nextBitHybrid X i` | On seed `(s, u)`: bits `j < i` come from `X(s)`, the rest from `u`. | Faithful. |
| `nextBitHybridFlip X i` | Bits `j < i` come from `X(s)`, bit `i` is `¬X(s)_i`, the rest come from `u`. | Faithful (the text's `H̃^{i+1}`). |
| `nextBitPred D i flip` | On prefix `t` and coins `(u, c)`: run `D(t ‖ u_{≥i}; c)`; output `u_i` if `D` accepts and `¬u_i` otherwise, XOR `flip`. | Faithful. |
| `nextBitDist i A` | Accept `t` iff `A(prefix_i t) = t_i`. | Faithful. |
| `HardCore 𝓕 h` | (i) a deterministic poly-time `H` with `H(⟨1^n, x⟩) = [h_n(x)]`; (ii) for every non-uniform PPT `A` there is a negligible `ε` with `Pr[x ← U_{inLen n}; A(1^n, f_n(x)) = h_n(x)] ≤ 1/2 + ε(n)` for all `n`. Nothing is required of `f`. | Faithful; the source places no requirement on `f` either. |
| `PRG.oneBit G` | The `PRG` of stretch `n + 1`. | Faithful. |
| `owpGenPRG P h` | `G_n(s) = f_n(s) ‖ h_n(s)`. | Faithful. |
| `owpPredictorSnoc D flip` | On `y` with coins `(σ, c)`: output `σ` if `D(y‖σ; c)` accepts, else `¬σ`, XOR `flip`. | Faithful; confirmed by the `rfl` step `h3` in `owp_hardcore_prg`. |
| `oneBitStep G` | `s ↦ (last bit of G(s), first n bits of G(s))`. | Faithful. |
| `PRG.expand G ℓ hℓ` | Stretch `ℓ`; bit `i` is the last bit of `G(X_i)`, where `X_0 = s` and `X_{i+1} = init G(X_i)`; requires `n < ℓ(n)` for all `n`. | Over-restrictive at `n = 0` (#1). |
| `expandRed` | The hybrid-`k` reduction. It enters the statements only through the existential of `exists_expandRed_ge`. | Not trusted surface beyond that existential. |
| `PermFamily.iterPRG P h ℓ hℓ` | Stretch `ℓ + 1`; bit `i` is `h(f^i(s))` for `i = 0…ℓ(n)`; requires `n ≤ ℓ(n)`. | Faithful. |
| `FunFamily.glPad` | The family `x‖r ↦ f(x)‖r` with `\|x\| = \|r\| = inLen(n)`. | Faithful. |
| `FunFamily.glBit` | `⟨x, r⟩ mod 2` on `x‖r`. | Faithful. |
| `FunFamily.glInverter` | `f(x)‖r ↦ R(f(x); c)‖r`. | Faithful. |
| `Collection.glPad F m henc` | Domain `D_i × {0,1}^{L_i}` with `L_i = \|encD_i(default)\|`; `f'_i(x, r) = ⟨f_i(x), r⟩`; the same `Gen`; the sampler appends `m(n)` fresh coins; requires `henc`. | Faithful, but `henc` is over-strong (#3). |
| `Collection.glBit` | `⟨encD_i(x)` padded or truncated to `L_i, r⟩`. | Faithful. |
| `PermCollection.glPad` | Permutations `perm_i × id`. | Faithful. |
| `TrapdoorCollection.glPad` | Inverter `⟨t, ⟨y, r⟩⟩ ↦ ⟨Inv(t, y), r⟩`. | Faithful. |

---

## Every theorem: does its statement say what its docstring claims?

**Pseudorandom.lean.**
- `pseudorandom_iff_prgAdv` and `secure_iff`: definitional unfoldings (`Iff.rfl`), as claimed.
- `uniform_pseudorandom` (reflexivity) and `Indist.pseudorandom` (transitivity): as claimed.
- `ensemble_X` and `ensemble_σ`: `rfl` unfoldings.
- `stretch_pos`: true, but its source attribution is wrong (#2).
- `Easy.samplable`: the output ensemble of an efficiently computable generator is samplable from `n` coins with zero statistical error, as claimed.

**NextBit.lean.**
- `nextBitProb_nonneg`/`_le_one` and `nextBitProb_eq`: trivial.
- `nextBitUnpredictable_iff_lt`: proves the claimed equivalence of the `≤` and `<` forms.
- `completePrefix_prefixOf`: as claimed.
- `acceptProb_nextBitHybrid_zero/self/mix`: exactly the identities `H^0 = U`, `H^ℓ = X` and `H^i = ½H^{i+1} + ½H̃^{i+1}`.
- `nextBitProb_nextBitPred_false/true`: exact predictor analyses `1/2 ± (P(H^{i+1}) − P(H̃^{i+1}))/2`. The statements are right; the first sketch is stale (#5).
- `exists_nextBitPred`: the concrete reduction at `1/2 + ε/ℓ`, as claimed.
- `NextBitUnpredictable.pseudorandom`: Thm 75.4 with the extra `hℓ` (#2).
- `nextBitProb_id` and `uniform_nextBitUnpredictable`: exact `1/2`; the non-vacuity claim holds.
- `acceptProb_nextBitDist`, `prgAdv_nextBitDist` and `Pseudorandom.nextBitUnpredictable`: the soundness direction, exact, as claimed.

**HardCore.lean.**
- `HardCore.easy/hard`: projections.
- `not_hardCore_const`: true, and it shows the hardness clause is not vacuous.
- `owpGenPRG_G_castSucc/last`: unfoldings.
- `exists_owpPredictorSnoc`: an exact `1/2 + prgAdv` that uses only bijectivity, as claimed.
- `owp_hardcore_prg`: Thm 79.4 as claimed.
- `PRG.expand_G`: the closed form.
- `prgAdv_fst`: as claimed (it needs `Nonempty δ`).
- `exists_expandRed_ge`: the concrete Lem 80.5 at `ε/l`.
- `prg_expand`: Lem 80.5 for one-bit-stretch input, with the `∀ n` hypothesis (#1, #4).
- `iterPRG_eq_expand` and `cor_81_7`: as claimed.
- `glPad_f`, `glBit_append`, `predProb_glPad`, `invProb_glInverter`: bridges, each an exact equality as claimed.
- `glPad_f_bijective`: bijectivity at each `n` only, and the docstring says so.
- `StrongOneWay.glPad`, `StrongOneWay.glPad_hardCore` and `goldreich_levin`: Thm 87.3 (a) and (b), as claimed.
- `Collection.glPad_gen/f/sample_runAtL/decD_eq`: unfoldings.
- `Collection.OneWay.glPad`, `OneWay.glPad_hardCore`, `goldreich_levin_coll`, and the Perm/Trapdoor variants: as claimed under `henc`. The trapdoor docstring overclaims (#3).

**HardCoreClaims.lean:** see the table under question 6.

---

## Adversarial instantiations

1. **A "PRG" whose output is no longer than its seed at some lengths.**
   - `⟨.var, fun _ s => s, ?⟩` needs `n < n`, so it is rejected, correctly.
   - `⟨.var + 1, fun n s => Fin.snoc s false, _⟩` is `Easy`, but the last-bit test has advantage `1/2`, so it is not `Secure`, correctly.
   - The genuine length-doubling `⟨2·var, G, ?⟩` needs `0 < 0` at `n = 0`, so it is **rejected although legitimate**. This is finding #1.
   - `prg_expand` with `ℓ = n²` needs `1 < 1`, so it is rejected (#1).
2. **A predicate that is hard-core only because the function is degenerate or not efficiently computable.**
   - For the constant family `f_n(x) = 0^n` and `h_n(x) = x_0`, `HardCore` holds information-theoretically: every predictor succeeds with probability exactly `1/2` once `inLen ≥ 1`. The source's Def 78.3 does not exclude this either.
   - Such an instance cannot reach Thm 79.4, which needs a `PermFamily` and `OneWayPermutation` (`easy`), or Thm 87.3, which needs `StrongOneWay` (`easy`).
   - Take instead a permutation family that is hard to compute in both directions, with `h(x) = x_0`. It may satisfy `HardCore`, and `f(s)‖h(s)` would then be pseudorandom. It is still blocked: `owp_hardcore_prg` needs `hP.easy`, and `PRG.Secure` needs `Easy`. A predicate that is not efficiently computable fails clause (i) of `HardCore`. No false generator theorem follows.
3. **A next-bit predictor that uses its advice to hard-wire the seed.**
   - The seed is drawn inside the experiment (`uprob` over `σ × coins`), after the advice is fixed, so the advice cannot contain the sample.
   - For `X_n = c_n ‖ U_n` with an arbitrary, even uncomputable, `c_n`: a predictor with advice `c_n` predicts the first `|c_n|` bits perfectly, so `X` is not next-bit unpredictable. A distinguisher with the same advice shows `X` is not pseudorandom. Both theorems agree.
   - The completeness reduction's own predictor uses advice only for the sign bit; the position comes from the prefix length.
   - An empty seed type, which would make the test vacuous, is excluded by `Ensemble.nonempty` (the run-3 P2-2 repair holds).
4. **An ensemble with `ℓ = n` that passes the next-bit test.** `NextBitUnpredictable.pseudorandom` cannot be applied, because `hℓ 0 : 0 < 0` fails, although the conclusion is true (#2).
5. **A collection whose generator outputs one fallback index at two parameters.** `henc` is then unsatisfiable for any non-constant `m`, so `goldreich_levin_coll` is vacuous for it (#3).

---

## Run-3a repairs in scope

| Repair | Status at `a3c5fa8b` |
|---|---|
| **P2-2** (`Ensemble.nonempty`; `NextBitUnpredictable.pseudorandom` back to the frozen shape) | Holds: the statement has no `hσ`, and the field is used. |
| **"P2-3"** (`uprob_split_bit` replaces the 2-to-1 map) | The mathematics holds (`ψ` is an involution). The repair is not recorded in the run-3 summary, and one sketch still describes the old map (#5). |
| **P3-1** (`henc` an argument of `Collection.glPad`) | Holds, but its cost is not stated (#3). |
| **P4-1** (`glPad` is never a `PermFamily`; the OWP route is `glHalf`) | The docstrings hold; the route is pack 03i's (#9). |
| **P4-2** (collection GL through `invProb_guessInverter_enc_pad`) | Statement unchanged and sketch updated. Holds. |

I did not re-report any finding that run 3 resolved.

---

## Attestations

- **Elaboration.** `replay.log` lists 338 modules, all `rc=0` with `errors=0`. The 22 sorry warnings add up correctly (2 + 1 + 5 + 3 + 4 + 2 + 3 + 1 + 1). All four files under audit, and the out-of-scope `HardCoreLemmas`, `HardCoreLoops`, `HardCoreGL*` and `GoldreichLevinDomain`, show `sorry=0`. `HardCorePermutation` is not in the closure (#9).
- **Axioms.** 22 prints, all using only `propext`, `Classical.choice` and `Quot.sound` (or a subset). Coverage is incomplete (#6). Three lines are double-spaced, which fits long names wrapped and re-joined during extraction; they are not raw `#print axioms` output, but nothing suggests tampering.
- **Admissions** (0) and **lint** (0 findings): consistent with the replay. The `@[simp]` on `PRG.ensemble_X` passed the lint (#11).

## Limits of this audit

- **No PDF.** The [PS10] PDF did not arrive and could not be downloaded, so the source comparisons rest on the inventory's quotations and my own reading of the text. The two *PDF check* items are the "for any polynomial ℓ" wording of Lemma 80.5 (#1) and the constant of the §3.4.3 per-bit bound (#7).
- **Context bodies not in the bundle.** I read the following from their DESIGN signatures, from the inventory, and from the `rfl` steps in the audited proofs: `predProb`, `prgAdv`, `distAdv`, `NUPPT.predictor`/`distinguisher`, `Negligible`, `owpPredictor`, `prgExtRed`, `PermFamily`, `OneWayPermutation`, `Collection.HardCore`.
- **Tactic proofs.** Not reviewed, per the brief.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03c-review.md =====

# Gate 03c: review of the external auditor's findings (hard-core bits and PRGs)

**Summary.**
- **Verdicts.** Of the 11 findings, 9 are **true** and 2 are **partly true**. None is false.
  - #1 is partly true. The limit on what `PRG` can express is real and exactly as stated. But its cost is already declared, with a proved workaround, in `PRF.lean` (pack 03d), which the auditor did not see. And no downstream statement is vacuous because of it.
  - #4 is partly true. The truncation lemma the auditor asks for already exists in `PRF.lean`.
- **Severity.**
  - **#1 stays major, not blocker.** No statement in ch. 2–4 or ch. 5–8 is about a `PRG` of stretch `2n` or `n^c`. It remains a major because the frozen interface needs an explicit ruling (Q1).
  - **I propose raising #3 from minor to major.** The auditor's example was hypothetical. The library's own trapdoor collections fail `henc`: RSA encodes elements in `2·max(n,2)` bits, Rabin/Blum in `2·max(n,3)` bits, and neither is a polynomial in `n`. Yet the docstring claiming "satisfiable from trapdoor permutations alone" is the stated justification of Thm 104.4's declared deviation in `PublicKey.lean`.
  - All other severities are unchanged.
- **Rulings needed: Q1 (#1), Q2 (#2), Q3 (#3).** My recommendations:
  - Q1-A: keep `∀ n, n < ℓ n` and declare the cost.
  - Q2-A: drop the extra hypothesis of Thm 75.4. The change stays inside `NextBit.lean`.
  - Q3-A: state the cost of `henc` now, and weaken it as a follow-up.
- **Impact if the recommendations are adopted.**
  - No pending pack has to wait for a 03c statement change.
  - 03d picks up docstring edits only.
  - 03f1, 03f2, 03g, 03h, 03i, 03j, 03k and 03l are unaffected.
  - No ch. 5–8 statement changes under any option. Prong D's Thm 180.1 takes `∃ G : PRG, G.Secure`, which has the same truth value under all three Q1 options.
  - 03c's collection section (`Collection.glPad`) must be re-checked after 03b's major #1 is repaired.

**How this was checked.**
- I read every Lean reference at `a3c5fa8b` in `wt-g03`.
- Source passages come from `blueprint/src/references/pass-shelat-2010-ch3.raw.md`. This settles both of the auditor's *PDF check* items (see #1 and #7).
- Downstream use was found by grepping, in each sibling worktree, only the files changed relative to `a3c5fa8b`:
  - `wt-s2b` at `afe5982f`;
  - `wt-prong-a` at `2d7b5441`;
  - `wt-prong-b` at `1cf007d1`;
  - `wt-prong-c` at `aa71d0e7`;
  - `wt-prong-d` at `6ea900ae`.
- The pack-to-file map is `gate03/packs.json`. The ripple script is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/gate03-review/scripts/ripple03c.py`.
- No Lean was built.

| # | Auditor | Verdict | Proposed severity | Fix type | Ruling |
|---|---|---|---|---|---|
| 1 | major | partly true | **major** (ruling item; not blocker) | Q1-A: docstrings + DESIGN §5/§2.12 | **Q1** |
| 2 | minor | true | minor | Q2-A: statement change (strengthening) | **Q2** |
| 3 | minor | true (understated) | **major** (as it stands) | Q3-A: docstrings + DESIGN §5.18 | **Q3** |
| 4 | minor | partly true | minor | DESIGN record + optional corollary | no |
| 5 | minor | true | minor | docstring + records | no |
| 6 | minor | true | minor | `Checks.lean` prints, re-attest | no |
| 7 | note | true | note | docstrings | no |
| 8 | note | true (answered) | note | none here; follows 03b | no |
| 9 | note | true (answered) | note | none | no |
| 10 | note | true | note | module docstring | no |
| 11 | note | true | note | hygiene | no |

---

## #1 (major): `PRG.expands` at every `n`, including `n = 0`

**Check: partly true.**

*True: the expressivity claim.*
- `Pseudorandom.lean:118` has `expands : ∀ n, n < stretch.eval n`.
- `HardCore.lean:332` (`PRG.expand`) and `:411` (`prg_expand`) take the same `hℓ : ∀ n, n < ℓ.eval n`.
- A `PolyExpr` (`PolyExpr.lean:67–83`) evaluates to a polynomial with coefficients in ℕ, with `pow p 0 = 1`. So:
  - `2·var` fails at `0 < 0`;
  - `var^2` fails at `1 < 1`;
  - no stretch equals `2n` exactly.
- The source shows `n = 0` is not intended:
  - Def 77.1 (raw l. 452–458) literally says "|G(x)| > |x|". The formal field is that literal reading at `x = ε`.
  - Lemma 80.5 does say "For any polynomial ℓ" (raw l. 565–566). This settles the auditor's *PDF check*.
  - Alg 92.1 (l. 1083) and Thm 97.3 (l. 1293) use a "length-doubling" generator.
- Inventory §4.4 (`inventory-ch3.md:995`) planned both "`n < ℓ n`" and "GGM … use `2n`", as the auditor says.

*False: "neither the PRG notes nor DESIGN §5 record this cost".* This is literally true of `Pseudorandom.lean` and of DESIGN §5, but the cost is recorded where it bites.
- `PRF.lean:43–48` (module docstring): "a length-doubling generator is not a `PRG` of this library (the stretch `2n` does not exceed `n` at `n = 0`), so it is the separate predicate `DoublingPRG`".
- `PRF.lean:370–372` repeats this as a declared deviation on `DoublingPRG`.
- The workaround is proved:
  - `PRG.truncate` (`:390`) and `PRG.Secure.truncate` (`:429`);
  - `two_mul_add_one_expands` (`:395`), the stretch `2n + 1`;
  - `PRG.doubling` (`:404`) and `PRG.Secure.doubling` (`:449`, printed in `Checks.lean:224`).
- Alg 92.1 avoids the issue: `prgScheme` uses `(P.expands n).le : n ≤ ℓ(n)` and the first `n` pad bits, declared at `Encryption.lean:55–60`.

*False: the risk "any downstream statement over `P : PRG` with `P.stretch = 2n` is vacuously true".* No such statement exists. I grepped every `PRG`-quantified statement in `wt-g03` and in the ch. 5–8 worktrees:
- `prgScheme*` (Encryption);
- `PRG.Secure.truncate`, `.doubling`, `exists_prf_of_exists_prg` (PRF);
- `truncateTo_*` (PRFLemmas);
- `exists_securePRG_of_owp` (HardCorePermutation);
- `exists_multiMessageSecure_of_exists_prg` (MultiMessage, also in S2b and the prongs);
- `bpp_subset_dtime_subexp` (prong D).

None constrains the stretch to `2n` or `n^c`. GGM is stated over `DoublingPRG G` (`PRF.lean:694`). **So the escalation condition fails; this is not a blocker.**

**Severity: agree major.** It is not misleading as code. It is a choice about a frozen interface (DESIGN §2.12, line 681) that differs from the source's use and is missing from the register. That is "debt that needs explicit human acknowledgment". QUEUE.md already lists it among the four gate 03 majors. It closes once Q1 is ruled and the register line lands.

**Facts the ruling should weigh.**
1. **"PRGs exist" is the same under every option.** A secure generator that expands only for `n ≥ n₀` gives one that expands everywhere: truncate to `n + 1` bits and output anything below `n₀`; security is asymptotic. So every `∃ P : PRG, P.Secure` statement has the same truth value under A, B and C. This covers MultiMessage, PRF, HardCorePermutation and prong D. This is a mathematical remark; it is not formalized.
2. **"Eventually" equals "from 2 on" for these polynomials.** A stretch that eventually exceeds `n` is non-constant, so `n ≤ ℓ(n)` holds for all `n`. Moreover `n < ℓ(n)` holds for all `n ≥ 2`, by cases on the polynomial:
   - degree ≥ 2: `ℓ(n) ≥ n² > n`;
   - linear coefficient ≥ 2: `ℓ(n) ≥ 2n > n`;
   - `n + c` with `c ≥ 1`: `n < n + c` everywhere.

   So option C's "eventually" can be written with the fixed threshold 2, and 2 is the least threshold that admits `n^c`.
3. **The security half of `prg_expand` needs only `0 < ℓ(n)`.** It uses `hℓ` only through `Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)`, for the hybrid index (`HardCore.lean:422, 435`). The everywhere clause is needed only to build the `PRG` value.

**Fix: Q1-A (recommended). Docstrings and DESIGN only.**
- Add to `PRG`'s docstring (`Pseudorandom.lean:103–111`), as a second Deviation:
  > **Deviation:** the expansion clause holds at every seed length, `n = 0` included, as the text's
  > `|G(x)| > |x|` says literally for `x = ε`. A `PolyExpr` stretch is a polynomial with coefficients
  > in ℕ, so a stretch with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) is not a `PRG`, although
  > the text uses such generators (Algorithm 92.1, Theorem 97.3). They are reached up to one bit
  > (`2n + 1`, `n^c + 1`, by `prg_expand`) or by truncation (`PRG.Secure.truncateTo_easy`/`_negligible`);
  > the length-doubling generator of Theorem 97.3 is the separate predicate `DoublingPRG`
  > (`Asymptotic/PRF.lean`), produced from any `PRG` by `PRG.Secure.doubling`.
- In `HardCore.lean:61–62` (module Deviation), `:327` (`PRG.expand`) and `:384` (`prg_expand`), change "`ℓ(n) > n`" to "`ℓ(n) > n` at every `n`, see `PRG`".
- Add DESIGN §5 entry 23: "`PRG.expands` (gate 03c #1): expansion at every `n`, `n = 0` included; stretches `2n`, `n^c` excluded; `DoublingPRG` for Thm 97.3, `2n + 1` or truncation elsewhere." Add a line comment at §2.12:681.
- Optional, prong D: in `Derandomization.lean:68`, name a stretch that expands everywhere, e.g. `a(s^c + 1)^k + s + 1`.

**Fix: Q1-B (`expands : ∀ n, 0 < n → n < stretch.eval n`).** This admits `2n`, but not `n^c`.

```lean
structure PRG where
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, 0 < n → n < stretch.eval n
theorem PRG.le_stretch (P : PRG) (n : ℕ) : n ≤ P.stretch.eval n          -- replaces `(P.expands n).le`
theorem PRG.stretch_pos (P : PRG) {n : ℕ} (hn : 0 < n) : 0 < P.stretch.eval n
def PRG.expand (G) (ℓ : PolyExpr) (hℓ : ∀ n, 0 < n → n < ℓ.eval n) : PRG
theorem prg_expand (G) (ℓ) (hℓ : ∀ n, 0 < n → n < ℓ.eval n) (h : (PRG.oneBit G).Secure) :
    (PRG.expand G ℓ hℓ).Secure      -- proof: default hybrid index where ℓ n = 0, `Negligible.mono ⟨1, _⟩`
def PRG.truncate (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
  fun n s i => if h : n + 1 ≤ P.stretch.eval n then P.G n s (Fin.castLE h i) else false
```

What changes under B:
- `PRG.oneBit`, `iterPRG` and `iterPRG_eq_expand` need proof-term edits only.
- `cor_81_7` and `owp_hardcore_prg` keep their statements.
- `PRG.Secure.truncate`, `PRG.doubling` and `PRG.Secure.doubling` change (`PRF.lean`, 03d, which S2b's F-1 restatement is editing now).
- The 8 uses of `(P.expands n).le` in `Encryption.lean` (03d) change.
- The callers of `truncateTo_*` must supply `hm` at `n = 0` (`PRFLemmas.lean`, 03j).
- `expandRedMachine`'s `hk : ∀ n, k n < ℓ.eval n` (`HardCoreLemmas.lean:533`, 03i) must be weakened.
- Thm 75.4's `hℓ` must go: Q2-A becomes mandatory.
- `DoublingPRG` could be retired, but that is optional.

**Fix: Q1-C (`expands : ∀ n, 2 ≤ n → n < stretch.eval n`, equivalent to "eventually").** This admits every non-trivial polynomial stretch, `n^c` included. It costs everything in B, plus:
- a private `PolyExpr` lemma (`eval p 1 = 0 → ∀ n, eval p n = 0`, by structural induction) to recover `PRG.le_stretch` for Alg 92.1;
- defaults below 2 in `truncate` and `prg_expand`.

**Ripple.**
- Q1-A: only 03c's files and DESIGN.
- Q1-B and Q1-C: 03c, then 03d (PRF.lean, Encryption.lean), 03i (HardCoreLemmas), 03j (PRFLemmas); also 03e's `Commitment.lean:445` (`simp [PRG.oneBit]`, proof-level only).
- ch. 5–8, under every option: no statement text changes. In particular, prong D's `bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure)` keeps its text and its meaning (fact 1). Its sketch already routes through `PRG.Secure.truncate` and `prg_expand`, which works under A with a stretch such as `a(s^c+1)^k + s + 1`.
- Under B or C, S2b's in-flight `PRF.lean`/`PRFLemmas.lean` would conflict.

**Ruling: yes, Q1.**

---

## #2 (minor): the extra `hℓ : ∀ n, 0 < ℓ.eval n` of Thm 75.4

**Check: true.**
- `NextBit.lean:643–644` has `(hℓ : ∀ n, 0 < ℓ.eval n)`. The source's Thm 75.4 (raw l. 351–353) has no such hypothesis.
- The docstring (`:618`) says "(with `ℓ(n) > 0`)" without a Deviation line. The module docstring's two Deviations (`:34`, `:39`) do not mention it.
- `stretch_pos` (`Pseudorandom.lean:150–152`) wrongly calls it "the hypothesis `0 < ℓ(n)` of [PS10, Theorem 75.4]".
- The hypothesis is removable. Where `ℓ(n) = 0`, both `X_n` and `U_0` are the point mass on the empty string, and seeds are nonempty (`Ensemble.nonempty`). So `prgAdv = 0`, and the contradiction set of the proof lies where `ℓ(n) > 0`.
- The machine in `exists_nextBitPredMachine` (`:540`) does not depend on `i`: its advice is `⟨D.advice n, [flip n]⟩`, and the position is read off `|t|`. So its identity generalizes to every `i : Fin (ℓ.eval n)`.
- The hypothesis is part of the frozen shape (DESIGN §2.12, line 690). It has no Lean consumer: `Ensembles.lean:57, 120` (03a) mention the theorem's name only.

**Severity: agree minor.** One interaction with #1: under Q1-B or Q1-C, PRG output ensembles with `ℓ(0) = 0` fall outside the theorem, and `stretch_pos` becomes false. So Q2-A is then required.

**Fix: Q2-A (recommended; a strengthening).**

```lean
private theorem exists_nextBitPredMachine {ℓ : PolyExpr} (D : NUPPT) (flip : ℕ → Bool) :
    ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
      ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
        A.predictor n i t (e n (u, c)) = nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n) t (u, c)
theorem prgAdv_eq_zero_of_eval_eq_zero … : ℓ.eval n = 0 → prgAdv (X.X n) D = 0
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (h : X.NextBitUnpredictable) : X.Pseudorandom
```

- In the proof, choose `(i n, flip n)` only where `0 < ℓ n`; take `flip n := false` elsewhere.
- Use the positive polynomial `mul p (add ℓ (const 1))`, with `1/(p(ℓ+1)) ≤ 1/(pℓ)` on the infinite set.
- Rewrite `stretch_pos`'s docstring to read "positive at every seed length (from the expansion clause)".
- Update DESIGN §2.12:690.

**Fix: Q2-B.** Keep `hℓ`, add "**Deviation:** `hℓ : ∀ n, 0 < ℓ(n)` (not in the source; removable, …)" plus a DESIGN §5 line, and fix the attribution in `stretch_pos`. Docstrings only. This is consistent only with Q1-A.

**Ripple.** `NextBit.lean` and DESIGN only. No pending pack and no ch. 5–8 file is affected.

**Ruling: yes, Q2.** It changes a frozen signature, though only to strengthen it.

---

## #3 (minor, proposed major): `henc` in `Collection.glPad`

**Check: true, and understated.**
- `HardCore.lean:731–732` requires `henc : ∀ n r x, (F.encD (F.index n r) x).length = m.eval n`.
- A non-constant polynomial with coefficients in ℕ is strictly increasing. So an index generated at two parameters forces `m` to be constant, as the auditor says.
- **The library's own instances fail it:**
  - `rsaTrapdoor` (`RSA.lean:631`). The index at `n` is `rsaIndexOf (max n 2) _` (`:406, :431`), and `rsaEnc i x = natToList (pairFstD i).length _` (`:230`), with `length_natToList` (`Arithmetic.lean:88`). So the encoding has `2·max(n,2)` bits: 4, 4, 4, 6, 8, … `henc` would need `m(0) = m(1) = 4` and `m(3) = 6`. That is impossible.
  - `rabinBlumTrapdoor` (`Rabin.lean:846`) has `2·max(n,3)` bits: `rabinIndexOf` at `:311–312`, `blumEnc` at `:682`. It fails the same way.
  - `expCollection` fails as the auditor describes.
- So `TrapdoorCollection.OneWay.glPad_hardCore` cannot be instantiated with any candidate in the library.
- Its docstring (`:973–975`) says Thm 104.4's hypothesis "is satisfiable from trapdoor permutations alone".
- That docstring is the justification of Thm 104.4's declared deviation in `PublicKey.lean:797–800` (03d): "`TrapdoorCollection.OneWay.glPad_hardCore` supplies one from trapdoor permutations alone".
- `glPad_tdpBitScheme_singleBitSecure` (`PublicKey.lean:944–949`) inherits `henc`.
- The per-index form that the auditor proposes does hold for RSA, Rabin and DL. Their encoding widths depend only on the index (`|pairFstD i|`, `|i|`, `dlW i`), and are bounded by `2n + 4` (RSA) and `2n + 6` (Rabin/Blum).

**Severity: propose major** (materially misleading as it stands). The theorems are true. But a trusted-surface claim that underwrites a declared deviation of Thm 104.4 is supported by no instance in the library. It is not a blocker:
- no ch. 5–8 statement uses `glPad`;
- OT (`ObliviousTransfer.lean:395, 427`, prong B) and padded CPA (`Composability/PublicKey.lean:432`, prong C) take `hHC : T.toCollection.HardCore h` as a hypothesis.

**Fix: Q3-A (recommended now). Docstrings only.**
- Extend the Deviation at `HardCore.lean:728–730`:
  > … `henc` ties the encoding length at every generated index to `m(n)`; a non-constant `PolyExpr`
  > is strictly increasing, so an index generated at two parameters forces `m` constant. The
  > library's candidates do not satisfy it as parametrized (`rsaTrapdoor`: `2·max(n,2)`-bit elements;
  > `rabinBlumTrapdoor`: `2·max(n,3)`; `expCollection`: `dlDefaultIndex` below `n₀`). A per-index
  > form (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit them; not formalized.
- Replace "satisfiable from trapdoor permutations alone" at `:973–975` and at `PublicKey.lean:797–800` with "satisfiable from trapdoor permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`)".
- Append the cost to DESIGN §5.18.

**Fix: Q3-B (the real repair; can follow later).**

```lean
noncomputable def Collection.glPad (m : PolyExpr)
    (hreg : ∀ i (x : F.D i), (F.encD i x).length = (F.encD i default).length)
    (hbd : ∀ n (r : F.gen.Coins n), (F.encD (F.index n r) default).length ≤ m.eval n) : Collection
-- Sample'(1^n, i; s ‖ ρ) = ⟨w, ρ.take |w|⟩ with w = Sample(1^n, i; s), ρ of m(n) bits
```

- `OneWay.glPad`, `OneWay.glPad_hardCore`, `goldreich_levin_coll`, and the Perm/Trapdoor variants change their hypotheses accordingly.
- `HardCoreGLColl.lean:229, 293` (03i) carries `henc` per index and globally, and needs reworking. The GL-domain lemma `invProb_guessInverter_enc_pad` is already per-length (`GoldreichLevinDomain.lean:153`) and needs no change.
- `glPad_tdpBitScheme_singleBitSecure` (03d) changes its statement.
- Sequencing: "`|w| = L_i`" needs canonical sampler outputs. That is 03b's major #1 (`decD_canonical`). So Q3-B must follow 03b's repair.

**Fix: Q3-C.** Keep `henc` and add reparametrized candidates (RSA at `n + 2`, Blum at `n + 3`) with `henc` proofs (`m = 2·var + 4`, `2·var + 6`) and one-wayness transfer. This is new API in 03f2.

**Ripple.**
- Q3-A: 03c and 03d (docstrings).
- Q3-B: 03c, 03i (HardCoreGLColl, HardCoreLemmas), 03d (statement); after 03b.
- Q3-C: 03f2.
- ch. 5–8: none under any option.

**Ruling: yes, Q3.**

---

## #4 (minor): `prg_expand` takes a one-bit `G`, not a `P : PRG`

**Check: partly true.**
- True:
  - The code is `prg_expand (G : ∀ n, … → (Fin (n + 1) → Bool)) (ℓ) (hℓ) (h : (PRG.oneBit G).Secure)` (`HardCore.lean:410–411`).
  - DESIGN §2.12:698 records `prg_expand (P : PRG) (ℓ) : P.Secure → …`, and §5 has no entry for the difference.
  - No truncation lemma is *in this pack*.
- False in effect:
  - The truncation exists: `PRG.truncate` and `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` (`PRF.lean:390, 429`, pack 03d), on top of `PRG.Secure.truncateTo_easy`/`_negligible` (`PRFLemmas.lean:225, 248`, pack 03j).
  - Prong D's docstring already cites this route (`Derandomization.lean:31`).
  - The auditor's proposed `PRG.truncSucc` would duplicate `PRG.truncate`.

**Severity: agree minor.**

**Fix.**
- Record the shipped signature in DESIGN §2.12:698. The one-bit input is faithful to Lem 80.5.
- Optionally add the `PRG`-level corollary next to the truncation, in 03d after S2b lands:

```lean
/-- **Any PRG expands to any stretch `ℓ(n) > n`** [PS10, Lemma 80.5, with the truncation of the
proof of Theorem 97.3]. -/
theorem PRG.Secure.expand {P : PRG} (hP : P.Secure) (ℓ : PolyExpr) (hℓ : ∀ n, n < ℓ.eval n) :
    (PRG.expand P.truncate ℓ hℓ).Secure :=
  prg_expand P.truncate ℓ hℓ hP.truncate
```

**Ripple.** DESIGN only. The optional corollary goes in 03d's `PRF.lean`. Prong D could cite it.

**Ruling: no.**

---

## #5 (minor): stale sketch of `nextBitProb_nextBitPred_false`; "P2-3" unrecorded

**Check: true.**
- `NextBit.lean:360–361` still describes "the bijection `(b, (s, u), c) ↦ (s, (update u i (xor b (X s i)), c))`". The proof rewrites with `uprob_split_bit` (`:375`), whose docstring (`:232–233`) calls that very map "2-to-1, not a bijection — run-3 audit P2-3".
- "P2-3" appears nowhere in `audits/pass-shelat/`; the run-3 summary has P2-1 and P2-2 only. It appears only at `NextBit.lean:233`.
- `inventory-ch3.md:317` has the same "bijection".

**Severity: agree minor** (policy §3, Synchronization).

**Fix.**
- Rewrite the sketch: "`uprob_split_bit` at position `i` with the bit `x_i` (an adjoined uniform bit and the involution `ψ`): the success event averages the same event with `x_i` and with `x̄_i` planted at bit `i` of `u`; planting `x_i` gives `nextBitHybrid X (i+1)` and the predictor is right iff `D` accepts, planting `x̄_i` gives `nextBitHybridFlip X i` and it is right iff `D` rejects."
- Record P2-3 in gate 03's resolution log, since the run-3 summary is a closed record, and annotate inventory row 317.

**Ripple.** None outside 03c. **Ruling: no.**

---

## #6 (minor): axiom evidence omits `HardCoreClaims` and the non-vacuity theorems

**Check: true.**
- `Checks.lean:186–210` and `evidence/c/axioms.log` (22 lines) do not cover:
  - `fact_88_4`, `thm_87_3_1/2/3/6/7/8/9`;
  - `not_hardCore_const`, `Ensemble.uniform_nextBitUnpredictable`;
  - `PermCollection.OneWay.glPad_hardCore`.
- `HardCoreClaims.lean` has no `sorry`, but its declarations re-export `HardcoreBit/*` lemmas, so only a print rules out a transitive `sorryAx`.
- DESIGN §4:943 asks for non-vacuity theorems to be printed in `Checks.lean`. The two named above are not in its list, but the rule plainly covers them.

**Severity: agree minor.**

**Fix.** Append 11 `#print axioms` lines to `Checks.lean` and re-run 03c's axiom attestation. **Ripple:** none. **Ruling: no.**

---

## #7 (note): `HardCoreClaims` docstrings

**Check: true.**
- The module docstring (`HardCoreClaims.lean:16–19`) says "each the family-level instance". But `fact_88_4` and `thm_87_3_6/7/8` (`:62, 108, 119, 129`) are stated for an arbitrary `f`.
- *PDF check settled.* The text reads "each `x_i` is wrong with probability at most `1/(4mε'²) ≤ 1/(mε'²)`" (raw l. 994–998). With `ε' = ε/2`, the formal `1/(ε²(2^k − 1))` is the text's tighter `1/(4mε'²)`, where `m` counts the samples. The docstring cites the looser constant.
- The text draws `r_1 … r_{m−1}` from `log m` seeds (l. 1009). So the text's `m` is `2^k` (as `thm_87_3_8` has it), while `thm_87_3_6` uses `m = 2^k − 1`, the number of samples.

**Fix.** Docstrings only:
- "the text's `1/(4mε'²)` (`≤ 1/(mε'²)`), `m` read as the `2^k − 1` samples (the text has `m − 1` samples and writes `m`)";
- qualify "family-level instance" in the module docstring.

**Ripple:** none.

---

## #8 (note): `Collection.HardCore` not auditable from the bundle

**Check: true as a scope note, and answered.** Pack 03b audited Def-78.3.coll: `gate03b-findings.md` #1 (major), #3, #7, and its inventory row at line 186. Its major #1 changes what `Collection`'s fields guarantee (canonical decoding, or `H` on every decodable string). `Collection.glPad`'s `decD`/`sample_spec` (`HardCore.lean:734–770`) and the evaluator that `glPad_hardCore` must supply are built on those fields.

**Fix.** None in 03c. **Ripple:** in the reverse direction. 03c's collection section (`HardCore.lean:712–981`) must be re-verified after 03b's repair, together with Q3-B if that is chosen.

---

## #9 (note): the OWP route through `HardCorePermutation` (pack 03i)

**Check: true as a scope note, and answered.** At `a3c5fa8b`, 03i's evidence settles it:
- `evidence/i/replay.log:316` shows `HardCorePermutation rc=0 … sorry=0`;
- `evidence/i/axioms.log:13–15` shows `OneWayPermutation.glHalf`, `exists_owp_hardCore` and `exists_securePRG_of_owp` with the standard axioms only.

**Fix:** none.

---

## #10 (note): unformalized items not recorded as remarks

**Check: true.** `inventory-ch3.md:363` asks for Constr-77.a, Claim-78.a and Claim-78.b to be recorded "as remarks in `HardCore.lean`'s module docstring if not formalized". `HardCore.lean:22–123` has none of them.

**Fix.** Add three remark lines:
- Shamir's `f^n(s)‖…‖s`;
- Claim-78.a via `uprob_comp_equiv` on `f^[k]`;
- Claim-78.b via Garg's `predProb_fixedBitPredictor`.

Claim-107.c (a PRG is a OWF) is optional (DESIGN §6.2). **Ripple:** none.

---

## #11 (note): policy hygiene

**Check: true.**
- `@[simp]` at `Pseudorandom.lean:145`.
- There are no `_iff` lemmas for `PRG.Easy` or `HardCore`, and no `_eq` lemmas for `PRG.oneBit`, `oneBitStep`, `expandRed`, `owpPredictorSnoc` or `Collection.glBit` (policy §1, the 2026-10-16 rule).
- Lines: `NextBit.lean` has 914, `HardCore.lean` 981.

**Fix.**
- Drop the `@[simp]`. `ensemble_X` has no consumer outside `Pseudorandom.lean`; pass it explicitly in `Easy.samplable`'s `simp` (`:176`).
- Add the `rfl` lemmas.
- Split `HardCore.lean`'s collection section (`:710–981`) into a child file that `HardCore.lean` re-imports, so consumers' imports are unchanged. Do this after #3 is settled, which grows that section under Q3-B.

**Ripple:** none. **Ruling: no.**

---

## Questions for the user

**Q1 (#1). How should `PRG`'s expansion clause treat small seed lengths?**
- **A (recommended).** Keep `∀ n, n < ℓ(n)`, the literal Def 77.1(2) at `x = ε`. Declare the cost at `PRG`, at `PRG.expand`/`prg_expand`, in DESIGN §5 (new entry 23) and at §2.12. Exact `2n` stays the separate `DoublingPRG`.
  - *Cost:* docstrings in 03c's files and DESIGN.
  - No pending pack waits. No ch. 5–8 change. `∃ PRG` statements keep their meaning.
- **B.** `∀ n, 0 < n → n < ℓ(n)`. Admits `2n` (so `DoublingPRG` could be retired), but not `n^c`.
  - *Cost:* statement changes in Pseudorandom/HardCore (03c), PRF/Encryption (03d, colliding with S2b's in-flight F-1), PRFLemmas (03j) and `expandRedMachine` (03i).
  - Forces Q2-A.
  - 03d, 03i and 03j wait.
- **C.** `∀ n, 2 ≤ n → n < ℓ(n)`, which equals "eventually" for these polynomials. Admits every polynomial stretch, `n^c` included.
  - *Cost:* everything in B, plus a `PolyExpr` lemma to keep `n ≤ ℓ(n)` for Alg 92.1, and defaults below 2 in `truncate` and `prg_expand`.

**Q2 (#2). Thm 75.4's extra `hℓ : ∀ n, 0 < ℓ(n)`.**
- **A (recommended).** Drop it. This strengthens the theorem to the source's statement.
  - *Cost:* restate the private machine lemma for all positions, plus about 50 lines of proof, in `NextBit.lean` only.
  - Change DESIGN §2.12:690. No consumers.
  - Required if Q1 is B or C.
- **B.** Keep it and declare it as a Deviation (docstring and DESIGN §5), fixing `stretch_pos`'s attribution.
  - *Cost:* docstrings only. Valid only with Q1-A.

**Q3 (#3). `Collection.glPad`'s `henc`, which no library candidate satisfies.**
- **A (recommended now).** State the cost: the RSA, Rabin/Blum and DL widths fail `henc`. Correct the "satisfiable from trapdoor permutations alone" claims in `HardCore.lean:973–975` and `PublicKey.lean:797–800`, and DESIGN §5.18.
  - *Cost:* docstrings in 03c and 03d. No statement change.
- **B.** Weaken `henc` to per-index regularity plus a polynomial bound. This admits RSA, Rabin and DL as they are.
  - *Cost:* statement changes in 03c (7 declarations), 03i (HardCoreGLColl) and 03d (`glPad_tdpBitScheme_singleBitSecure`).
  - A new sampler.
  - Must follow 03b's major #1. 03d and 03i wait.
- **C.** Keep `henc` and add reparametrized RSA/Blum instances with `henc` proofs.
  - *Cost:* new API and proofs in 03f2 (RSA.lean, Rabin.lean). DL is still excluded.

---

## What the auditor missed

1. **The length-doubling cost is already declared, with a proved workaround,** in `PRF.lean:43–48, 370–372`: `DoublingPRG`, `PRG.truncate`, `PRG.Secure.truncate`, `two_mul_add_one_expands`, `PRG.doubling`, `PRG.Secure.doubling`. This weakens #1's "not recorded" and #4's "no truncation lemma".
2. **No downstream statement is vacuous** (#1's escalation test). I checked every statement quantifying over `PRG` in ch. 2–4 and ch. 5–8.
3. **`henc` fails for the library's own trapdoor collections.** RSA has `2·max(n,2)`-bit elements and Rabin/Blum `2·max(n,3)`. Thm 104.4's declared deviation (`PublicKey.lean:797–800`, 03d) rests on the overstated docstring.
4. **#1 and #2 interact.** Under Q1-B or Q1-C, `stretch_pos` is false and Thm 75.4's `hℓ` excludes PRG output ensembles.
5. **Both *PDF checks* can be settled from the branch's raw text.** Lem 80.5 does say "for any polynomial ℓ". The per-bit bound reads "`1/(4mε'²) ≤ 1/(mε'²)`", and the formal bound equals the tighter one.
6. **For `PolyExpr` stretches, "eventually expanding" is equivalent to "expanding for all `n ≥ 2`",** and every such stretch satisfies `n ≤ ℓ(n)`. Also, "PRGs exist" has the same meaning under every Q1 option.
7. **Note #8 is answered by 03b's findings** (#1, #3, #7), and 03b's repair ripples back into 03c's `Collection.glPad`.
8. **Note #9 is answered by 03i's evidence:** the three declarations are free of `sorryAx` at `a3c5fa8b`.

---

## Pending packs

| Pack | With the recommended rulings (Q1-A, Q2-A, Q3-A) | Under the alternatives |
|---|---|---|
| 03d | **Touched, docstrings only:** `PublicKey.lean:797–800` and `:938–943` (#3); optional `PRG.Secure.expand` (#4). Fold these in when 03d pins after S2b; no wait. | Waits under Q1-B/C (PRF.lean `truncate`/`doubling`, Encryption.lean `(P.expands n).le` ×8) and under Q3-B (`glPad_tdpBitScheme_singleBitSecure`). |
| 03i | Unaffected. | Waits under Q3-B (HardCoreGLColl `:229, :293`; HardCoreLemmas' `glPad` machinery) and under Q1-B/C (`expandRedMachine` `hk`, `HardCoreLemmas.lean:533`). |
| 03j | Unaffected. | Waits under Q1-B/C (callers of `truncateTo_*`). |
| 03f2 | Unaffected. | Touched under Q3-C (new instances in RSA.lean, Rabin.lean). |
| 03f1, 03g, 03h, 03k, 03l | **Unaffected under every option.** 03f1's `DiscreteLogHardcore` uses `Collection.HardCore` (03b's), not `glPad`; 03k's `CommitmentLemmas` only imports `HardCore`. | Same. |

- Packs outside the pending list: 03e's `Commitment.lean:445` (`simp [… PRG.oneBit]`) is proof-level only under Q1-B/C. 03a's `Ensembles.lean` mentions Thm 75.4 by name only.
- **03c itself:** its collection section must be re-verified after 03b's major #1 is repaired.

**After the fixes, run** (in the infoview or the gate's replay):
- the four 03c files;
- the new `#print axioms` lines (#6);
- `PRG.Easy.samplable` after dropping the `@[simp]`;
- under Q2-A, `Ensemble.NextBitUnpredictable.pseudorandom`'s axioms.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03c-r1.md =====

# Gate 03c (hard-core bits and PRGs): round 1 resolutions

- **Round 1:** findings `findings/gate03c-findings.md`, verbatim, SHA-256
  `0547776d90b620023b825684a873ebb11f4ec0c3fbf9baa54f02a4da80376a3a`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 1 major (#1), 5 minors,
  5 notes.**
- **Review:** `review/gate03c-review.md`: 9 true, 2 partly true (#1, #4), none false. #1 stays a
  major, not a blocker (no statement of ch. 2–8 is about a stretch-`2n` `PRG`). One severity
  change, proposed by the review: #3 from minor to **major** (the library's own trapdoor
  collections fail `henc`). New tally **0 blockers, 2 majors, 4 minors, 5 notes**. Eight items
  missed by the auditor (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-2 (A), keep `∀ n, n < ℓ(n)` and declare the cost (#1); G3-7 (b),
  drop Thm 75.4's extra hypothesis (#2); G3-7 (c), state `henc`'s cost now (#3); G3-6 (A), approve
  the listed `@[simp]` (#11).
- **Repair:** commit `bc2aab59333e27729c9fbac3052cd650bf62c3aa` (on #198's head
  `c10ed6ace0b991146c0be769313fbbe52d36e25a`), in PR #201 with 03a's
  `e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820`; #201's head
  `0c348ff94cacf24d96d99078c9dd9e328530c8d2` is **not yet merged**, so every "Fixed" below except
  #3 is on #201's branch only. #3 (G3-7 (c)) was done in #198 (`c10ed6ac…`, merged by
  `cdff8890ee4af8eec7d6682963c02041390f52f2`). Evidence `evidence-repairs/03ac/` (replay of the
  97 downstream modules plus `Checks`, the `Checks` axiom print at #201's head, lint 0). Line numbers
  are at #201's head; Lean paths are under `TCSlib/Cryptography/Asymptotic/`.
- **Moved file:** `HardCore.lean`'s collection section (17 declarations, statements unchanged) is
  now `HardCoreCollection.lean`, which `HardCore.lean` imports (#11).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major (not blocker) | **Fixed** (G3-2; docstrings and DESIGN, no statement change). A second Deviation on `PRG` (`Pseudorandom.lean:120–131`, with the module docstring :38–41 and the `expands` field :137–139) states the cost and the routes (`prg_expand` from `PRG.truncate`, `truncateTo_*`, `DoublingPRG`); "`ℓ(n) > n` at every `n`, see `PRG`" in `HardCore.lean:64, 372–377, 441, 452`; DESIGN §2.12 line comment and §5 item 25 (`briefs/pass-shelat/DESIGN.md:714, 1068–1078`). |
| 2 | minor | **Fixed** (G3-7 (b); a strengthening). `Ensemble.NextBitUnpredictable.pseudorandom` no longer takes `hℓ` (`NextBit.lean:682–683`; repair note :657–659), via the machine lemma for every position (:573–577) and the new `prgAdv_eq_zero_of_length_eq_zero` (:453); `stretch_pos`'s attribution fixed (`Pseudorandom.lean:178–180`); DESIGN §2.12 (`DESIGN.md:723`). Both print standard (`evidence-repairs/03ac/checks-axioms.log:241–243, 484`); no Lean consumer. |
| 3 | major (review; was minor) | **Fixed** (G3-7 (c), in #198). `Collection.glPad`'s deviation states the cost (no library candidate satisfies `henc`; `HardCoreCollection.lean:84–91`), as does DESIGN §5 item 18 (`DESIGN.md:1036–1045`); "satisfiable from trapdoor permutations alone" is replaced in `HardCoreCollection.lean:344–347` and `PublicKey.lean:809–812, 952–958`. `henc` itself is unchanged (the per-index form is not formalized, as ruled). |
| 4 | minor (partly true) | **Fixed** (record). DESIGN §2.12 records the shipped one-bit signature and the route through `PRG.truncate`/`PRG.Secure.truncate` (`DESIGN.md:732–737`), as does `prg_expand`'s docstring (`HardCore.lean:445`). The optional `PRG.Secure.expand` corollary is left to 03d (commit message only). |
| 5 | minor | **Fixed.** The sketches of `nextBitProb_nextBitPred_false` (`NextBit.lean:369–379`) and `acceptProb_nextBitHybrid_mix` (:320–325) now go through `uprob_split_bit`'s involution; inventory-ch3 Thm-75.4.2 is annotated (`briefs/pass-shelat/inventory-ch3.md:319–321`). **Recorded here**, as the review asks (the run-3 summary is closed): *P2-3* is the run-3 repair that replaced the 2-to-1 planting map by `uprob_split_bit` (`NextBit.lean:236–243`). |
| 6 | minor | **Fixed.** The eleven prints (`fact_88_4`, `thm_87_3_1/2/3/6/7/8/9`, `not_hardCore_const`, `Ensemble.uniform_nextBitUnpredictable`, `PermCollection.OneWay.glPad_hardCore`) are in `audits/pass-shelat/Checks.lean:559–571`; all standard at #201's head (`checks-axioms.log:485–495`). |
| 7 | note | **Fixed** (docstrings). `HardCoreClaims.lean:14–27` separates the family-level claims (`thm_87_3_1/2/3/9`) from the concrete ones (`fact_88_4`, `thm_87_3_6/7/8`); `thm_87_3_6` (:109–117) places the formal `1/(4mε'²)` between the text's `(1 − 4ε'²)/(4mε'²)` and `1/(mε'²)`, `m` being the `2^k − 1` samples; `thm_87_3_8` (:134–139) notes `m = 2^k`. |
| 8 | note | **No change** in 03c (scope note, answered by 03b's audit of `Collection.HardCore`, #1, #3, #7). After G3-1, `Collection.glPad` proves `encD_decD` (`HardCoreCollection.lean:103–107`); the collection section is re-verified in this closing round. |
| 9 | note | **No change:** answered by 03i's evidence (`evidence/i/axioms.log:13–15`: `glHalf`, `exists_owp_hardCore`, `exists_securePRG_of_owp` standard; replay `sorry=0`). |
| 10 | note | **Fixed.** Remarks for Constr-77.a (Shamir), Claim-78.a and Claim-78.b in `HardCore.lean`'s module docstring (:73–82). Claim-107.c is not formalized (optional, DESIGN §6.2). |
| 11 | note | **Fixed**, with G3-6. New `PRG.easy_iff` (`Pseudorandom.lean:156`), `hardCore_iff`, `PRG.oneBit_stretch`, `PRG.oneBit_G`, `owpPredictorSnoc_eq`, `oneBitStep_eq`, `expandRed_eq` (`HardCore.lean:161, 221, 225, 253, 366, 405`) and `Collection.glBit_eq` (`HardCoreCollection.lean:146`), printed (`Checks.lean:572–580`); `HardCore.lean` split (775 and 353 lines). **Recorded** (G3-6): `PRG.ensemble_X` keeps `@[simp]` (`Pseudorandom.lean:173`), against the review's per-pack advice to drop it. `NextBit.lean` is not split (972 lines; the review did not ask). |
| M1 | (review) the cost was declared in `PRF.lean` | **No change** (observation). The new `PRG` deviation cites `DoublingPRG`, `PRG.truncate` and `PRG.doubling`. |
| M2 | (review) no downstream statement is vacuous | **No change:** #1's escalation test fails, so #1 is not a blocker. |
| M3 | (review) `henc` fails for the library's trapdoors | **Fixed** with #3 (G3-7 (c)). |
| M4 | (review) #1 and #2 interact | **No change:** G3-2 keeps `∀ n`, so the interaction is not triggered; G3-7 (b) removed `hℓ` anyway. |
| M5 | (review) the PDF checks are settled | **No change.** #7's docstring quotes the per-bit bound from the raw extract (`blueprint/src/references/pass-shelat-2010-ch3.raw.md`, about l. 995–997). |
| M6 | (review) "eventually" equals "from 2 on"; "PRGs exist" is unchanged | **No change**; the second remark is in the `PRG` deviation (`Pseudorandom.lean:127–130`, not formalized). |
| M7 | (review) note #8 is answered by 03b | **Recorded** with #8. |
| M8 | (review) note #9 is answered by 03i's evidence | **No change** (see #9). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-r2/03c/repair.diff.txt =====

# Gate 03c, round 2: the repair diff
#
# Section A: every change to this pack's Lean files between the round 1 head a3c5fa8b72e50939822f22364647dc844a3914a0 and the round 2 pin e79397eaf68b156b9db091f464741f6eb75b9c28, whichever repair made it.
# Section B: the rest of the 03c repair commit bc2aab59333e27729c9fbac3052cd650bf62c3aa (in #201): its changes outside this pack's files (consumers, Checks.lean, records).

### --- A: this pack's files, a3c5fa8b72e50939822f22364647dc844a3914a0..e79397eaf68b156b9db091f464741f6eb75b9c28 ---
diff --git a/TCSlib/Cryptography/Asymptotic/HardCore.lean b/TCSlib/Cryptography/Asymptotic/HardCore.lean
index e7e9f538..6e88eaf1 100644
--- a/TCSlib/Cryptography/Asymptotic/HardCore.lean
+++ b/TCSlib/Cryptography/Asymptotic/HardCore.lean
@@ -7,7 +7,7 @@ import TCSlib.Cryptography.Asymptotic.NextBit
 import TCSlib.Cryptography.Asymptotic.Collections
 import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
 import TCSlib.Cryptography.Asymptotic.HardCoreGL
-import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
+import TCSlib.Cryptography.Asymptotic.HardCoreCollection
 import TCSlib.Cryptography.Asymptotic.HardCoreGLFamily
 import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
 import TCSlib.Cryptography.Asymptotic.HardCoreLoops
@@ -30,8 +30,10 @@ one-bit-stretch generator to `ℓ(n)` bits [PS10, Lemma 80.5]; the iterated gene
 for every one-way function `f`, `g(x, r) = (f(x), r)` is one-way and `⟨x, r⟩` is hard-core for
 `g` [PS10, Theorem 87.3], together with the concrete claims of its proof (the oversimplified
 case, the `3/4 + ε` case, the good set, Fact 88.4, Algorithms 88.5 and 89.6, the
-pairwise-independence and union-bound claims, the final bound) and the version for
-collections of (trapdoor) permutations needed by [PS10, Theorem 104.4].
+pairwise-independence and union-bound claims, the final bound; in
+`Asymptotic/HardCoreClaims.lean`) and the version for collections of (trapdoor) permutations
+needed by [PS10, Theorem 104.4] (in `Asymptotic/HardCoreCollection.lean`, which this file
+imports).
 
 Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer is
 the frozen Garg development reused verbatim: `owpPredictor`/`exists_owpPredictor`
@@ -59,17 +61,25 @@ rather than through the next-bit test (Theorem 75.4), which would lose a factor
 **Deviation:** [PS10, Lemma 80.5]: the generator `G'` outputs the bits only (the final seed is
 dropped, as in the text); `G(X_i)` is read seed-first/bit-last as in the text (the concrete
 `prgExt` reads bit-first; `oneBitStep` is the fixed re-encoding); the expansion clause
-`ℓ(n) > n` is an explicit hypothesis. [PS10, Corollary 81.7] lists `ℓ(n) + 1` bits
-`i = 0, …, ℓ(n)` (source error 38) and needs `n ≤ ℓ(n)`.
-
-**Deviation:** [PS10, Theorem 87.3] for collections (unnumbered): the padded collection
-`Collection.glPad F m` pads each element by `|encD_i(default)|` uniform bits; its one-wayness
-and hard-core theorems assume length-regular encodings at generated indices
-(`∀ n r x, |encD_{index n r} x| = m(n)`), which the text's "`|x| = |r|`" presupposes. Its
-hard-core proof uses the encoded-domain Goldreich–Levin lemma
-`HardcoreBit.invProb_guessInverter_enc_pad` (`Asymptotic/GoldreichLevinDomain.lean`): the
-cube lemma does not transfer to a domain `D_i` whose encoding is a strict subset of the cube
-(run-3 audit P4-2).
+`ℓ(n) > n` at every `n` is an explicit hypothesis, see `PRG` (the text's "for any polynomial
+`ℓ`": stretches with `ℓ(0) = 0` or `ℓ(1) = 1` are excluded; gate 03c, finding 1, ruling G3-2).
+[PS10, Corollary 81.7] lists `ℓ(n) + 1` bits `i = 0, …, ℓ(n)` (source error 38) and needs
+`n ≤ ℓ(n)`.
+
+The collection form of [PS10, Theorem 87.3] and its Deviation (the encoding-length hypothesis
+`henc` of `Collection.glPad`) are in `Asymptotic/HardCoreCollection.lean` (moved out of this
+file for size; gate 03c, finding 11).
+
+**Remarks (not formalized; [PS10, §3.3.2], inventory Constr-77.a, Claim-78.a, Claim-78.b).**
+Shamir's generator `G(s) = f^n(s) ‖ ⋯ ‖ f(s) ‖ s` (Constr-77.a) motivates the construction
+and is not formalized. Claim-78.a (for a permutation `f` and a uniform `x`, `f^k(x)` is
+uniform) is an instance of `uprob_comp_equiv` (the uniform distribution is invariant under a
+bijection) applied to the `k`-th iterate of the permutation; it is not stated separately.
+Claim-78.b (unpredictable blocks need not have unpredictable bits: a one-way permutation may
+leave input bits unchanged) has the concrete witness of [Gar26, Claim 2.3] in
+`HardcoreBit/NoFixedBit.lean`: `g(x, y) = f(x_{-y}) ‖ x_y ‖ y` reveals the bits of `y` with
+certainty (`predProb_positionBit`) and each fixed input bit `x_i` with advantage
+`1/(2(n + 1))` (`predProb_fixedBitPredictor`).
 
 ## Main definitions
 
@@ -85,7 +95,7 @@ cube lemma does not transfer to a domain `D_i` whose encoding is a strict subset
 * `TCSlib.Cryptography.FunFamily.glPad`, `FunFamily.glBit`, `FunFamily.glInverter` — the
   Goldreich–Levin setting `g(x, r) = (f(x), r)`, `h(x, r) = ⟨x, r⟩` [PS10, Theorem 87.3].
 * `TCSlib.Cryptography.Collection.glPad`, `Collection.glBit`, `PermCollection.glPad`,
-  `TrapdoorCollection.glPad` — the collection form.
+  `TrapdoorCollection.glPad` — the collection form (in `Asymptotic/HardCoreCollection.lean`).
 
 ## Main results
 
@@ -106,9 +116,13 @@ cube lemma does not transfer to a domain `D_i` whose encoding is a strict subset
   `Asymptotic/HardCorePermutation.lean` (run-3 audit P4-1).
 * `TCSlib.Cryptography.goldreich_levin_coll`, `Collection.OneWay.glPad`,
   `Collection.OneWay.glPad_hardCore`, `PermCollection.OneWay.glPad`,
-  `TrapdoorCollection.OneWay.glPad` [PS10, Theorem 87.3, collection form].
+  `TrapdoorCollection.OneWay.glPad` [PS10, Theorem 87.3, collection form] (in
+  `Asymptotic/HardCoreCollection.lean`).
 * `TCSlib.Cryptography.not_hardCore_const` — a constant predicate is never hard-core
   (non-vacuity of the hardness clause of Definition 78.3).
+* `TCSlib.Cryptography.hardCore_iff`, `PRG.oneBit_stretch`, `PRG.oneBit_G`,
+  `owpPredictorSnoc_eq`, `oneBitStep_eq`, `expandRed_eq` — the unfoldings of the definitions
+  of this file (gate 03c, finding 11).
 
 ## References
 
@@ -141,6 +155,17 @@ def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) 
   ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
     ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n
 
+/-- **Hard-core unfolded** [PS10, Definition 78.3]: `h` is hard-core for `f` iff some
+polynomial-time `H` computes `[h n x]` from `⟨1^n, x⟩`, and for every non-uniform PPT `A` some
+negligible `ε` bounds `Pr[x ← {0,1}^{inLen n} : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)` for all `n`. -/
+theorem hardCore_iff (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) :
+    HardCore 𝓕 h ↔
+      (∃ H : List Bool → List Bool, PolyTimeComputable H ∧
+        ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
+      ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
+        ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n :=
+  Iff.rfl
+
 /-- The efficiency clause of a hard-core predicate [PS10, Definition 78.3 (1)]. -/
 theorem HardCore.easy {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
     (hh : HardCore 𝓕 h) :
@@ -192,6 +217,14 @@ def PRG.oneBit (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) : PRG wh
   G := G
   expands n := Nat.lt_succ_self n
 
+/-- Field equation: the stretch of `PRG.oneBit G` is `n + 1`. -/
+theorem PRG.oneBit_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) :
+    (PRG.oneBit G).stretch = .add .var (.const 1) := rfl
+
+/-- Field equation: the generator of `PRG.oneBit G` at seed length `n` is `G n`. -/
+theorem PRG.oneBit_G (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (n : ℕ)
+    (s : Fin n → Bool) : (PRG.oneBit G).G n s = G n s := rfl
+
 /-- The generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4] for a permutation family `f`
 and a predicate `h`: output length `n + 1`, the bit `h(s)` in the last position. -/
 def owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : PRG :=
@@ -215,6 +248,14 @@ def owpPredictorSnoc {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ 
   fun y c => owpPredictor (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r)
     flip (y, ()) c
 
+/-- Unfolding: `owpPredictorSnoc D flip` is the concrete `owpPredictor` [Gar26, proof of
+Theorem 3.2] for the distinguisher `(y, (), σ) ↦ D(y ‖ σ)`, at the point `(y, ())`. -/
+theorem owpPredictorSnoc_eq {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool)
+    (flip : Bool) (y : Fin n → Bool) (c : Bool × ρ) :
+    owpPredictorSnoc D flip y c = owpPredictor
+      (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r) flip (y, ()) c :=
+  rfl
+
 /-- **PRG from a one-way permutation, concrete form** [PS10, Theorem 79.4; Gar26, Theorem 3.2]:
 if `D` distinguishes `f(s) ‖ B(s)` from a uniform `(n+1)`-bit string with advantage `ε`, then
 for one sign `flip` the predictor `owpPredictorSnoc D flip` predicts `B(s)` from `f(s)` with
@@ -321,13 +362,21 @@ def oneBitStep {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) :
     (Fin n → Bool) → Bool × (Fin n → Bool) :=
   fun s => (G s (Fin.last n), Fin.init (G s))
 
+/-- Unfolding: one step outputs the last bit of `G(s)` and the next seed `init G(s)`. -/
+theorem oneBitStep_eq {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (s : Fin n → Bool) :
+    oneBitStep G s = (G s (Fin.last n), Fin.init (G s)) := rfl
+
 /-- The **expanded generator** `G'(s) = b_1 ⋯ b_{ℓ(n)}` of [PS10, Lemma 80.5]: `X_0 = s`,
 `X_{i+1} ‖ b_{i+1} ← G(X_i)`, output the `ℓ(n)` bits (the final seed is dropped). Formally
 the first component of the concrete `prgExt (oneBitStep (G n)) (ℓ n)` [Gar26,
-Construction 3.1]; the expansion clause `n < ℓ(n)` is the hypothesis `hℓ`.
+Construction 3.1]; the expansion clause `n < ℓ(n)`, at every `n` (see `PRG`), is the
+hypothesis `hℓ`.
 
 **Deviation:** `G(X_i)` is read seed-first/bit-last as in the text; the output drops the
-final seed (as in the text), the concrete `prgExt` keeps it. -/
+final seed (as in the text), the concrete `prgExt` keeps it. The text's "for any polynomial
+`ℓ`" is restricted to `ℓ(n) > n` at every `n`, `n = 0` included (the cost of `PRG.expands`:
+`2n` and `n^c` are excluded, `2n + 1` and `n^c + 1` are not; gate 03c, finding 1, ruling
+G3-2). -/
 def PRG.expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
     (hℓ : ∀ n, n < ℓ.eval n) : PRG where
   stretch := ℓ
@@ -350,6 +399,14 @@ def expandRed {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) →
     (D : (Fin l → Bool) → ρ → Bool) : (Fin (n + 1) → Bool) → (Fin l → Bool) × ρ → Bool :=
   fun T c => prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c
 
+/-- Unfolding: `expandRed G l k D` on `T` is the concrete hybrid-`k` reduction `prgExtRed`
+[Gar26, Theorem 3.1] of `oneBitStep G` against `D ∘ fst`, on the re-encoded input
+`(T_{n+1}, T_1 ⋯ T_n)`. -/
+theorem expandRed_eq {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (l k : ℕ)
+    (D : (Fin l → Bool) → ρ → Bool) (T : Fin (n + 1) → Bool) (c : (Fin l → Bool) × ρ) :
+    expandRed G l k D T c =
+      prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c := rfl
+
 /-- Dropping an independent uniform component from a generator's output does not change
 PRG advantages: `prgAdv (fst ∘ X) D = prgAdv X (D ∘ fst)` (the projection is a deterministic
 post-processing and the projection of a uniform pair is uniform). -/
@@ -381,11 +438,19 @@ theorem exists_expandRed_ge {ρ : Type*} [Fintype ρ] {n : ℕ}
     (prgExtRed (oneBitStep G) l k fun z r => D z.1 r)
 
 /-- **Expansion of a PRG** [PS10, Lemma 80.5]: if the one-bit-stretch generator `G` is a PRG
-then so is its `ℓ(n)`-bit expansion `G'` (`ℓ(n) > n`).
+then so is its `ℓ(n)`-bit expansion `G'` (`ℓ(n) > n` at every `n`, see `PRG`).
+
+The input is a one-bit-stretch `G : {0,1}^n → {0,1}^{n+1}`, as in the text ("Let
+`G : {0,1}^n → {0,1}^{n+1}` be a PRG"), not a general `P : PRG` (the shape recorded at DESIGN
+§2.12); a general secure `P` reaches it through its truncation to `n + 1` bits, `PRG.truncate`
+with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` (`Asymptotic/PRF.lean`; gate 03c,
+finding 4).
 
 **Deviation:** `G'` drops the final seed and reads `G(X_i)` seed-first, as the text; the
 text's proof interchanges `m(n)` and `ℓ(n)`, starts the hybrids at `i = 1` (they must start
-at `0`) and reads `M(y)` bit-first against the construction (source error 34).
+at `0`) and reads `M(y)` bit-first against the construction (source error 34). The text's
+"for any polynomial `ℓ`" is restricted to `ℓ(n) > n` at every `n`, `n = 0` included (the cost
+of `PRG.expands`; gate 03c, finding 1, ruling G3-2); the security half uses only `ℓ(n) > 0`.
 
 **Proof sketch.** *Easy:* from `h.1 = ⟨F, hF, hFs⟩`, `G'` is computed by
 `polyTimeComputable_iterateEmit` with step `x ↦ (F x).dropLast` (the next seed,
@@ -707,275 +772,4 @@ theorem goldreich_levin {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
     𝓕.glPad.StrongOneWay ∧ HardCore 𝓕.glPad 𝓕.glBit :=
   ⟨h.glPad, h.glPad_hardCore⟩
 
-/-! ## Goldreich–Levin for collections [PS10, Theorem 87.3, collection form] -/
-
-namespace Collection
-
-variable (F : Collection)
-
-/-- The **padded collection** `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] for a
-collection `{f_i : D_i → R_i}` whose elements have encoding length `m(n)` at the indices
-generated at parameter `n` (`henc`): the domain `D'_i = D_i × {0,1}^{|encD_i(default)|}` (the
-padding has the length of the encoded elements), elements encoded as `⟨encD_i x, r⟩`, the
-same index generator `Gen`, the sampler `Sample'(1^n, i) = ⟨Sample(1^n, i), r⟩` with `m(n)`
-fresh coins `r`, and the evaluator `⟨i, ⟨x, r⟩⟩ ↦ ⟨eval ⟨i, x⟩, r⟩`. The sampler's outputs
-decode (`sample_spec`): the first component by `F.sample_spec`, the padding because it has
-exactly `m(n) = |encD_i(default)|` bits by `henc`.
-
-Repair (run-3 audit P3-1): the hypothesis `henc` (previously carried by the theorems only) is
-now an argument of the definition, since without it the padding of the sampled string need not
-have the length the decoder expects and `Collection.sample_spec` would fail.
-
-**Deviation:** the text's "`|x| = |r|`" presupposes that all elements of `D_i` have the same
-encoding length; `glPad` assumes `|encD_i x| = m(n)` at generated indices (`henc`). -/
-noncomputable def glPad (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
-    Collection where
-  D i := F.D i × (Fin (F.encD i default).length → Bool)
-  encD i z := pairEncode (F.encD i z.1) (List.ofFn z.2)
-  decD i w := match pairDecode w with
-    | some (a, b) => match F.decD i a, decodeFin (F.encD i default).length b with
-      | some x, some r => some (x, r)
-      | _, _ => none
-    | none => none
-  decD_encD i z := by simp [pairDecode_pairEncode, F.decD_encD, decodeFin_ofFn]
-  f i z := pairEncode (F.f i z.1) (List.ofFn z.2)
-  gen := F.gen
-  gen_uniform := F.gen_uniform
-  sample := NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)
-  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
-  eval w := pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w))))
-    (pairSndD (pairSndD w))
-  eval_poly := (F.eval_poly.comp (polyTimeComputable_pairFstD.pairEncode
-    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
-    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
-  eval_spec i z := by simp [F.eval_spec]
-  sample_spec n r s := by
-    obtain ⟨⟨s₁, s₂⟩, hs⟩ := (Fin.appendEquiv (F.sample.coins.eval n) (m.eval n)).surjective s
-    have hofn : List.ofFn s = List.ofFn s₁ ++ List.ofFn s₂ := by
-      rw [← hs]
-      exact List.ofFn_fin_append s₁ s₂
-    have hA : (List.ofFn s).take (F.sample.coinLen n) = List.ofFn s₁ := by
-      rw [hofn, List.take_left' List.length_ofFn]
-    have hB : (List.ofFn s).drop (F.sample.coinLen n) = List.ofFn s₂ := by
-      rw [hofn, List.drop_left' List.length_ofFn]
-    obtain ⟨x, hx, hev⟩ := F.sample_spec n r s₁
-    have hL : (F.encD (pairFstD (F.gen.runAt n [] r)) default).length = m.eval n := henc n r default
-    have hs₂ : List.ofFn s₂ = List.ofFn
-        fun j : Fin (F.encD (pairFstD (F.gen.runAt n [] r)) default).length => s₂ (Fin.cast hL j) :=
-      List.ofFn_congr hL.symm s₂
-    refine ⟨(x, fun j => s₂ (Fin.cast hL j)), ?_, ?_⟩
-    · simp only [glPadSample_runAt, hA, hB, pairDecode_pairEncode, ← NUPPT.runAt_eq, hx, hs₂,
-        decodeFin_ofFn]
-    · simp only [glPadSample_runAt, hA, hB, pairFstD_pairEncode, pairSndD_pairEncode,
-        ← NUPPT.runAt_eq, hev, hs₂]
-
-/-- The predicate `h_i(x, r) = ⟨x, r⟩` for the padded collection: the inner product of the
-encoding of `x` (padded or truncated to the padding length) with `r`. -/
-def glBit : ∀ i, F.D i × (Fin (F.encD i default).length → Bool) → Bool :=
-  fun i z => HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2
-
-variable {F} in
-/-- Unfolding: the padded collection keeps the index generator. -/
-theorem glPad_gen (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
-    (F.glPad m henc).gen = F.gen := rfl
-
-variable {F} in
-/-- Unfolding: `g_i(x, r) = ⟨f_i(x), r⟩`. -/
-theorem glPad_f (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
-    (i : List Bool) (z : (F.glPad m henc).D i) :
-    (F.glPad m henc).f i z = pairEncode (F.f i z.1) (List.ofFn z.2) := rfl
-
-variable {F} in
-/-- Unfolding: the sampler of the padded collection runs `Sample(1^n, i)` on its first
-`|Sample's coins|` coins and appends the remaining coins. -/
-theorem glPad_sample_runAtL (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
-    (n : ℕ) (i r : List Bool) :
-    (F.glPad m henc).sample.runAtL n i r =
-      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)) := by
-  simp only [glPad, NUPPT.runAtL, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
-    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
-    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
-    NUPPT.coinLen]
-
-variable {F} in
-/-- Unfolding: the decoder of the padded collection is `glPadDecode` at the padding length
-`|encD_i(default)|` (propositional: the two `match` expressions are compiled separately). -/
-theorem glPad_decD_eq (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
-    (i : List Bool) : (F.glPad m henc).decD i = glPadDecode F i (F.encD i default).length := by
-  funext w
-  unfold Collection.glPad glPadDecode
-  dsimp only
-  cases pairDecode w with
-  | none => rfl
-  | some ab =>
-    obtain ⟨a, b⟩ := ab
-    dsimp only
-    cases F.decD i a <;> cases decodeFin (F.encD i default).length b <;> rfl
-
-/-- **The padded collection is one-way** ([PS10, Theorem 87.3], collection form, first clause):
-if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at the
-indices generated at parameter `n`, then `F.glPad m` is a collection of one-way functions.
-
-**Proof sketch.** *Sampling:* with `h.sampleClose = ⟨δ, hδ, hS⟩`, at index `i = index n r`
-the decoded sampler output is `(decD i (Sample(1^n, i; s₁)), decodeFin _ (ofFn s₂))` on the
-coin split `splitCoins (Sample.coins n) (m n)` (`glPad_sample_runAtL`, `List.ofFn` of the
-split, `uprob_comp_equiv`); `henc` gives `(encD i default).length = m n`, so the second
-component decodes exactly (`decodeFin_ofFn`) and `StatClose.prod (hS n r) (StatClose.refl _)`
-with `StatClose.map` to the pair gives `SampleClose δ`. *Hard:* for `A : NUPPT` against
-`F.glPad m`, the inverter `B` against `F`: coins `m + A.coins` (`NUPPT.exists_split m`, the
-first `m n` coins are `r`), on `⟨1^n, ⟨i, y⟩⟩` it calls `A` once on `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`
-(`NUPPT.exists_comp`, `NUPPT.exists_seq`) and returns the first component of the answer
-(`pairFstD`). Then `(F.glPad m).invProbAt A n ≤ F.invProbAt B n`: unfold both `uexp` over
-`Gen`'s coins (`OneWay.uexp_mono`), split the inner `uprob` over `D_i × ({0,1}^{m n} × A.Coins n)`
-against `D_i × B.Coins n` by `uprob_comp_equiv` on `splitCoins`, and `uprob_mono`: a decoded
-answer `(x', r')` with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)`
-(`pairEncode_injective`). `Negligible.mono` with `h.hard B`. -/
-theorem OneWay.glPad {F : Collection} (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
-    (h : F.OneWay) : (F.glPad m henc).OneWay := by
-  obtain ⟨δ, hδ, hS⟩ := h.sampleClose
-  refine ⟨⟨δ, hδ, fun n r => ?_⟩, fun A => ?_⟩
-  · have key := statClose_glPadSampler F m (F.glPad m henc).sample rfl (glPad_sample_runAtL m henc)
-      hS n r _ (henc n r default)
-    simp only [glPad_decD_eq] at key ⊢
-    exact key
-  · refine (h.hard (glPadCollInvMachine A m)).mono ⟨0, fun n _ => ?_⟩
-    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
-    have key := glPad_invProbAt_le F m A n (fun r => (F.encD (F.index n r) default).length)
-      (fun r => henc n r default)
-    unfold Collection.invProbAt at key ⊢
-    simp only [glPad_decD_eq]
-    exact key
-
-/-- **`⟨x, r⟩` is hard-core for the padded collection** ([PS10, Theorem 87.3], collection form,
-second clause; inventory Thm-87.3.coll, needed by Theorem 104.4): if `F` is a collection of
-one-way functions with encoding length `m(n)` at generated indices, then
-`h_i(x, r) = ⟨encD_i x, r⟩` is a hard-core predicate for `F.glPad m` (`Collection.HardCore`).
-
-Repair (run-3 audit P4-2): statement unchanged. The run-2 sketch transferred the cube lemma
-`HardcoreBit.invProb_guessInverter` to `D_i` by "identifying `D_i` with `{0,1}^{m n}` through
-the injective encoding"; that step is invalid — the image of `encD_i` is in general a strict
-subset of the cube (`Z_N^*`, `QR_N`), the uniform `x ∈ D_i` is not a uniform cube element and
-the predictor's behaviour off the image is uncontrolled. The transfer is replaced by the
-encoded-domain lemma `HardcoreBit.invProb_guessInverter_enc_pad`
-(`Asymptotic/GoldreichLevinDomain.lean`), stated for `x` uniform on an arbitrary finite type
-with an arbitrary encoding into `{0,1}^m`.
-
-**Proof sketch.** *Easy:* `⟨i, ⟨a, b⟩⟩ ↦ ipFun ⟨padToLen a b, b⟩` — pad `a = encD_i x` to the
-length of `b = r` and apply the inner-product evaluator (`exists_glBitCollEvaluator`,
-`Asymptotic/HardCoreGLColl.lean`). *Hard:* `glColl_negligible` with the padding length
-`L n r = |encD_i(default)| = m(n)` (`henc`) and the one-wayness of the padded collection
-(`OneWay.glPad`, its inversion experiment rewritten by `glPad_decD_eq`): by contradiction,
-`not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ E_r[Pr[A(1^n, ⟨i, ⟨f_i x, r⟩⟩) = ⟨encD_i x, r⟩]]`
-infinitely often; the good indices (`HardcoreBit.half_le_uprob_threshold`) have per-index
-success `≥ 1/2 + n^{−c}/2`, where `HardcoreBit.invProb_guessInverter_enc_pad` with
-`enc := padFin (m n) ∘ encD_i` and the hard-wired `k(n) = size (8 m(n) n^{2c})` (`glKc`) makes
-the recovery procedure of [PS10, Algorithm 89.6] output `encD_i x` with probability
-`≥ ε/(4·2^{k(n)})`, `ε = n^{−c}/2`; the inverter `glCollMachine` (the recovery machine `glMachine`
-on the pre-processed predictor `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`, output `⟨x', r⟩`) realises it
-(`glColl_uprob_le`); averaging over the good indices (`HardcoreBit.uprob_mul_le_uexp`) gives
-inversion probability `≥ ε²/(4·2^{k(n)})`, inverse polynomial infinitely often, contradicting
-`(OneWay.glPad m henc h).hard`. -/
-theorem OneWay.glPad_hardCore {F : Collection} (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
-    (h : F.OneWay) : (F.glPad m henc).HardCore F.glBit := by
-  refine ⟨?_, fun A => ?_⟩
-  · obtain ⟨H, hH, hHx⟩ := exists_glBitCollEvaluator F
-    exact ⟨H, hH, fun i x => hHx i x.1 x.2⟩
-  · have hmax : ∀ x : ℝ, x ≤ 1 / 2 + max 0 (x - 1 / 2) := fun x => by
-      linarith [le_max_right (0 : ℝ) (x - 1 / 2)]
-    refine ⟨_, glColl_negligible F m (fun n r => (F.encD (F.index n r) default).length)
-      (fun n r => henc n r default) henc A (fun B => ?_), fun n => hmax _⟩
-    have key := (OneWay.glPad m henc h).hard B
-    unfold Collection.invProbAt at key
-    simp only [glPad_decD_eq] at key
-    exact key
-
-end Collection
-
-/-- **Goldreich–Levin for collections** ([PS10, Theorem 87.3], the collection form the text
-uses for Theorem 104.4 and Chapter 4): for a collection `F` of one-way functions with
-encoding length `m(n)` at generated indices, `g_i(x, r) = (f_i(x), r)` is a collection of
-one-way functions and `⟨x, r⟩` is hard-core for it. -/
-theorem goldreich_levin_coll {F : Collection} (m : PolyExpr)
-    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
-    (h : F.OneWay) : (F.glPad m henc).OneWay ∧ (F.glPad m henc).HardCore F.glBit :=
-  ⟨Collection.OneWay.glPad m henc h, Collection.OneWay.glPad_hardCore m henc h⟩
-
-/-- The padded collection of a collection of permutations is a collection of permutations
-[PS10, Theorem 87.3, "(OWP)"]: `g_i = perm_i × id` on `D_i × {0,1}^{|encD_i default|}`. -/
-noncomputable def PermCollection.glPad (P : PermCollection) (m : PolyExpr)
-    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
-    PermCollection :=
-  { P.toCollection.glPad m henc with
-    perm := fun i => (P.perm i).prodCongr (Equiv.refl _)
-    f_perm := fun i z => by simp [Collection.glPad, P.f_perm] }
-
-/-- Unfolding: the underlying collection of `P.glPad m henc` is `P.toCollection.glPad m henc`. -/
-theorem PermCollection.glPad_toCollection (P : PermCollection) (m : PolyExpr)
-    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
-    (P.glPad m henc).toCollection = P.toCollection.glPad m henc := rfl
-
-/-- **The padded permutation collection is one-way** when the original is (collection form of
-[PS10, Theorem 87.3] for Definition 55.1). -/
-theorem PermCollection.OneWay.glPad {P : PermCollection} (m : PolyExpr)
-    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
-    (h : P.OneWay) : (P.glPad m henc).OneWay :=
-  Collection.OneWay.glPad m henc h
-
-/-- **`⟨x, r⟩` is hard-core for the padded permutation collection**. -/
-theorem PermCollection.OneWay.glPad_hardCore {P : PermCollection} (m : PolyExpr)
-    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
-    (h : P.OneWay) : (P.glPad m henc).toCollection.HardCore P.glBit :=
-  Collection.OneWay.glPad_hardCore m henc h
-
-/-- The padded collection of a collection of trapdoor permutations is a collection of
-trapdoor permutations [PS10, Theorem 87.3 for Definition 56.1, as used in Theorem 104.4]:
-`Inv'(1^n, ⟨t, ⟨y, r⟩⟩) = ⟨Inv(1^n, ⟨t, y⟩), r⟩`.
-
-**Proof sketch** (of `inv_spec`). Unfold the activation of the `ofPolyTimeUniform` machine
-(`NUPPT.output_ofPolyTime`, the layout projections); `T.inv` is uniform so its activation is
-its output on the layout with empty advice; `T.inv_spec` decodes the first component to
-`(perm i).symm y.1` and `decodeFin_ofFn` the second to `y.2`. -/
-noncomputable def TrapdoorCollection.glPad (T : TrapdoorCollection) (m : PolyExpr)
-    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
-    TrapdoorCollection :=
-  { T.toPermCollection.glPad m henc with
-    inv := NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins
-    inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
-    inv_spec := fun n r y s => by
-      have hspec := T.inv_spec n r y.1 s
-      simp only [NUPPT.runAt, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime, glPadInvFun,
-        NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
-        pairFstD_pairEncode, pairSndD_pairEncode, PermCollection.glPad, Collection.glPad,
-        pairDecode_pairEncode, decodeFin_ofFn, T.inv_uniform n] at hspec ⊢
-      rw [hspec]
-      rfl }
-
-/-- Unfolding: the underlying permutation collection of `T.glPad m henc` is
-`T.toPermCollection.glPad m henc`. -/
-theorem TrapdoorCollection.glPad_toPermCollection (T : TrapdoorCollection) (m : PolyExpr)
-    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
-    (T.glPad m henc).toPermCollection = T.toPermCollection.glPad m henc := rfl
-
-/-- **The padded trapdoor collection is one-way** when the original is ([PS10, Theorem 87.3]
-for Definition 56.1 (5)). -/
-theorem TrapdoorCollection.OneWay.glPad {T : TrapdoorCollection} (m : PolyExpr)
-    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
-    (h : T.OneWay) : (T.glPad m henc).OneWay :=
-  Collection.OneWay.glPad m henc h
-
-/-- **`⟨x, r⟩` is hard-core for the padded trapdoor collection**: the hypothesis "trapdoor
-permutations with a hard-core predicate" of [PS10, Theorem 104.4] is satisfiable from
-trapdoor permutations alone. -/
-theorem TrapdoorCollection.OneWay.glPad_hardCore {T : TrapdoorCollection} (m : PolyExpr)
-    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
-    (h : T.OneWay) : (T.glPad m henc).toCollection.HardCore T.glBit :=
-  Collection.OneWay.glPad_hardCore m henc h
-
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean b/TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean
index 7dcd070b..d7f7e716 100644
--- a/TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean
+++ b/TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean
@@ -14,11 +14,16 @@ set_option autoImplicit false
 
 The concrete claims of the proof of [PS10, Theorem 87.3] (§3.4.3): the oversimplified case,
 the `3/4 + ε` case, the good set, Fact 88.4, the pairwise-independence and union-bound
-claims about Algorithm 89.6, and the final bound — each the family-level instance
-(`FunFamily.glPad`, `FunFamily.glBit`, `FunFamily.glInverter` of
-`TCSlib.Cryptography.Asymptotic.HardCore`) of the corresponding concrete lemma of the Garg
-layer (`TCSlib/Cryptography/HardcoreBit/*`), through the bridges `FunFamily.predProb_glPad`
-and `FunFamily.invProb_glInverter`. (Moved out of `Asymptotic/HardCore.lean` for size; the
+claims about Algorithm 89.6, and the final bound — each a re-export of the corresponding
+concrete lemma of the Garg layer (`TCSlib/Cryptography/HardcoreBit/*`). The claims about
+the prediction and inversion experiments of `g` (`thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`,
+`thm_87_3_9`) are stated at the family level (`FunFamily.glPad`, `FunFamily.glBit`,
+`FunFamily.glInverter` of `TCSlib.Cryptography.Asymptotic.HardCore`), through the bridges
+`FunFamily.predProb_glPad` and `FunFamily.invProb_glInverter`; the claims about the inner
+product and the samples of Algorithm 89.6 (`fact_88_4`, `thm_87_3_6`, `thm_87_3_7`,
+`thm_87_3_8`) do not involve the family and are stated concretely, for an arbitrary
+`f : {0,1}^n → β` (gate 03c, finding 7). The declaration names encode the inventory ids
+(Thm-87.3.x), not [PS10] numbers. (Moved out of `Asymptotic/HardCore.lean` for size; the
 statements are those of the audited statement phase.)
 
 ## Main definitions
@@ -54,8 +59,9 @@ The setting (inventory Thm-87.3.c) is `FunFamily.glPad`, `FunFamily.glBit`,
 `secProb` (`Pr_r[A(f(x), r) = ⟨x, r⟩]` for a fixed `x`). Algorithm 88.5 is
 `HardcoreBit.majorityInverter` (`majorityRecover`, `trialBit`); Algorithm 89.6 is
 `HardcoreBit.guessInverter` (`guessRecover`, the subroutine `C` realised by guessing the
-`k = log m` bits `b'_j` and forming subset sums). Each claim below is the family-level
-instance of the corresponding concrete lemma. -/
+`k = log m` bits `b'_j` and forming subset sums). Each claim below re-exports the
+corresponding concrete lemma: at the family level for the claims about `g`, concretely for
+`fact_88_4` and `thm_87_3_6/7/8`. -/
 
 /-- **Fact 88.4** [PS10]: `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` (bit strings as a Boolean ring, `+` is
 XOR); the concrete `HardcoreBit.ip_add`. -/
@@ -102,9 +108,13 @@ theorem thm_87_3_3 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
 
 /-- **Pairwise-independent samples suffice** [PS10, §3.4.3; inventory Thm-87.3.6]: for a good
 `x` (`secProb ≥ 1/2 + ε/2`) and `k ≥ 1`, each bit of the ideal recovery procedure (correct
-guesses `b_L = ⟨x, S_L⟩`) is wrong with probability at most `1/(ε²(2^k − 1))` — the text's
-`1/(mε'²)` with `m = 2^k − 1` nonempty subsets and `ε' = ε/2`, by the pairwise-independent
-sampling inequality (`chebyshev_pairwise`); the concrete `uprob_idealRecover_ne_le`. -/
+guesses `b_L = ⟨x, S_L⟩`) is wrong with probability at most `1/(ε²(2^k − 1))`, by the
+pairwise-independent sampling inequality (`chebyshev_pairwise`); the concrete
+`uprob_idealRecover_ne_le`, stated for an arbitrary `f`. The text bounds this probability by
+`(1 − 4ε'²)/(4mε'²) ≤ 1/(mε'²)` with `ε' = ε/2`; the formal `1/(ε²(2^k − 1)) = 1/(4mε'²)` lies
+between the two, with `m` read as the number `2^k − 1` of samples, one per nonempty `L ⊆ [k]`
+(the text draws the `m − 1` samples `r_1, …, r_{m−1}` from `log m` seeds and writes `m`; its
+`m` is the `2^k` of `thm_87_3_8`). -/
 theorem thm_87_3_6 {n : ℕ} {β ρ : Type*} [Fintype ρ] [Nonempty ρ] (f : (Fin n → Bool) → β)
     (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (hk : 0 < k) (x : Fin n → Bool) (i : Fin n)
     {ε : ℝ} (hε : 0 < ε) (hx : 1 / 2 + ε / 2 ≤ HardcoreBit.secProb f A x) :
@@ -125,7 +135,8 @@ theorem thm_87_3_7 {n k : ℕ} :
 [PS10, §3.4.3; inventory Thm-87.3.8]: the guessed bits `b'_1 ⋯ b'_k` equal `⟨x, s_1⟩ ⋯ ⟨x, s_k⟩`
 with probability `1/2^k` (`uprob_guess_eq`), and under that event the recovery procedure
 computes `b_L = ⟨x, S_L⟩` for every `L`, i.e. it is the ideal procedure
-(`guessRecover_correct_guess`). -/
+(`guessRecover_correct_guess`); stated for an arbitrary `f`. Here `m = 2^k` is the text's `m`
+(`log m` guessed bits), while `thm_87_3_6` counts the `2^k − 1` samples. -/
 theorem thm_87_3_8 {n : ℕ} {β ρ : Type*} [Fintype ρ] (f : (Fin n → Bool) → β)
     (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (x : Fin n → Bool) (s : Fin k → Fin n → Bool)
     (cs : Fin n → HardcoreBit.NESubset k → ρ) :
diff --git a/TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean b/TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean
new file mode 100644
index 00000000..cf45e6d0
--- /dev/null
+++ b/TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean
@@ -0,0 +1,353 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
+import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Goldreich–Levin for collections
+
+The collection form of the Goldreich–Levin theorem [PS10, Theorem 87.3], the one the text uses
+for [PS10, Theorem 104.4] and Chapter 4: for a collection `{f_i : D_i → R_i}` of one-way
+functions, the padded collection `g_i(x, r) = (f_i(x), r)` is a collection of one-way functions
+and `⟨x, r⟩` is hard-core for it; and the same for collections of permutations and of trapdoor
+permutations. The machine side is `Asymptotic/HardCoreGLColl.lean` and
+`Asymptotic/HardCoreLemmas.lean`. (Moved out of `Asymptotic/HardCore.lean` for size, gate 03c,
+finding 11; the declarations, their names and statements are unchanged, and `HardCore.lean`
+imports this file, so its importers see them as before.)
+
+**Deviation:** [PS10, Theorem 87.3] for collections (unnumbered): the padded collection
+`Collection.glPad F m` pads each element by `|encD_i(default)|` uniform bits; its one-wayness
+and hard-core theorems assume length-regular encodings at generated indices
+(`∀ n r x, |encD_{index n r} x| = m(n)`), which the text's "`|x| = |r|`" presupposes, at the
+cost stated at `Collection.glPad` (no candidate of the library satisfies it as parametrized;
+gate 03c, finding 3, ruling G3-7c). Its hard-core proof uses the encoded-domain
+Goldreich–Levin lemma `HardcoreBit.invProb_guessInverter_enc_pad`
+(`Asymptotic/GoldreichLevinDomain.lean`): the cube lemma does not transfer to a domain `D_i`
+whose encoding is a strict subset of the cube (run-3 audit P4-2).
+
+## Main definitions
+
+* `TCSlib.Cryptography.Collection.glPad`, `TCSlib.Cryptography.Collection.glBit` — the padded
+  collection `g_i(x, r) = (f_i(x), r)` and the predicate `⟨x, r⟩`.
+* `TCSlib.Cryptography.PermCollection.glPad`, `TCSlib.Cryptography.TrapdoorCollection.glPad` —
+  the padded collection of (trapdoor) permutations.
+
+## Main results
+
+* `TCSlib.Cryptography.goldreich_levin_coll`, `TCSlib.Cryptography.Collection.OneWay.glPad`,
+  `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` [PS10, Theorem 87.3, collection form].
+* `TCSlib.Cryptography.PermCollection.OneWay.glPad`,
+  `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore`,
+  `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad`,
+  `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` — the (trapdoor) permutation
+  forms, for [PS10, Theorem 104.4].
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+  (§2.5: Definition 41.1; §2.10: Definition 55.1; §2.11: Definition 56.1; §3.4.2–3.4.3:
+  Theorem 87.3; §3.10: Theorem 104.4.)
+* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
+  draft of 22 January 2026, §2.5 (Theorem 2.3).
+* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
+-/
+
+namespace TCSlib.Cryptography
+
+open Complexity Turing Finset
+
+/-! ## Goldreich–Levin for collections [PS10, Theorem 87.3, collection form] -/
+
+namespace Collection
+
+variable (F : Collection)
+
+/-- The **padded collection** `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] for a
+collection `{f_i : D_i → R_i}` whose elements have encoding length `m(n)` at the indices
+generated at parameter `n` (`henc`): the domain `D'_i = D_i × {0,1}^{|encD_i(default)|}` (the
+padding has the length of the encoded elements), elements encoded as `⟨encD_i x, r⟩`, the
+same index generator `Gen`, the sampler `Sample'(1^n, i) = ⟨Sample(1^n, i), r⟩` with `m(n)`
+fresh coins `r`, and the evaluator `⟨i, ⟨x, r⟩⟩ ↦ ⟨eval ⟨i, x⟩, r⟩`. The sampler's outputs
+decode (`sample_spec`): the first component by `F.sample_spec`, the padding because it has
+exactly `m(n) = |encD_i(default)|` bits by `henc`.
+
+Repair (run-3 audit P3-1): the hypothesis `henc` (previously carried by the theorems only) is
+now an argument of the definition, since without it the padding of the sampled string need not
+have the length the decoder expects and `Collection.sample_spec` would fail.
+
+**Deviation:** the text's "`|x| = |r|`" presupposes that all elements of `D_i` have the same
+encoding length; `glPad` assumes `|encD_i x| = m(n)` at generated indices (`henc`). Cost (gate
+03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly increasing, so an index
+generated at two parameters forces `m` constant, and no candidate of the library satisfies `henc`
+as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements; `rabinBlumTrapdoor`: `2·max(n, 3)`;
+`expCollection`: `dlDefaultIndex` below `n₀`). A per-index form (`|encD_i x| = |encD_i default|
+≤ m(n)`) would admit them; it is not formalized. -/
+noncomputable def glPad (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
+    Collection where
+  D i := F.D i × (Fin (F.encD i default).length → Bool)
+  encD i z := pairEncode (F.encD i z.1) (List.ofFn z.2)
+  decD i w := match pairDecode w with
+    | some (a, b) => match F.decD i a, decodeFin (F.encD i default).length b with
+      | some x, some r => some (x, r)
+      | _, _ => none
+    | none => none
+  decD_encD i z := by simp [pairDecode_pairEncode, F.decD_encD, decodeFin_ofFn]
+  encD_decD i w z h := by
+    rcases hw : pairDecode w with _ | ⟨a, b⟩
+    · simp [hw] at h
+    cases ha : F.decD i a <;> cases hb : decodeFin (F.encD i default).length b <;> simp [hw, ha, hb] at h
+    rw [eq_pairEncode_of_pairDecode w a b hw, ← h, F.encD_decD i a _ ha, ofFn_of_decodeFin_eq_some hb]
+  f i z := pairEncode (F.f i z.1) (List.ofFn z.2)
+  gen := F.gen
+  gen_uniform := F.gen_uniform
+  sample := NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)
+  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
+  eval w := pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w))))
+    (pairSndD (pairSndD w))
+  eval_poly := (F.eval_poly.comp (polyTimeComputable_pairFstD.pairEncode
+    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
+    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
+  eval_spec i z := by simp [F.eval_spec]
+  sample_spec n r s := by
+    obtain ⟨⟨s₁, s₂⟩, hs⟩ := (Fin.appendEquiv (F.sample.coins.eval n) (m.eval n)).surjective s
+    have hofn : List.ofFn s = List.ofFn s₁ ++ List.ofFn s₂ := by
+      rw [← hs]
+      exact List.ofFn_fin_append s₁ s₂
+    have hA : (List.ofFn s).take (F.sample.coinLen n) = List.ofFn s₁ := by
+      rw [hofn, List.take_left' List.length_ofFn]
+    have hB : (List.ofFn s).drop (F.sample.coinLen n) = List.ofFn s₂ := by
+      rw [hofn, List.drop_left' List.length_ofFn]
+    obtain ⟨x, hx, hev⟩ := F.sample_spec n r s₁
+    have hL : (F.encD (pairFstD (F.gen.runAt n [] r)) default).length = m.eval n := henc n r default
+    have hs₂ : List.ofFn s₂ = List.ofFn
+        fun j : Fin (F.encD (pairFstD (F.gen.runAt n [] r)) default).length => s₂ (Fin.cast hL j) :=
+      List.ofFn_congr hL.symm s₂
+    refine ⟨(x, fun j => s₂ (Fin.cast hL j)), ?_, ?_⟩
+    · simp only [glPadSample_runAt, hA, hB, pairDecode_pairEncode, ← NUPPT.runAt_eq, hx, hs₂,
+        decodeFin_ofFn]
+    · simp only [glPadSample_runAt, hA, hB, pairFstD_pairEncode, pairSndD_pairEncode,
+        ← NUPPT.runAt_eq, hev, hs₂]
+
+/-- The predicate `h_i(x, r) = ⟨x, r⟩` for the padded collection: the inner product of the
+encoding of `x` (padded or truncated to the padding length) with `r`. -/
+def glBit : ∀ i, F.D i × (Fin (F.encD i default).length → Bool) → Bool :=
+  fun i z => HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2
+
+/-- Unfolding: `h_i(x, r)` is the inner product `⟨padFin(encD_i x), r⟩`, the encoding of `x`
+padded or truncated to the padding length `|encD_i(default)|`. -/
+theorem glBit_eq (i : List Bool) (z : F.D i × (Fin (F.encD i default).length → Bool)) :
+    F.glBit i z = HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2 := rfl
+
+variable {F} in
+/-- Unfolding: the padded collection keeps the index generator. -/
+theorem glPad_gen (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
+    (F.glPad m henc).gen = F.gen := rfl
+
+variable {F} in
+/-- Unfolding: `g_i(x, r) = ⟨f_i(x), r⟩`. -/
+theorem glPad_f (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
+    (i : List Bool) (z : (F.glPad m henc).D i) :
+    (F.glPad m henc).f i z = pairEncode (F.f i z.1) (List.ofFn z.2) := rfl
+
+variable {F} in
+/-- Unfolding: the sampler of the padded collection runs `Sample(1^n, i)` on its first
+`|Sample's coins|` coins and appends the remaining coins. -/
+theorem glPad_sample_runAtL (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
+    (n : ℕ) (i r : List Bool) :
+    (F.glPad m henc).sample.runAtL n i r =
+      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)) := by
+  simp only [glPad, NUPPT.runAtL, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
+    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
+    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
+    NUPPT.coinLen]
+
+variable {F} in
+/-- Unfolding: the decoder of the padded collection is `glPadDecode` at the padding length
+`|encD_i(default)|` (propositional: the two `match` expressions are compiled separately). -/
+theorem glPad_decD_eq (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
+    (i : List Bool) : (F.glPad m henc).decD i = glPadDecode F i (F.encD i default).length := by
+  funext w
+  unfold Collection.glPad glPadDecode
+  dsimp only
+  cases pairDecode w with
+  | none => rfl
+  | some ab =>
+    obtain ⟨a, b⟩ := ab
+    dsimp only
+    cases F.decD i a <;> cases decodeFin (F.encD i default).length b <;> rfl
+
+/-- **The padded collection is one-way** ([PS10, Theorem 87.3], collection form, first clause):
+if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at the
+indices generated at parameter `n`, then `F.glPad m` is a collection of one-way functions.
+
+**Proof sketch.** *Sampling:* with `h.sampleClose = ⟨δ, hδ, hS⟩`, at index `i = index n r`
+the decoded sampler output is `(decD i (Sample(1^n, i; s₁)), decodeFin _ (ofFn s₂))` on the
+coin split `splitCoins (Sample.coins n) (m n)` (`glPad_sample_runAtL`, `List.ofFn` of the
+split, `uprob_comp_equiv`); `henc` gives `(encD i default).length = m n`, so the second
+component decodes exactly (`decodeFin_ofFn`) and `StatClose.prod (hS n r) (StatClose.refl _)`
+with `StatClose.map` to the pair gives `SampleClose δ`. *Hard:* for `A : NUPPT` against
+`F.glPad m`, the inverter `B` against `F`: coins `m + A.coins` (`NUPPT.exists_split m`, the
+first `m n` coins are `r`), on `⟨1^n, ⟨i, y⟩⟩` it calls `A` once on `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`
+(`NUPPT.exists_comp`, `NUPPT.exists_seq`) and returns the first component of the answer
+(`pairFstD`). Then `(F.glPad m).invProbAt A n ≤ F.invProbAt B n`: unfold both `uexp` over
+`Gen`'s coins (`OneWay.uexp_mono`), split the inner `uprob` over `D_i × ({0,1}^{m n} × A.Coins n)`
+against `D_i × B.Coins n` by `uprob_comp_equiv` on `splitCoins`, and `uprob_mono`: a decoded
+answer `(x', r')` with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)`
+(`pairEncode_injective`). `Negligible.mono` with `h.hard B`. -/
+theorem OneWay.glPad {F : Collection} (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
+    (h : F.OneWay) : (F.glPad m henc).OneWay := by
+  obtain ⟨δ, hδ, hS⟩ := h.sampleClose
+  refine ⟨⟨δ, hδ, fun n r => ?_⟩, fun A => ?_⟩
+  · have key := statClose_glPadSampler F m (F.glPad m henc).sample rfl (glPad_sample_runAtL m henc)
+      hS n r _ (henc n r default)
+    simp only [glPad_decD_eq] at key ⊢
+    exact key
+  · refine (h.hard (glPadCollInvMachine A m)).mono ⟨0, fun n _ => ?_⟩
+    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
+    have key := glPad_invProbAt_le F m A n (fun r => (F.encD (F.index n r) default).length)
+      (fun r => henc n r default)
+    unfold Collection.invProbAt at key ⊢
+    simp only [glPad_decD_eq]
+    exact key
+
+/-- **`⟨x, r⟩` is hard-core for the padded collection** ([PS10, Theorem 87.3], collection form,
+second clause; inventory Thm-87.3.coll, needed by Theorem 104.4): if `F` is a collection of
+one-way functions with encoding length `m(n)` at generated indices, then
+`h_i(x, r) = ⟨encD_i x, r⟩` is a hard-core predicate for `F.glPad m` (`Collection.HardCore`).
+
+Repair (run-3 audit P4-2): statement unchanged. The run-2 sketch transferred the cube lemma
+`HardcoreBit.invProb_guessInverter` to `D_i` by "identifying `D_i` with `{0,1}^{m n}` through
+the injective encoding"; that step is invalid — the image of `encD_i` is in general a strict
+subset of the cube (`Z_N^*`, `QR_N`), the uniform `x ∈ D_i` is not a uniform cube element and
+the predictor's behaviour off the image is uncontrolled. The transfer is replaced by the
+encoded-domain lemma `HardcoreBit.invProb_guessInverter_enc_pad`
+(`Asymptotic/GoldreichLevinDomain.lean`), stated for `x` uniform on an arbitrary finite type
+with an arbitrary encoding into `{0,1}^m`.
+
+**Proof sketch.** *Easy:* `⟨i, ⟨a, b⟩⟩ ↦ ipFun ⟨padToLen a b, b⟩` — pad `a = encD_i x` to the
+length of `b = r` and apply the inner-product evaluator (`exists_glBitCollEvaluator`,
+`Asymptotic/HardCoreGLColl.lean`). *Hard:* `glColl_negligible` with the padding length
+`L n r = |encD_i(default)| = m(n)` (`henc`) and the one-wayness of the padded collection
+(`OneWay.glPad`, its inversion experiment rewritten by `glPad_decD_eq`): by contradiction,
+`not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ E_r[Pr[A(1^n, ⟨i, ⟨f_i x, r⟩⟩) = ⟨encD_i x, r⟩]]`
+infinitely often; the good indices (`HardcoreBit.half_le_uprob_threshold`) have per-index
+success `≥ 1/2 + n^{−c}/2`, where `HardcoreBit.invProb_guessInverter_enc_pad` with
+`enc := padFin (m n) ∘ encD_i` and the hard-wired `k(n) = size (8 m(n) n^{2c})` (`glKc`) makes
+the recovery procedure of [PS10, Algorithm 89.6] output `encD_i x` with probability
+`≥ ε/(4·2^{k(n)})`, `ε = n^{−c}/2`; the inverter `glCollMachine` (the recovery machine `glMachine`
+on the pre-processed predictor `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`, output `⟨x', r⟩`) realises it
+(`glColl_uprob_le`); averaging over the good indices (`HardcoreBit.uprob_mul_le_uexp`) gives
+inversion probability `≥ ε²/(4·2^{k(n)})`, inverse polynomial infinitely often, contradicting
+`(OneWay.glPad m henc h).hard`. -/
+theorem OneWay.glPad_hardCore {F : Collection} (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
+    (h : F.OneWay) : (F.glPad m henc).HardCore F.glBit := by
+  refine ⟨?_, fun A => ?_⟩
+  · obtain ⟨H, hH, hHx⟩ := exists_glBitCollEvaluator F
+    exact ⟨H, hH, fun i x => hHx i x.1 x.2⟩
+  · have hmax : ∀ x : ℝ, x ≤ 1 / 2 + max 0 (x - 1 / 2) := fun x => by
+      linarith [le_max_right (0 : ℝ) (x - 1 / 2)]
+    refine ⟨_, glColl_negligible F m (fun n r => (F.encD (F.index n r) default).length)
+      (fun n r => henc n r default) henc A (fun B => ?_), fun n => hmax _⟩
+    have key := (OneWay.glPad m henc h).hard B
+    unfold Collection.invProbAt at key
+    simp only [glPad_decD_eq] at key
+    exact key
+
+end Collection
+
+/-- **Goldreich–Levin for collections** ([PS10, Theorem 87.3], the collection form the text
+uses for Theorem 104.4 and Chapter 4): for a collection `F` of one-way functions with
+encoding length `m(n)` at generated indices, `g_i(x, r) = (f_i(x), r)` is a collection of
+one-way functions and `⟨x, r⟩` is hard-core for it. -/
+theorem goldreich_levin_coll {F : Collection} (m : PolyExpr)
+    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
+    (h : F.OneWay) : (F.glPad m henc).OneWay ∧ (F.glPad m henc).HardCore F.glBit :=
+  ⟨Collection.OneWay.glPad m henc h, Collection.OneWay.glPad_hardCore m henc h⟩
+
+/-- The padded collection of a collection of permutations is a collection of permutations
+[PS10, Theorem 87.3, "(OWP)"]: `g_i = perm_i × id` on `D_i × {0,1}^{|encD_i default|}`. -/
+noncomputable def PermCollection.glPad (P : PermCollection) (m : PolyExpr)
+    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
+    PermCollection :=
+  { P.toCollection.glPad m henc with
+    perm := fun i => (P.perm i).prodCongr (Equiv.refl _)
+    f_perm := fun i z => by simp [Collection.glPad, P.f_perm] }
+
+/-- Unfolding: the underlying collection of `P.glPad m henc` is `P.toCollection.glPad m henc`. -/
+theorem PermCollection.glPad_toCollection (P : PermCollection) (m : PolyExpr)
+    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
+    (P.glPad m henc).toCollection = P.toCollection.glPad m henc := rfl
+
+/-- **The padded permutation collection is one-way** when the original is (collection form of
+[PS10, Theorem 87.3] for Definition 55.1). -/
+theorem PermCollection.OneWay.glPad {P : PermCollection} (m : PolyExpr)
+    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
+    (h : P.OneWay) : (P.glPad m henc).OneWay :=
+  Collection.OneWay.glPad m henc h
+
+/-- **`⟨x, r⟩` is hard-core for the padded permutation collection**. -/
+theorem PermCollection.OneWay.glPad_hardCore {P : PermCollection} (m : PolyExpr)
+    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
+    (h : P.OneWay) : (P.glPad m henc).toCollection.HardCore P.glBit :=
+  Collection.OneWay.glPad_hardCore m henc h
+
+/-- The padded collection of a collection of trapdoor permutations is a collection of
+trapdoor permutations [PS10, Theorem 87.3 for Definition 56.1, as used in Theorem 104.4]:
+`Inv'(1^n, ⟨t, ⟨y, r⟩⟩) = ⟨Inv(1^n, ⟨t, y⟩), r⟩`.
+
+**Proof sketch** (of `inv_spec`). Unfold the activation of the `ofPolyTimeUniform` machine
+(`NUPPT.output_ofPolyTime`, the layout projections); `T.inv` is uniform so its activation is
+its output on the layout with empty advice; `T.inv_spec` decodes the first component to
+`(perm i).symm y.1` and `decodeFin_ofFn` the second to `y.2`. -/
+noncomputable def TrapdoorCollection.glPad (T : TrapdoorCollection) (m : PolyExpr)
+    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
+    TrapdoorCollection :=
+  { T.toPermCollection.glPad m henc with
+    inv := NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins
+    inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
+    inv_spec := fun n r y s => by
+      have hspec := T.inv_spec n r y.1 s
+      simp only [NUPPT.runAt, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime, glPadInvFun,
+        NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
+        pairFstD_pairEncode, pairSndD_pairEncode, PermCollection.glPad, Collection.glPad,
+        pairDecode_pairEncode, decodeFin_ofFn, T.inv_uniform n] at hspec ⊢
+      rw [hspec]
+      rfl }
+
+/-- Unfolding: the underlying permutation collection of `T.glPad m henc` is
+`T.toPermCollection.glPad m henc`. -/
+theorem TrapdoorCollection.glPad_toPermCollection (T : TrapdoorCollection) (m : PolyExpr)
+    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
+    (T.glPad m henc).toPermCollection = T.toPermCollection.glPad m henc := rfl
+
+/-- **The padded trapdoor collection is one-way** when the original is ([PS10, Theorem 87.3]
+for Definition 56.1 (5)). -/
+theorem TrapdoorCollection.OneWay.glPad {T : TrapdoorCollection} (m : PolyExpr)
+    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
+    (h : T.OneWay) : (T.glPad m henc).OneWay :=
+  Collection.OneWay.glPad m henc h
+
+/-- **`⟨x, r⟩` is hard-core for the padded trapdoor collection**: the hypothesis "trapdoor
+permutations with a hard-core predicate" of [PS10, Theorem 104.4] is satisfiable from trapdoor
+permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`; no
+candidate of the library satisfies it as parametrized, see `Collection.glPad`). -/
+theorem TrapdoorCollection.OneWay.glPad_hardCore {T : TrapdoorCollection} (m : PolyExpr)
+    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
+    (h : T.OneWay) : (T.glPad m henc).toCollection.HardCore T.glBit :=
+  Collection.OneWay.glPad_hardCore m henc h
+
+end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Asymptotic/NextBit.lean b/TCSlib/Cryptography/Asymptotic/NextBit.lean
index 1c452569..911552d6 100644
--- a/TCSlib/Cryptography/Asymptotic/NextBit.lean
+++ b/TCSlib/Cryptography/Asymptotic/NextBit.lean
@@ -35,9 +35,11 @@ The file has two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`
   two hybrids).
 * **Asymptotic**: `Ensemble.NextBitUnpredictable` [PS10, Definition 75.2] and the
   completeness theorem `Ensemble.NextBitUnpredictable.pseudorandom` [PS10, Theorem 75.4],
-  proved by instantiating the concrete reduction at each `n`, hard-wiring the sign into the
-  advice of the predictor machine (the position is read off the length of the prefix), and
-  finishing with the contradiction idiom `not_negligible_iff_exists_polyExpr`.
+  proved by instantiating the concrete reduction at each `n` with `ℓ(n) > 0` (where
+  `ℓ(n) = 0` no distinguisher has an advantage, `prgAdv_eq_zero_of_length_eq_zero`),
+  hard-wiring the sign into the advice of the predictor machine (the position is read off the
+  length of the prefix), and finishing with the contradiction idiom
+  `not_negligible_iff_exists_polyExpr`.
 
 The implicit converse ("a pseudorandom ensemble passes the next-bit test", the soundness of
 the test the text takes for granted) is `nextBitDist` / `prgAdv_nextBitDist` concretely and
@@ -57,6 +59,12 @@ shape (DESIGN.md §2.12); the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)`
 `Ensemble.nonempty` (with an empty seed type the experiment has probability `0`, the ensemble
 passes the next-bit test vacuously, and the always-accepting distinguisher has advantage `1`).
 
+**Repair (gate 03c, finding 2; ruling G3-7b):** `NextBitUnpredictable.pseudorandom` no longer
+assumes `0 < ℓ(n)` for every `n` (a hypothesis the text does not have, which excluded every
+ensemble with `ℓ(0) = 0`); it is now the source's statement. Where `ℓ(n) = 0` both `X_n` and
+`U_0` are the point mass on the empty string, and the proof needs a position only where
+`ℓ(n) > 0`.
+
 ## Main definitions
 
 * `TCSlib.Cryptography.nextBitProb` — the next-bit experiment at one parameter.
@@ -73,7 +81,8 @@ passes the next-bit test vacuously, and the always-accepting distinguisher has a
 ## Main results
 
 * `TCSlib.Cryptography.exists_nextBitPred` — the concrete next-bit reduction
-  (`1/2 + prgAdv X D / ℓ ≤` predictor success for some `i < ℓ` and some sign).
+  (`1/2 + prgAdv X D / ℓ ≤` predictor success for some `i < ℓ` and some sign);
+  `TCSlib.Cryptography.prgAdv_eq_zero_of_length_eq_zero` — no advantage on `{0,1}^0`.
 * `TCSlib.Cryptography.acceptProb_nextBitHybrid_zero`,
   `TCSlib.Cryptography.acceptProb_nextBitHybrid_self`,
   `TCSlib.Cryptography.acceptProb_nextBitHybrid_mix` — the hybrid identities
@@ -230,7 +239,8 @@ every event `p` on `(σ × {0,1}^ℓ) × ρ` and every bit `g s` depending on th
 "`H^i` is sampled by drawing from `H^{i+1}` or from `H̃^{i+1}` with probability `1/2`" step of
 the proof of [PS10, Theorem 75.4], in a form shared by the mixing identity and the predictor
 analysis. (The planting map `(b, (s, u), r) ↦ ((s, update u i (b ⊕ g s)), r)` is 2-to-1, not a
-bijection — run-3 audit P2-3 — so the proof adjoins an ignored uniform bit instead.)
+bijection — a run-3 repair, labelled P2-3 here and noted at gate 03c, finding 5 — so the
+proof adjoins an ignored uniform bit instead.)
 
 **Proof sketch.** Adjoin an ignored uniform bit `b` (`uprob_fst` after `Equiv.prodComm`),
 then apply the involution `ψ (b, (s, u), r) := (u_i ⊕ g s, (s, update u i (b ⊕ g s)), r)` of
@@ -356,14 +366,17 @@ from the prefix of length `i` with probability exactly
 [PS10, Theorem 75.4] (which writes `A(t) = 1` for `A(t) = b`), i.e. the identity of
 [PS10, Lemma 73.8] (`predict_eq`) with `X¹ := H^{i+1}` and `X⁰ := H̃^{i+1}`.
 
-**Proof sketch.** Split on whether the drawn bit `u_i` equals `x_i` (each case has
-probability `1/2`, independently of `s`, the other bits of `u`, and `c`: the bijection
-`(b, (s, u), c) ↦ (s, (update u i (xor b (X s i)), c))` followed by `uprob_bool_prod`, as in
-`predProb_owpPredictor_false`). If `u_i = x_i`, the completed string
-`completePrefix i (prefixOf i (X s)) u` is `nextBitHybrid X (i+1) (s, u)`
-(`completePrefix_prefixOf`) and the predictor is right iff `D` accepts; if `u_i = x̄_i`, the
-completed string is `nextBitHybridFlip X i (s, u)` and the predictor is right iff `D`
-rejects (`uprob_not`, which needs the nonemptiness hypotheses). Average the two. -/
+**Proof sketch.** Reassociate the sample space to `(σ × {0,1}^ℓ) × ρ` (`Equiv.prodAssoc`) and
+apply `uprob_split_bit` at position `i` with the bit `x_i = X s i` (an adjoined uniform bit and
+the involution `ψ`): the success probability is the average of the success event with `x_i`
+planted at bit `i` of `u` and with `x̄_i` planted there. With `x_i` planted, the completed
+string `completePrefix i (prefixOf i (X s)) u` is `nextBitHybrid X (i+1) (s, u)`
+(`completePrefix_prefixOf_eq`, `nextBitHybrid_update_eq`) and the predictor, which outputs
+`u_i = x_i` on acceptance, is right iff `D` accepts; with `x̄_i` planted the completed string is
+`nextBitHybridFlip X i (s, u)` (`nextBitHybrid_update_not_eq`) and the predictor is right iff
+`D` rejects (`uprob_not`, which needs the nonemptiness hypotheses). Average the two:
+`(Pr[D(H^{i+1}) = 1] + 1 − Pr[D(H̃^{i+1}) = 1]) / 2`. (The run-2 sketch transported the event
+along the 2-to-1 map `(b, (s, u), c) ↦ (s, (update u i (b ⊕ x_i), c))`; see `uprob_split_bit`.) -/
 theorem nextBitProb_nextBitPred_false {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
     [Nonempty ρ] {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
     nextBitProb X i (nextBitPred D i false) =
@@ -421,6 +434,28 @@ theorem nextBitProb_nextBitPred_true {σ ρ : Type*} [Fintype σ] [Fintype ρ] [
   rw [h, nextBitProb_nextBitPred_false]
   ring
 
+/-- The PRG advantage is the gap between the extreme hybrids: `prgAdv X D =
+|Pr[D(H^0) = 1] − Pr[D(H^ℓ) = 1]|`, by `H^0 = U_ℓ` (`acceptProb_nextBitHybrid_zero`) and
+`H^ℓ = X` (`acceptProb_nextBitHybrid_self`). -/
+private theorem prgAdv_eq_abs_nextBitHybrid {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
+    {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
+    prgAdv X D = |acceptProb (nextBitHybrid X 0) D - acceptProb (nextBitHybrid X ℓ) D| := by
+  unfold prgAdv distAdv
+  rw [acceptProb_nextBitHybrid_zero, acceptProb_nextBitHybrid_self, abs_sub_comm]
+
+/-- **No advantage on the empty string**: if `ℓ = 0`, then every distinguisher `D` has PRG
+advantage `0` against every sampler `X` into `{0,1}^ℓ` (both `X` and the uniform `U_0` are the
+point mass on the empty string). This is the case `ℓ(n) = 0` of [PS10, Theorem 75.4], which
+needs no position.
+
+**Proof sketch.** With `ℓ = 0` the two extreme hybrids `H^0` and `H^ℓ` coincide, so the gap
+`prgAdv_eq_abs_nextBitHybrid` is `|a − a| = 0`. -/
+theorem prgAdv_eq_zero_of_length_eq_zero {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
+    {ℓ : ℕ} (hℓ : ℓ = 0) (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
+    prgAdv X D = 0 := by
+  subst hℓ
+  rw [prgAdv_eq_abs_nextBitHybrid, sub_self, abs_zero]
+
 /-- **The next-bit reduction, concrete form** (the content of the proof of
 [PS10, Theorem 75.4] at one parameter): for every sampler `X` into `{0,1}^ℓ` with `ℓ > 0` and
 every distinguisher `D` with PRG advantage `ε = prgAdv X D` against `X`, there are a position
@@ -428,8 +463,8 @@ every distinguisher `D` with PRG advantage `ε = prgAdv X D` against `X`, there
 [PS10, Algorithm 76.5] predicts bit `i` of `X` from the prefix of length `i` with probability
 at least `1/2 + ε/ℓ`. (The text obtains `1/2 + 1/(p(n)ℓ(n))` from `ε = 1/p(n)`.)
 
-**Proof sketch.** `prgAdv X D = |Pr[D(H^ℓ) = 1] − Pr[D(H^0) = 1]|` by
-`acceptProb_nextBitHybrid_self` and `acceptProb_nextBitHybrid_zero`; the hybrid lemma
+**Proof sketch.** `prgAdv X D = |Pr[D(H^0) = 1] − Pr[D(H^ℓ) = 1]|`
+(`prgAdv_eq_abs_nextBitHybrid`); the hybrid lemma
 `hybrid_lemma` (`exists_hybrid_gap`) over `i ↦ acceptProb (nextBitHybrid X i) D` gives
 `i < ℓ` with `ε/ℓ ≤ |Pr[D(H^i) = 1] − Pr[D(H^{i+1}) = 1]|`. By the mixing identity
 `acceptProb_nextBitHybrid_mix`, `Pr[D(H^i) = 1] − Pr[D(H^{i+1}) = 1] =
@@ -442,10 +477,7 @@ theorem exists_nextBitPred {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty 
     {ℓ : ℕ} (hℓ : 0 < ℓ) (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
     ∃ (i : Fin ℓ) (flip : Bool),
       1 / 2 + prgAdv X D / ℓ ≤ nextBitProb X i (nextBitPred D i flip) := by
-  have hadv : prgAdv X D =
-      |acceptProb (nextBitHybrid X 0) D - acceptProb (nextBitHybrid X ℓ) D| := by
-    unfold prgAdv distAdv
-    rw [acceptProb_nextBitHybrid_zero, acceptProb_nextBitHybrid_self, abs_sub_comm]
+  have hadv := prgAdv_eq_abs_nextBitHybrid X D
   obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun j => acceptProb (nextBitHybrid X j) D) hℓ
   have hmix := acceptProb_nextBitHybrid_mix X ⟨k, hk⟩ D
   have hδ : prgAdv X D / ℓ ≤ |acceptProb (nextBitHybrid X (k + 1)) D -
@@ -517,13 +549,14 @@ private theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fint
 /-! ### Completeness of the next-bit test [PS10, Theorem 75.4] -/
 
 /-- **The next-bit predictor as a machine** [PS10, Algorithm 76.5]: for a distinguisher
-machine `D`, positions `i n < ℓ(n)` and signs `flip n`, a non-uniform PPT `A` with coins
-`ℓ + D.coins` and advice `⟨D.advice n, [flip n]⟩` such that, at parameter `n` and position
-`i n`, `A` on the prefix `t` with coins `(u, c)` (split by `e n`) is exactly the concrete
-predictor `nextBitPred (D.distinguisher n (ℓ n)) (i n) (flip n) t (u, c)`: it runs
+machine `D` and signs `flip n`, a non-uniform PPT `A` with coins `ℓ + D.coins` and advice
+`⟨D.advice n, [flip n]⟩` such that, at every parameter `n` and every position `i < ℓ(n)`, `A`
+on the prefix `t` with coins `(u, c)` (split by `e n`) is exactly the concrete predictor
+`nextBitPred (D.distinguisher n (ℓ n)) i (flip n) t (u, c)`: it runs
 `D(1^n, t ++ u.drop |t|; c)` and outputs `u_{|t|}` or its negation according to the verdict,
-negated once more if `flip n`. The position is read off the prefix length `|t| = i n`, so
-only the sign is hard-wired.
+negated once more if `flip n`. The position is read off the prefix length `|t| = i`, so only
+the sign is hard-wired, and the identity holds at every position (restated so at gate 03c,
+finding 2: no choice of position is needed where `ℓ(n) = 0`).
 
 **Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨D.advice n, [flip n]⟩⟩, r⟩`
 cuts `r` into `u := r.take (ℓ n)` and `c := r.drop (ℓ n)` (`polyTimeComputable_pairTakePoly`/
@@ -537,12 +570,11 @@ it with coins `add ℓ D.coins` and advice bound `2·D.adv + 3` (`length_pairEnc
 split is `Fin.appendEquiv` composed with `finCongr`, and the identity is `runAtL_ofPolyTime`,
 the projection identities of the layout, `List.take_left'`/`List.drop_left'`,
 `ofFn_completePrefix` and `headD_drop_ofFn`. -/
-private theorem exists_nextBitPredMachine {ℓ : PolyExpr} (D : NUPPT) (i : ∀ n, Fin (ℓ.eval n))
-    (flip : ℕ → Bool) :
+private theorem exists_nextBitPredMachine (ℓ : PolyExpr) (D : NUPPT) (flip : ℕ → Bool) :
     ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
-      ∀ n (t : Fin (i n) → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
-        A.predictor n (i n) t (e n (u, c)) =
-          nextBitPred (D.distinguisher n (ℓ.eval n)) (i n) (flip n) t (u, c) := by
+      ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
+        A.predictor n i t (e n (u, c)) =
+          nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n) t (u, c) := by
   -- the coin cut `⟨1^n, r⟩ ↦ u = r.take (ℓ n)`, `c = r.drop (ℓ n)`
   have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
   have hu : PolyTimeComputable fun z =>
@@ -604,7 +636,7 @@ private theorem exists_nextBitPredMachine {ℓ : PolyExpr} (D : NUPPT) (i : ∀
   let e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n := fun n =>
     (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)).trans
       (Equiv.arrowCongr (finCongr (hlen n).symm) (Equiv.refl Bool))
-  refine ⟨A, e, fun n t u c => ?_⟩
+  refine ⟨A, e, fun n i t u c => ?_⟩
   have hofn : List.ofFn (e n (u, c)) = List.ofFn u ++ List.ofFn c := by
     rw [← List.ofFn_fin_append]
     exact (List.ofFn_congr (hlen n).symm (Fin.append u c)).symm
@@ -612,71 +644,97 @@ private theorem exists_nextBitPredMachine {ℓ : PolyExpr} (D : NUPPT) (i : ∀
   rw [NUPPT.runAtL_ofPolyTime]
   simp [NUPPT.advInput, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
     NUPPT.runAtL, List.take_left', List.drop_left', ofFn_completePrefix]
-  split_ifs <;> cases u (i n) <;> cases flip n <;> rfl
+  split_ifs <;> cases u i <;> cases flip n <;> rfl
 
 /-- **Completeness of the next-bit test** [PS10, Theorem 75.4]: if the ensemble `{X_n}` over
-`{0,1}^{ℓ(n)}` (with `ℓ(n) > 0`) passes the next-bit test, then it is pseudorandom.
+`{0,1}^{ℓ(n)}` passes the next-bit test, then it is pseudorandom.
 
 **Repair (run-3 audit P2-2):** the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` was dropped
 (it is the field `Ensemble.nonempty`; with an empty seed type the experiment has probability
 `0`, the ensemble passes the next-bit test vacuously, and the always-accepting distinguisher
 has advantage `1`); the frozen shape of DESIGN.md §2.12 is restored.
 
+**Repair (gate 03c, finding 2; ruling G3-7b):** the hypothesis `hℓ : ∀ n, 0 < ℓ.eval n`, which
+the text does not have, was dropped; the theorem now applies to every ensemble, `ℓ(0) = 0`
+included (e.g. `ℓ = n`, `2n`, `n²`).
+
 **Proof sketch.** By contradiction, as in the text. Fix a distinguisher `D` with
 `¬ Negligible (fun n => prgAdv (X_n) (D.distinguisher n (ℓ n)))`
 (`Ensemble.pseudorandom_iff_prgAdv`); by `not_negligible_iff_exists_polyExpr` there is a
 positive syntactic polynomial `p` with `1/p(n) ≤ prgAdv` for infinitely many `n`. At every
-`n`, `exists_nextBitPred (hℓ n)` (with the instance `X.nonempty n`) gives a position
+`n` with `ℓ(n) > 0`, `exists_nextBitPred` (with the instance `X.nonempty n`) gives a position
 `i_n < ℓ(n)` and a sign `flip_n` with
-`1/2 + prgAdv/ℓ(n) ≤ nextBitProb (X_n) i_n (nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n)`
-(`choose`). The predictor machine `A` is `exists_nextBitPredMachine D i flip` (advice
+`1/2 + prgAdv/ℓ(n) ≤ nextBitProb (X_n) i_n (nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n)`;
+where `ℓ(n) = 0` put `flip_n := false` (`choose` on "a sign, and a position if `ℓ(n) > 0`").
+The predictor machine `A` is `exists_nextBitPredMachine ℓ D flip` (advice
 `⟨D.advice n, [flip_n]⟩`, coins `ℓ + D.coins`; on `⟨1^n, t⟩` with coins `u ++ c` it runs
 `D(1^n, t ++ u.drop |t|; c)` and outputs `xor (if g then u_{|t|} else !u_{|t|}) flip_n`, the
-position being read off the prefix length). Its functional identity
-`A.predictor n i_n t (e (u, c)) = nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n t (u, c)`
+position being read off the prefix length). Its functional identity, at every position `i`,
+`A.predictor n i t (e (u, c)) = nextBitPred (D.distinguisher n (ℓ n)) i flip_n t (u, c)`
 along the coin split `e : (Fin (ℓ n) → Bool) × D.Coins n ≃ A.Coins n` (`Fin.appendEquiv`)
-gives `nextBitProb (X_n) i_n (A.predictor n i_n) = nextBitProb (X_n) i_n (nextBitPred …)`
+gives `nextBitProb (X_n) i (A.predictor n i) = nextBitProb (X_n) i (nextBitPred …)`
 (`uprob_comp_equiv`). Now `h A` gives a negligible `ε` with `nextBitProb … ≤ 1/2 + ε n` for
-all `n, i`; hence `1/(p(n) ℓ(n)) ≤ prgAdv/ℓ(n) ≤ ε n` for infinitely many `n`, i.e.
-`¬ Negligible ε` by `not_negligible_iff_exists_polyExpr` with the polynomial `mul p ℓ`
-(positive by `hℓ` and `0 < p`), a contradiction. -/
+all `n, i`. At every `n` of the infinite set, `ℓ(n) > 0`, since at `ℓ(n) = 0` the advantage is
+`0 < 1/p(n)` (`prgAdv_eq_zero_of_length_eq_zero`); there
+`1/(p(n)(ℓ(n) + 1)) ≤ 1/(p(n) ℓ(n)) ≤ prgAdv/ℓ(n) ≤ ε n`, i.e. `¬ Negligible ε` by
+`not_negligible_iff_exists_polyExpr` with the positive polynomial `mul p (ℓ + 1)`, a
+contradiction. -/
 theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
-    (hℓ : ∀ n, 0 < ℓ.eval n) (h : X.NextBitUnpredictable) :
-    X.Pseudorandom := by
+    (h : X.NextBitUnpredictable) : X.Pseudorandom := by
   rw [Ensemble.pseudorandom_iff_prgAdv]
   intro D
   by_contra hneg
   obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
-  have hex : ∀ n, ∃ (i : Fin (ℓ.eval n)) (flip : Bool),
+  -- a sign at every `n`, and a position where `ℓ(n) > 0` (the concrete reduction)
+  have hex : ∀ n, ∃ flip : Bool, 0 < ℓ.eval n → ∃ i : Fin (ℓ.eval n),
       1 / 2 + prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n) ≤
-        nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i flip) :=
-    fun n => exists_nextBitPred (hℓ n) (X.X n) (D.distinguisher n (ℓ.eval n))
-  choose i flip hif using hex
-  obtain ⟨A, e, hA⟩ := exists_nextBitPredMachine D i flip
-  obtain ⟨ε, hε, hbound⟩ := h A
-  have hprob : ∀ n, nextBitProb (X.X n) (i n) (A.predictor n (i n)) =
-      nextBitProb (X.X n) (i n) (nextBitPred (D.distinguisher n (ℓ.eval n)) (i n) (flip n)) := by
+        nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i flip) := by
     intro n
+    by_cases hn : 0 < ℓ.eval n
+    · obtain ⟨i, flip, hif⟩ := exists_nextBitPred hn (X.X n) (D.distinguisher n (ℓ.eval n))
+      exact ⟨flip, fun _ => ⟨i, hif⟩⟩
+    · exact ⟨false, fun hn' => absurd hn' hn⟩
+  choose flip hif using hex
+  -- the predictor machine, and its identity with the concrete predictor at every position
+  obtain ⟨A, e, hA⟩ := exists_nextBitPredMachine ℓ D flip
+  obtain ⟨ε, hε, hbound⟩ := h A
+  have hprob : ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) =
+      nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n)) := by
+    intro n i
     unfold nextBitProb
     rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (X.σ n)) (e n))]
     apply OneWay.uprob_congr
     rintro ⟨s, u, c⟩
     simp [hA]
-  refine (not_negligible_iff_exists_polyExpr.mpr ⟨.mul p ℓ, fun n => ?_, fun n₀ => ?_⟩) hε
-  · simp only [PolyExpr.eval_mul]
-    exact Nat.mul_pos (hp n) (hℓ n)
+  -- `ε` is not negligible, with the positive polynomial `p · (ℓ + 1)`
+  refine (not_negligible_iff_exists_polyExpr.mpr
+    ⟨.mul p (.add ℓ (.const 1)), fun n => ?_, fun n₀ => ?_⟩) hε
+  · simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
+    exact Nat.mul_pos (hp n) (Nat.succ_pos _)
   · obtain ⟨n, hn, hpn⟩ := hinf n₀
     refine ⟨n, hn, ?_⟩
-    have h1 := hif n
-    have h2 := hbound n (i n)
-    rw [hprob n] at h2
-    have hℓpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast hℓ n
     have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
     have h0 : 0 ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
     rw [abs_of_nonneg h0] at hpn
-    calc (1 : ℝ) / ((PolyExpr.mul p ℓ).eval n : ℝ)
-        = (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := by
-          rw [PolyExpr.eval_mul, Nat.cast_mul, div_div]
+    -- on the infinite set `ℓ(n) > 0`: at `ℓ(n) = 0` the advantage is `0`
+    have hℓn : 0 < ℓ.eval n := by
+      rcases Nat.eq_zero_or_pos (ℓ.eval n) with hz | hz
+      · have hzero := prgAdv_eq_zero_of_length_eq_zero hz (X.X n) (D.distinguisher n (ℓ.eval n))
+        have := one_div_pos.mpr hppos
+        linarith
+      · exact hz
+    obtain ⟨i, h1⟩ := hif n hℓn
+    have h2 := hbound n i
+    rw [hprob n i] at h2
+    have hℓpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast hℓn
+    have hstep : (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ) ≤
+        (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := by
+      rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, div_div]
+      push_cast
+      exact one_div_le_one_div_of_le (mul_pos hppos hℓpos)
+        (mul_le_mul_of_nonneg_left (by linarith) hppos.le)
+    calc (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ)
+        ≤ (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := hstep
       _ ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n : ℝ) := by gcongr
       _ ≤ ε n := by linarith
       _ ≤ |ε n| := le_abs_self _
diff --git a/TCSlib/Cryptography/Asymptotic/Pseudorandom.lean b/TCSlib/Cryptography/Asymptotic/Pseudorandom.lean
index 9f34c952..1baff478 100644
--- a/TCSlib/Cryptography/Asymptotic/Pseudorandom.lean
+++ b/TCSlib/Cryptography/Asymptotic/Pseudorandom.lean
@@ -35,6 +35,11 @@ polynomial `stretch`, so that `G` is a typed family `G n : {0,1}^n → {0,1}^{
 concrete layer's convention [Gar26, Definition 3.5]); the text's `G : {0,1}* → {0,1}*` with
 `|G(x)| > |x|` admits irregular lengths, which no construction of the book uses.
 
+**Deviation:** the expansion clause `PRG.expands` holds at every seed length, `n = 0` included
+(the text's `|G(x)| > |x|` read literally at `x = ε`), so no `PolyExpr` stretch with `ℓ(0) = 0`
+(exactly `2n`) or `ℓ(1) = 1` (`n^c`) is a `PRG`; the length-doubling generators of the text are
+`DoublingPRG` (`Asymptotic/PRF.lean`). See `PRG` (gate 03c, finding 1; ruling G3-2).
+
 **Deviation:** `PRG.Easy`: a deterministic polynomial-time evaluator on the seed string
 instead of a PPT computing `G` with probability one (equivalent by `Complexity.NUPPT.Computes`
 and `ofPolyTimeUniform`, as for `FunFamily.Easy`); the seed is not prefixed by `1^n` since
@@ -55,12 +60,13 @@ its length is the parameter.
   "`prgAdv` negligible for every `D`" (the concrete quantity of [Gar26, Definition 3.5]).
 * `TCSlib.Cryptography.Ensemble.uniform_pseudorandom` — the uniform ensemble is pseudorandom
   (non-vacuity of Definition 74.1).
-* `TCSlib.Cryptography.PRG.secure_iff` — unfolding of `PRG.Secure` to the `prgAdv` form.
+* `TCSlib.Cryptography.PRG.easy_iff`, `TCSlib.Cryptography.PRG.secure_iff` — unfoldings of
+  `PRG.Easy` and of `PRG.Secure` (the latter to the `prgAdv` form).
 * `TCSlib.Cryptography.PRG.Easy.samplable` — the output ensemble of an efficiently
   computable generator is efficiently samplable (D6), so that `Ensemble.Indist.copies`
   applies to it.
-* `TCSlib.Cryptography.PRG.stretch_pos` — the output length is positive (the hypothesis of
-  [PS10, Theorem 75.4] holds for every generator).
+* `TCSlib.Cryptography.PRG.stretch_pos` — the output length of a generator is positive at
+  every seed length (from the expansion clause).
 
 ## References
 
@@ -101,20 +107,35 @@ theorem Ensemble.Indist.pseudorandom {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h :
 /-! ### Pseudorandom generators [PS10, Definition 77.1] -/
 
 /-- A **(length-regular) generator** with explicit stretch: at every seed length `n`, a
-function `G n : {0,1}^n → {0,1}^{ℓ(n)}` with `ℓ(n) > n` — the expansion clause
+function `G n : {0,1}^n → {0,1}^{ℓ(n)}` with `ℓ(n) > n` (at every `n`, `n = 0` included; see
+the second Deviation) — the expansion clause
 [PS10, Definition 77.1 (2)] with the output length a syntactic polynomial `stretch` (D9).
 The efficiency and pseudorandomness clauses are `PRG.Easy` and `PRG.Secure`.
 
 **Deviation:** `PRG` is *length-regular*: `|G(x)|` depends only on `|x|` and is the syntactic
 polynomial `stretch`, so that `G` is a typed family `G n : {0,1}^n → {0,1}^{ℓ(n)}` (the
 concrete layer's convention [Gar26, Definition 3.5]); the text's `G : {0,1}* → {0,1}*` with
-`|G(x)| > |x|` admits irregular lengths, which no construction of the book uses. -/
+`|G(x)| > |x|` admits irregular lengths, which no construction of the book uses.
+
+**Deviation:** the expansion clause holds at every seed length, `n = 0` included, as the text's
+`|G(x)| > |x|` says literally for `x = ε`. A `PolyExpr` stretch is a polynomial with coefficients
+in ℕ, so a stretch with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) is not a `PRG`, although
+the text uses such generators (the length-doubling `G` of Algorithm 92.1 and Theorem 97.3;
+Lemma 80.5's "for any polynomial `ℓ`"). They are reached up to one bit (`2n + 1`, `n^c + 1`, by
+`prg_expand` from the one-bit truncation `PRG.truncate` of `Asymptotic/PRF.lean`) or by truncation
+(`PRG.Secure.truncateTo_easy`/`_negligible`, `Asymptotic/PRFLemmas.lean`); the length-doubling
+generator of Theorem 97.3 is the separate predicate `DoublingPRG` (`Asymptotic/PRF.lean`),
+produced from any secure `PRG` by `PRG.doubling` (`PRG.Secure.doubling`). "PRGs exist" means the
+same under either reading, since a generator expanding only from some `n₀` on is made to expand
+everywhere by truncating to `n + 1` bits and changing it below `n₀` (a remark, not formalized).
+(Gate 03c, finding 1; ruling G3-2; DESIGN §5.25.) -/
 structure PRG where
   /-- The output length `ℓ(n)` at seed length `n`. -/
   stretch : PolyExpr
   /-- The generator at seed length `n`. -/
   G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
-  /-- Expansion: `|G(x)| > |x|` [PS10, Definition 77.1 (2)]. -/
+  /-- Expansion: `|G(x)| > |x|` [PS10, Definition 77.1 (2)], at every seed length `n`,
+  `n = 0` included (see the Deviation above). -/
   expands : ∀ n, n < stretch.eval n
 
 namespace PRG
@@ -130,6 +151,13 @@ def Easy (P : PRG) : Prop :=
   ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
     ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
 
+/-- **Efficiency unfolded** [PS10, Definition 77.1 (1)]: `G` is easy iff some polynomial-time
+string function `F` sends every seed string `s` of length `n` to `G n s`. -/
+theorem easy_iff (P : PRG) :
+    P.Easy ↔ ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
+      ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s) :=
+  Iff.rfl
+
 /-- The **output ensemble** `{x ← U_n : G(x)}_n` of a generator [PS10, Definition 77.1 (3)]:
 seeds are the uniform `n`-bit strings and the sampler is `G n`. -/
 def ensemble (P : PRG) : Ensemble P.stretch where
@@ -147,9 +175,8 @@ def Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom
 /-- Unfolding of the output ensemble: the seed type at `n` is `{0,1}^n`. -/
 theorem ensemble_σ (P : PRG) (n : ℕ) : P.ensemble.σ n = (Fin n → Bool) := rfl
 
-/-- The output length of a generator is positive at every seed length (from the expansion
-clause); this is the hypothesis `0 < ℓ(n)` of [PS10, Theorem 75.4] for output ensembles of
-generators. -/
+/-- The output length of a generator is positive at every seed length: `0 < ℓ(n)` for all `n`
+(from the expansion clause `n < ℓ(n)` of [PS10, Definition 77.1 (2)]). -/
 theorem stretch_pos (P : PRG) (n : ℕ) : 0 < P.stretch.eval n :=
   lt_of_le_of_lt (Nat.zero_le n) (P.expands n)
 

### --- B: the 03c repair commit bc2aab59333e27729c9fbac3052cd650bf62c3aa (in #201), outside this pack's files ---
diff --git a/TCSlib/Cryptography/Asymptotic.lean b/TCSlib/Cryptography/Asymptotic.lean
index b49fcc04..15206d5c 100644
--- a/TCSlib/Cryptography/Asymptotic.lean
+++ b/TCSlib/Cryptography/Asymptotic.lean
@@ -14,6 +14,7 @@ import TCSlib.Cryptography.Asymptotic.Universal
 import TCSlib.Cryptography.Asymptotic.Pseudorandom
 import TCSlib.Cryptography.Asymptotic.NextBit
 import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
+import TCSlib.Cryptography.Asymptotic.HardCoreCollection
 import TCSlib.Cryptography.Asymptotic.HardCore
 import TCSlib.Cryptography.Asymptotic.HardCorePermutation
 import TCSlib.Cryptography.Asymptotic.Encryption
@@ -63,6 +64,8 @@ machine-closure facts of `TCSlib/Complexity/Randomized`.
   Algorithm 76.5].
 * `GoldreichLevinDomain` — the concrete Goldreich–Levin bound for `x` uniform on an encoded
   finite domain (the collection form of [PS10, Theorem 87.3]; run-3 audit P4-2).
+* `HardCoreCollection` — Goldreich–Levin for collections of one-way functions and of
+  (trapdoor) permutations [PS10, Theorem 87.3, collection form, as used in Theorem 104.4].
 * `HardCore` — hard-core predicates, the PRG from a one-way permutation, expansion and
   Goldreich–Levin [PS10, Definition 78.3, Theorems 79.4, 87.3, Lemma 80.5, Corollary 81.7].
 * `HardCorePermutation` — the balanced Goldreich–Levin permutation `PermFamily.glHalf`:
diff --git a/TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean b/TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean
index 3f212d16..a5ece521 100644
--- a/TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean
+++ b/TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean
@@ -45,7 +45,7 @@ None: the file proves lemmas about the existing `HardcoreBit.guessRecover`.
 * `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc_pad` — the same bound on the
   sample space `(α × {0,1}^m) × coins` of the padded collection (the padding `r` is carried
   along unused), the form consumed by `Collection.OneWay.glPad_hardCore`
-  (`Asymptotic/HardCore.lean`).
+  (`Asymptotic/HardCoreCollection.lean`).
 
 ## References
 
diff --git a/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean b/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean
index 08830e54..2b655080 100644
--- a/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean
+++ b/TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean
@@ -17,7 +17,7 @@ The collection form of [PS10, Theorem 87.3] (needed by [PS10, Theorem 104.4] and
 if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at
 generated indices, then `⟨encD_i x, r⟩` is hard-core for the padded collection
 `g_i(x, r) = ⟨f_i(x), r⟩`. This file supplies the machine side for
-`Collection.OneWay.glPad_hardCore` (`Asymptotic/HardCore.lean`):
+`Collection.OneWay.glPad_hardCore` (`Asymptotic/HardCoreCollection.lean`):
 
 * the evaluator of the bit `⟨padFin(encD_i x), r⟩` on `⟨i, ⟨encD_i x, r⟩⟩` (`padToLen`, `ipFun`);
 * the recovery machine `glMachine` of `Asymptotic/HardCoreGL.lean` applied to the predictor
diff --git a/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean b/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean
index 1676781e..8ecd4575 100644
--- a/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean
@@ -901,7 +901,8 @@ namespace TCSlib.Cryptography
 
 open Complexity Turing Finset
 
-/-! ## Helpers of the padded families and collections (`Asymptotic/HardCore.lean`) -/
+/-! ## Helpers of the padded families and collections (`Asymptotic/HardCore.lean`,
+`Asymptotic/HardCoreCollection.lean`) -/
 
 /-- The re-encoding `(x ‖ r, c) ↦ ((x, r), c)` of the experiments. -/
 def splitPair (a b : ℕ) (ρ : Type*) :
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index db0e077b..c8459c16 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -392,3 +392,30 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.not_weakOneWay_id
 #print axioms TCSlib.Cryptography.not_worstCaseOneWay_id
 #print axioms TCSlib.Cryptography.FunFamily.not_toCollection_oneWay_id
+
+-- ## Gate 03c repairs (pack 03c: Pseudorandom, NextBit, HardCore, HardCoreClaims, HardCoreCollection)
+-- Finding 2 (ruling G3-7b): Thm 75.4 restated without `0 < ℓ(n)` (its print is above, C3b:
+-- `Ensemble.NextBitUnpredictable.pseudorandom`); the case `ℓ(n) = 0`.
+#print axioms TCSlib.Cryptography.prgAdv_eq_zero_of_length_eq_zero
+-- Finding 6: the claims of `HardCoreClaims.lean`, the pack's two non-vacuity theorems and the
+-- permutation-collection hard-core form.
+#print axioms TCSlib.Cryptography.fact_88_4
+#print axioms TCSlib.Cryptography.thm_87_3_1
+#print axioms TCSlib.Cryptography.thm_87_3_2
+#print axioms TCSlib.Cryptography.thm_87_3_3
+#print axioms TCSlib.Cryptography.thm_87_3_6
+#print axioms TCSlib.Cryptography.thm_87_3_7
+#print axioms TCSlib.Cryptography.thm_87_3_8
+#print axioms TCSlib.Cryptography.thm_87_3_9
+#print axioms TCSlib.Cryptography.not_hardCore_const
+#print axioms TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable
+#print axioms TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore
+-- Finding 11: the unfolding lemmas of the pack's definitions.
+#print axioms TCSlib.Cryptography.PRG.easy_iff
+#print axioms TCSlib.Cryptography.hardCore_iff
+#print axioms TCSlib.Cryptography.PRG.oneBit_stretch
+#print axioms TCSlib.Cryptography.PRG.oneBit_G
+#print axioms TCSlib.Cryptography.owpPredictorSnoc_eq
+#print axioms TCSlib.Cryptography.oneBitStep_eq
+#print axioms TCSlib.Cryptography.expandRed_eq
+#print axioms TCSlib.Cryptography.Collection.glBit_eq
diff --git a/briefs/pass-shelat/DESIGN.md b/briefs/pass-shelat/DESIGN.md
index 65a36662..5bacfec9 100644
--- a/briefs/pass-shelat/DESIGN.md
+++ b/briefs/pass-shelat/DESIGN.md
@@ -689,11 +689,14 @@ once with `uprob_bool_prod`.
 
 ### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes
 
+(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
+`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)
+
 ```lean
 structure PRG where                                           -- [PS10, Def 77.1], length-regular
   stretch : PolyExpr
   G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
-  expands : ∀ n, n < stretch.eval n
+  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
 def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
 def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
 def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom
@@ -702,7 +705,7 @@ noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ)
   uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
 def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
   ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
-theorem Ensemble.NextBitUnpredictable.pseudorandom (hℓ : ∀ n, 0 < ℓ.eval n) (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]
+theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)
 
 def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
   (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
@@ -711,7 +714,12 @@ def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) 
 
 Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
 (79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
-(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator);
+(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
+(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
+(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
+text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
+`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
+carries the cost of §5.25);
 `cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
 (87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
 for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
@@ -1041,6 +1049,17 @@ Issues found in this synthesis and resolved here (not raised by the panel):
     decodes only if it is the encoding of its value — so the outputs of the sampler and of the
     trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
     "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
+25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
+    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
+    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
+    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
+    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
+    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
+    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
+    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
+    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
+    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
+    of ch. 2–8 is vacuous by it.
 
 ---
 
diff --git a/briefs/pass-shelat/inventory-ch3.md b/briefs/pass-shelat/inventory-ch3.md
index 1730a3a1..681ab7d3 100644
--- a/briefs/pass-shelat/inventory-ch3.md
+++ b/briefs/pass-shelat/inventory-ch3.md
@@ -316,6 +316,9 @@ distinguisher `D : (Fin ℓ → Bool) → ρ → Bool`, there exist `i : Fin ℓ
   equals `X s i` or `¬X s i` each with probability `1/2` independently of everything else
   (`uprob_bool_prod` after the bijection `(b, s, u) ↦ (s, update u i (xor b (X s i)))`, as in
   `acceptProb_id_owp`). Hence `|P(H^{i+1}) − P(H̃^{i+1})| ≥ 2 prgAdv/ℓ`.
+  *[Annotation, gate 03c finding 5: that map is 2-to-1 (the original `u_i` is lost), not a
+  bijection; the formal proof adjoins an ignored uniform bit and uses the involution of
+  `uprob_split_bit` in `NextBit.lean` (the run-3 repair labelled P2-3 there).]*
 * predictor analysis: `nextBitProb X i (nextBitPred D i false) = 1/2 + (P(H^{i+1}) − P(H̃^{i+1}))/2`
   — the completed string is a sample of `H^{i+1}` when `u_{i+1} = t_{i+1}` and of `H̃^{i+1}`
   otherwise (Claim-73.a's identity with `X¹ = H^{i+1}`, `X⁰ = H̃^{i+1}`); `flip = true` gives

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/c2/replay.log =====

# closure of pack 03c2's files at e79397eaf68b156b9db091f464741f6eb75b9c28: 95 modules, extracted from replay-combined.log
TCSlib/Complexity/CircuitComplexity/Advice rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Basic rc=0 8s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuit rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGFanin rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGTransform rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredCircuit rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredDAG rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredPPoly rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PPoly rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/SizeClasses rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/TreeDAG rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CoNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CounterProgPolyTime rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/NP rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PClosure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTime rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePrefix rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassP/DTIME rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassP/P rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 2s errors=0 sorry=2
TCSlib/Complexity/PolyHierarchy/Padding rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Complexity/Randomized/PPT rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody rc=0 13s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 50s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 54s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 4s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Composition rc=0 3s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProg rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgInput rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgRun rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 3s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 11s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 6s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UnaryTape rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 60s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/GoldreichLevin rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/InnerProduct rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/ThreeQuarters rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/OutputLength rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Generators rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Indistinguishability rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 2s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/c2/axioms.log =====

# axiom prints of every public theorem and lemma for declarations in pack 03c2's files, at e79397eaf68b156b9db091f464741f6eb75b9c28
TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.uniform_pseudorandom: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.pseudorandom: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PRG.easy_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PRG.ensemble_X: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PRG.ensemble_σ: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PRG.stretch_pos: propext
TCSlib.Cryptography.PRG.secure_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PRG.Easy.samplable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.nextBitProb_nonneg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.nextBitProb_le_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.nextBitUnpredictable_iff_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.nextBitProb_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.completePrefix_prefixOf: propext, Quot.sound
TCSlib.Cryptography.acceptProb_nextBitHybrid_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_nextBitHybrid_self: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_nextBitHybrid_mix: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.nextBitProb_nextBitPred_false: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.nextBitProb_nextBitPred_true: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.prgAdv_eq_zero_of_length_eq_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_nextBitPred: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.nextBitProb_id: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.acceptProb_nextBitDist: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.prgAdv_nextBitDist: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.hardCore_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.HardCore.easy: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.HardCore.hard: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.not_hardCore_const: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PRG.oneBit_stretch: propext
TCSlib.Cryptography.PRG.oneBit_G: propext
TCSlib.Cryptography.owpGenPRG_G_castSucc: propext, Quot.sound
TCSlib.Cryptography.owpGenPRG_G_last: propext, Quot.sound
TCSlib.Cryptography.owpPredictorSnoc_eq: none
TCSlib.Cryptography.exists_owpPredictorSnoc: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owp_hardcore_prg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.oneBitStep_eq: none
TCSlib.Cryptography.PRG.expand_G: propext
TCSlib.Cryptography.expandRed_eq: none
TCSlib.Cryptography.prgAdv_fst: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_expandRed_ge: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.prg_expand: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PermFamily.iterPRG_eq_expand: propext, Quot.sound
TCSlib.Cryptography.cor_81_7: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.glPad_f: propext, Quot.sound
TCSlib.Cryptography.FunFamily.glBit_append: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.predProb_glPad: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.invProb_glInverter: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.glPad_f_bijective: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.StrongOneWay.glPad: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.goldreich_levin: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.fact_88_4: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_1: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_2: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_3: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_6: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_7: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_8: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.thm_87_3_9: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.glBit_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.glPad_gen: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.glPad_f: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.glPad_sample_runAtL: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.glPad_decD_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.OneWay.glPad: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.OneWay.glPad_hardCore: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.goldreich_levin_coll: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PermCollection.glPad_toCollection: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PermCollection.OneWay.glPad: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.TrapdoorCollection.glPad_toPermCollection: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore: propext,  Classical.choice,  Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/c2/admissions.txt =====

# declarations with `sorry` in pack 03c2's files, at e79397eaf68b156b9db091f464741f6eb75b9c28

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/c2/lint.log =====

# scripts/style_lint.py on pack 03c2's files, at e79397eaf68b156b9db091f464741f6eb75b9c28






0 findings in 5 files

## ===== TCSlib/Cryptography/Asymptotic/Pseudorandom.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Ensembles
import TCSlib.Cryptography.Pseudorandom.Generators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom ensembles and pseudorandom generators

The definitions of [PS10, §3.2.1 and §3.3.1]: a *pseudorandom ensemble* is one that is
computationally indistinguishable from the uniform ensemble `{U_{ℓ(n)}}`
[PS10, Definition 74.1], and a *pseudorandom generator* is an efficiently computable,
length-expanding function whose output on a uniform seed is a pseudorandom ensemble
[PS10, Definition 77.1].

`Ensemble.Pseudorandom` itself is the frozen definition of
`TCSlib.Cryptography.Asymptotic.Ensembles` (`Indist X (uniform ℓ)`); this file records that it
is literally "the PRG advantage `prgAdv` of [Gar26] is negligible for every non-uniform PPT"
(`Ensemble.pseudorandom_iff_prgAdv`), that the uniform ensemble is pseudorandom
(non-vacuity), and introduces the generator structure `PRG` with its efficiency clause
`PRG.Easy`, its output ensemble `PRG.ensemble` and the security predicate `PRG.Secure`.

Foundation decisions (`PassShelatChapter2-4Plan.md`): D5 (typed domains at each parameter),
D6 (ensembles are families of samplers), D9 (every length is a syntactic polynomial
`Complexity.PolyExpr`; the stretch `ℓ` of a generator is one).

**Deviation:** `PRG` is *length-regular*: `|G(x)|` depends only on `|x|` and is the syntactic
polynomial `stretch`, so that `G` is a typed family `G n : {0,1}^n → {0,1}^{ℓ(n)}` (the
concrete layer's convention [Gar26, Definition 3.5]); the text's `G : {0,1}* → {0,1}*` with
`|G(x)| > |x|` admits irregular lengths, which no construction of the book uses.

**Deviation:** the expansion clause `PRG.expands` holds at every seed length, `n = 0` included
(the text's `|G(x)| > |x|` read literally at `x = ε`), so no `PolyExpr` stretch with `ℓ(0) = 0`
(exactly `2n`) or `ℓ(1) = 1` (`n^c`) is a `PRG`; the length-doubling generators of the text are
`DoublingPRG` (`Asymptotic/PRF.lean`). See `PRG` (gate 03c, finding 1; ruling G3-2).

**Deviation:** `PRG.Easy`: a deterministic polynomial-time evaluator on the seed string
instead of a PPT computing `G` with probability one (equivalent by `Complexity.NUPPT.Computes`
and `ofPolyTimeUniform`, as for `FunFamily.Easy`); the seed is not prefixed by `1^n` since
its length is the parameter.

## Main definitions

* `TCSlib.Cryptography.PRG` — a length-regular generator with explicit stretch
  [PS10, Definition 77.1 (2)].
* `TCSlib.Cryptography.PRG.Easy` — the efficiency clause [PS10, Definition 77.1 (1)].
* `TCSlib.Cryptography.PRG.ensemble` — the output ensemble `{x ← U_n : G(x)}`.
* `TCSlib.Cryptography.PRG.Secure` — `G` is a pseudorandom generator
  [PS10, Definition 77.1 (1)+(3)].

## Main results

* `TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv` — [PS10, Definition 74.1] is
  "`prgAdv` negligible for every `D`" (the concrete quantity of [Gar26, Definition 3.5]).
* `TCSlib.Cryptography.Ensemble.uniform_pseudorandom` — the uniform ensemble is pseudorandom
  (non-vacuity of Definition 74.1).
* `TCSlib.Cryptography.PRG.easy_iff`, `TCSlib.Cryptography.PRG.secure_iff` — unfoldings of
  `PRG.Easy` and of `PRG.Secure` (the latter to the `prgAdv` form).
* `TCSlib.Cryptography.PRG.Easy.samplable` — the output ensemble of an efficiently
  computable generator is efficiently samplable (D6), so that `Ensemble.Indist.copies`
  applies to it.
* `TCSlib.Cryptography.PRG.stretch_pos` — the output length of a generator is positive at
  every seed length (from the expansion clause).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.1: Definition 74.1; §3.3.1: Definition 77.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3 (Definition 3.5, the concrete `prgAdv`).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Pseudorandom ensembles [PS10, Definition 74.1] -/

/-- **Pseudorandomness is a negligible PRG advantage**: the frozen
`Ensemble.Pseudorandom X := Indist X (uniform ℓ)` [PS10, Definition 74.1] says exactly that
for every non-uniform PPT `D` the concrete PRG advantage
`prgAdv (X_n) D = |Pr[t ← X_n : D(1^n, t) = 1] − Pr[t ← U_{ℓ(n)} : D(1^n, t) = 1]|`
[Gar26, Definition 3.5] is a negligible function of `n`. Definitional: the uniform ensemble
samples by the identity. -/
theorem Ensemble.pseudorandom_iff_prgAdv {ℓ : PolyExpr} (X : Ensemble ℓ) :
    X.Pseudorandom ↔
      ∀ D : NUPPT, Negligible fun n => prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) :=
  Iff.rfl

/-- **The uniform ensemble is pseudorandom** (non-vacuity of [PS10, Definition 74.1]):
`{U_{ℓ(n)}} ≈ {U_{ℓ(n)}}` by reflexivity of `≈`. -/
theorem Ensemble.uniform_pseudorandom (ℓ : PolyExpr) : (Ensemble.uniform ℓ).Pseudorandom :=
  Ensemble.Indist.refl _

/-- Pseudorandomness is preserved by `≈`: if `{X_n} ≈ {Y_n}` and `{Y_n}` is pseudorandom then
so is `{X_n}` (transitivity of `≈`, [PS10, §3.1.1]). -/
theorem Ensemble.Indist.pseudorandom {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y)
    (hY : Y.Pseudorandom) : X.Pseudorandom :=
  h.trans hY

/-! ### Pseudorandom generators [PS10, Definition 77.1] -/

/-- A **(length-regular) generator** with explicit stretch: at every seed length `n`, a
function `G n : {0,1}^n → {0,1}^{ℓ(n)}` with `ℓ(n) > n` (at every `n`, `n = 0` included; see
the second Deviation) — the expansion clause
[PS10, Definition 77.1 (2)] with the output length a syntactic polynomial `stretch` (D9).
The efficiency and pseudorandomness clauses are `PRG.Easy` and `PRG.Secure`.

**Deviation:** `PRG` is *length-regular*: `|G(x)|` depends only on `|x|` and is the syntactic
polynomial `stretch`, so that `G` is a typed family `G n : {0,1}^n → {0,1}^{ℓ(n)}` (the
concrete layer's convention [Gar26, Definition 3.5]); the text's `G : {0,1}* → {0,1}*` with
`|G(x)| > |x|` admits irregular lengths, which no construction of the book uses.

**Deviation:** the expansion clause holds at every seed length, `n = 0` included, as the text's
`|G(x)| > |x|` says literally for `x = ε`. A `PolyExpr` stretch is a polynomial with coefficients
in ℕ, so a stretch with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) is not a `PRG`, although
the text uses such generators (the length-doubling `G` of Algorithm 92.1 and Theorem 97.3;
Lemma 80.5's "for any polynomial `ℓ`"). They are reached up to one bit (`2n + 1`, `n^c + 1`, by
`prg_expand` from the one-bit truncation `PRG.truncate` of `Asymptotic/PRF.lean`) or by truncation
(`PRG.Secure.truncateTo_easy`/`_negligible`, `Asymptotic/PRFLemmas.lean`); the length-doubling
generator of Theorem 97.3 is the separate predicate `DoublingPRG` (`Asymptotic/PRF.lean`),
produced from any secure `PRG` by `PRG.doubling` (`PRG.Secure.doubling`). "PRGs exist" means the
same under either reading, since a generator expanding only from some `n₀` on is made to expand
everywhere by truncating to `n + 1` bits and changing it below `n₀` (a remark, not formalized).
(Gate 03c, finding 1; ruling G3-2; DESIGN §5.25.) -/
structure PRG where
  /-- The output length `ℓ(n)` at seed length `n`. -/
  stretch : PolyExpr
  /-- The generator at seed length `n`. -/
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  /-- Expansion: `|G(x)| > |x|` [PS10, Definition 77.1 (2)], at every seed length `n`,
  `n = 0` included (see the Deviation above). -/
  expands : ∀ n, n < stretch.eval n

namespace PRG

/-- **Efficiency** [PS10, Definition 77.1 (1)]: a polynomial-time string function computes
`G n s` from the seed string `s` (of length `n`).

**Deviation:** `PRG.Easy`: a deterministic polynomial-time evaluator on the seed string
instead of a PPT computing `G` with probability one (equivalent by `Complexity.NUPPT.Computes`
and `ofPolyTimeUniform`, as for `FunFamily.Easy`); the seed is not prefixed by `1^n` since
its length is the parameter. -/
def Easy (P : PRG) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)

/-- **Efficiency unfolded** [PS10, Definition 77.1 (1)]: `G` is easy iff some polynomial-time
string function `F` sends every seed string `s` of length `n` to `G n s`. -/
theorem easy_iff (P : PRG) :
    P.Easy ↔ ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s) :=
  Iff.rfl

/-- The **output ensemble** `{x ← U_n : G(x)}_n` of a generator [PS10, Definition 77.1 (3)]:
seeds are the uniform `n`-bit strings and the sampler is `G n`. -/
def ensemble (P : PRG) : Ensemble P.stretch where
  σ n := Fin n → Bool
  X := P.G

/-- `G` is a **pseudorandom generator** [PS10, Definition 77.1]: efficiently computable
(clause (1)) and its output ensemble is pseudorandom (clause (3)); expansion (clause (2)) is
the field `PRG.expands` of the structure. -/
def Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

/-- Unfolding of the output ensemble: the sampler at `n` is `G n`. -/
@[simp] theorem ensemble_X (P : PRG) (n : ℕ) : P.ensemble.X n = P.G n := rfl

/-- Unfolding of the output ensemble: the seed type at `n` is `{0,1}^n`. -/
theorem ensemble_σ (P : PRG) (n : ℕ) : P.ensemble.σ n = (Fin n → Bool) := rfl

/-- The output length of a generator is positive at every seed length: `0 < ℓ(n)` for all `n`
(from the expansion clause `n < ℓ(n)` of [PS10, Definition 77.1 (2)]). -/
theorem stretch_pos (P : PRG) (n : ℕ) : 0 < P.stretch.eval n :=
  lt_of_le_of_lt (Nat.zero_le n) (P.expands n)

/-- **Security unfolded**: `G` is a secure PRG iff it is easy to compute and for every
non-uniform PPT `D` the PRG advantage `prgAdv (G n) (D(1^n, ·))` [Gar26, Definition 3.5] is
negligible — the form in which the concrete reductions of the Garg layer are consumed. -/
theorem secure_iff (P : PRG) :
    P.Secure ↔ P.Easy ∧
      ∀ D : NUPPT, Negligible fun n => prgAdv (P.G n) (D.distinguisher n (P.stretch.eval n)) :=
  Iff.rfl

/-- **An efficiently computable generator has an efficiently samplable output ensemble**
(D6): the sampler draws `n` uniform bits `r` (`s := var`) and returns `F r` where `F` is the
polynomial-time evaluator; the law of the padded output is exactly that of `G n` on a
uniform seed. This is what makes `Ensemble.Indist.copies` applicable to PRG outputs
[PS10, §3.3.5, the multi-copy argument of Lemma 80.5]. -/
theorem Easy.samplable {P : PRG} (h : P.Easy) : P.ensemble.Samplable := by
  obtain ⟨F, hF, hG⟩ := h
  refine ⟨.var, F ∘ pairSndD, hF.comp polyTimeComputable_pairSndD, fun n => ?_⟩
  have e : (fun r : Fin (PolyExpr.var.eval n) → Bool =>
      padFin (P.stretch.eval n) ((F ∘ pairSndD) (NUPPT.advInput n (List.ofFn r)))) =
      P.ensemble.X n := by
    funext r
    simp [NUPPT.advInput, hG, padFin_ofFn]
  rw [e]
  exact StatClose.refl _

end PRG

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/NextBit.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Pseudorandom
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The next-bit test and its completeness

The *next-bit test* of [PS10, §3.2.2]: an ensemble `{X_n}` over `{0,1}^{ℓ(n)}` passes it if
no non-uniform PPT `A`, given `1^n` and a prefix `t_1 ⋯ t_i` of a sample `t ← X_n`, predicts
the next bit `t_{i+1}` with probability noticeably above `1/2` [PS10, Definition 75.2,
Remark 75.3]. The theorem of the section is its *completeness* [PS10, Theorem 75.4]: an
ensemble that passes the next-bit test is pseudorandom.

The file has two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`).

* **Concrete** (one `ℓ`, samplers `X : σ → Fin ℓ → Bool`, adversaries as functions of the
  input and of uniform coins): the next-bit experiment `nextBitProb`, the hybrids
  `nextBitHybrid X i` (`H^i_n`: the first `i` bits from `X`, the rest uniform) and
  `nextBitHybridFlip X i` (`H̃^{i+1}_n` of the text: bit `i` negated), the next-bit predictor
  `nextBitPred D i flip` of [PS10, Algorithm 76.5], and the exact next-bit reduction
  `exists_nextBitPred`: a distinguisher of `X` from uniform with advantage `ε` yields a
  position `i < ℓ` and a sign `flip` at which the predictor succeeds with probability at
  least `1/2 + ε/ℓ`. The ingredients are the hybrid lemma `hybrid_lemma`
  [PS10, Lemma 71.6], the mixing identity `acceptProb_nextBitHybrid_mix`
  (`H^i = ½ H^{i+1} + ½ H̃^{i+1}`), and the predictor analysis
  `nextBitProb_nextBitPred_false/true` (the identity of [PS10, Lemma 73.8] specialised to the
  two hybrids).
* **Asymptotic**: `Ensemble.NextBitUnpredictable` [PS10, Definition 75.2] and the
  completeness theorem `Ensemble.NextBitUnpredictable.pseudorandom` [PS10, Theorem 75.4],
  proved by instantiating the concrete reduction at each `n` with `ℓ(n) > 0` (where
  `ℓ(n) = 0` no distinguisher has an advantage, `prgAdv_eq_zero_of_length_eq_zero`),
  hard-wiring the sign into the advice of the predictor machine (the position is read off the
  length of the prefix), and finishing with the contradiction idiom
  `not_negligible_iff_exists_polyExpr`.

The implicit converse ("a pseudorandom ensemble passes the next-bit test", the soundness of
the test the text takes for granted) is `nextBitDist` / `prgAdv_nextBitDist` concretely and
`Ensemble.Pseudorandom.nextBitUnpredictable` asymptotically.

**Deviation:** `NextBitUnpredictable`: the position ranges over the existing bits `i < ℓ(n)`
(the text's `i ∈ [0, ℓ(n)]` includes the nonexistent bit `t_{ℓ(n)+1}`); the bound is
`≤ 1/2 + ε(n)` instead of the text's strict `<` (equivalent, `nextBitUnpredictable_iff_lt`);
the predictor receives `1^n` [PS10, Remark 75.3] (D5).

**Deviation:** `nextBitPred` draws `ℓ(n)` uniform bits and ignores the first `i` (the text's
`U_{ℓ(n)−1}` is a typo for `U_{ℓ(n)−i}`; a coin polynomial independent of `i` keeps one
coin type per `n` in the machine layer, D3).

**Repair (run-3 audit P2-2):** `NextBitUnpredictable.pseudorandom` is stated in its frozen
shape (DESIGN.md §2.12); the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` is now the field
`Ensemble.nonempty` (with an empty seed type the experiment has probability `0`, the ensemble
passes the next-bit test vacuously, and the always-accepting distinguisher has advantage `1`).

**Repair (gate 03c, finding 2; ruling G3-7b):** `NextBitUnpredictable.pseudorandom` no longer
assumes `0 < ℓ(n)` for every `n` (a hypothesis the text does not have, which excluded every
ensemble with `ℓ(0) = 0`); it is now the source's statement. Where `ℓ(n) = 0` both `X_n` and
`U_0` are the point mass on the empty string, and the proof needs a position only where
`ℓ(n) > 0`.

## Main definitions

* `TCSlib.Cryptography.nextBitProb` — the next-bit experiment at one parameter.
* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable` — passing the next-bit test
  [PS10, Definition 75.2, Remark 75.3].
* `TCSlib.Cryptography.prefixOf`, `TCSlib.Cryptography.completePrefix` — prefix of length
  `i` and its completion by uniform bits.
* `TCSlib.Cryptography.nextBitHybrid`, `TCSlib.Cryptography.nextBitHybridFlip` — the hybrids
  `H^i_n` and `H̃^{i+1}_n` of the proof of [PS10, Theorem 75.4].
* `TCSlib.Cryptography.nextBitPred` — the next-bit predictor [PS10, Algorithm 76.5].
* `TCSlib.Cryptography.nextBitDist` — the distinguisher built from a next-bit predictor
  (soundness direction).

## Main results

* `TCSlib.Cryptography.exists_nextBitPred` — the concrete next-bit reduction
  (`1/2 + prgAdv X D / ℓ ≤` predictor success for some `i < ℓ` and some sign);
  `TCSlib.Cryptography.prgAdv_eq_zero_of_length_eq_zero` — no advantage on `{0,1}^0`.
* `TCSlib.Cryptography.acceptProb_nextBitHybrid_zero`,
  `TCSlib.Cryptography.acceptProb_nextBitHybrid_self`,
  `TCSlib.Cryptography.acceptProb_nextBitHybrid_mix` — the hybrid identities
  `H^0 = U_ℓ`, `H^ℓ = X_n`, `H^i = ½ H^{i+1} + ½ H̃^{i+1}`.
* `TCSlib.Cryptography.nextBitProb_nextBitPred_false`,
  `TCSlib.Cryptography.nextBitProb_nextBitPred_true` — the predictor analysis.
* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom` — completeness of the
  next-bit test [PS10, Theorem 75.4].
* `TCSlib.Cryptography.nextBitProb_id`, `TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable`
  — the uniform ensemble passes the next-bit test with probability exactly `1/2`
  (non-vacuity).
* `TCSlib.Cryptography.prgAdv_nextBitDist`,
  `TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable` — soundness of the test.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.2: Definition 75.2, Remark 75.3, Theorem 75.4, Algorithm 76.5; §3.1.1: Lemmas 71.6,
  73.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3 (Definition 3.5; the predictor-from-distinguisher pattern of
  Theorem 3.2 and the hybrid pattern of Theorem 3.1).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The next-bit experiment and the next-bit test [PS10, Definition 75.2] -/

/-- **The next-bit experiment** at one parameter: the probability, over a uniform seed `s` of
the sampler `X : σ → {0,1}^ℓ` and uniform coins `r`, that the predictor `A`, given the prefix
of length `i` of `t = X s`, outputs bit `i` of `t` — the quantity
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}]` of [PS10, Definition 75.2] with `0`-indexed bits
(prefix of length `i`, predicted bit `i`). -/
noncomputable def nextBitProb {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i

/-- **Passing the next-bit test** [PS10, Definition 75.2]: for every non-uniform PPT `A` there
is a negligible `ε` such that for all `n` and all positions `i < ℓ(n)`,
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}] ≤ 1/2 + ε(n)`. The predictor is the machine `A`
activated at parameter `n` on `⟨1^n, t_1 ⋯ t_i⟩` (`A.predictor n i`), which is the convention
of [PS10, Remark 75.3]: `A` receives `1^n` so that its size and running time may be polynomial
in `n` rather than in the possibly short prefix. The quantifier order `∀ A ∃ ε ∀ n ∀ i` is the
text's (one negligible function for all positions).

**Deviation:** `NextBitUnpredictable`: the position ranges over the existing bits `i < ℓ(n)`
(the text's `i ∈ [0, ℓ(n)]` includes the nonexistent bit `t_{ℓ(n)+1}`); the bound is
`≤ 1/2 + ε(n)` instead of the text's strict `<` (equivalent, `nextBitUnpredictable_iff_lt`);
the predictor receives `1^n` [PS10, Remark 75.3] (D5). -/
def Ensemble.NextBitUnpredictable {ℓ : PolyExpr} (X : Ensemble ℓ) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1 / 2 + ε n

/-- The next-bit success probability is nonnegative. -/
theorem nextBitProb_nonneg {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    0 ≤ nextBitProb X i A :=
  uprob_nonneg _

/-- The next-bit success probability is at most one. -/
theorem nextBitProb_le_one {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    nextBitProb X i A ≤ 1 :=
  uprob_le_one _

/-- **The text's strict form of Definition 75.2** — "there exists a negligible `ε` with
success `< 1/2 + ε(n)` for all `n` and `i`" — is equivalent to the frozen `≤` form
[PS10, Definition 75.2]: one direction is `le_of_lt`, the other replaces `ε(n)` by
`ε(n) + 2^{-n}`. -/
theorem Ensemble.nextBitUnpredictable_iff_lt {ℓ : PolyExpr} (X : Ensemble ℓ) :
    X.NextBitUnpredictable ↔ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) < 1 / 2 + ε n := by
  constructor
  · intro h A
    obtain ⟨ε, hε, hle⟩ := h A
    refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n i => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith [hle n i]
  · intro h A
    obtain ⟨ε, hε, hlt⟩ := h A
    exact ⟨ε, hε, fun n i => (hlt n i).le⟩

/-! ### Prefixes and their completion -/

/-- The prefix of length `i` of an `ℓ`-bit string (`t_1 ⋯ t_i` of [PS10, Definition 75.2],
`0`-indexed). -/
def prefixOf {ℓ : ℕ} (i : Fin ℓ) (x : Fin ℓ → Bool) : Fin i → Bool :=
  fun j => x (Fin.castLE i.isLt.le j)

/-- Completion of a prefix `t` of length `i` by the bits `u_i ⋯ u_{ℓ-1}` of a string `u`:
the string `t_1 ⋯ t_i u_{i+1} ⋯ u_ℓ` fed to the distinguisher in [PS10, Algorithm 76.5]. -/
def completePrefix {ℓ : ℕ} (i : Fin ℓ) (t : Fin i → Bool) (u : Fin ℓ → Bool) : Fin ℓ → Bool :=
  fun j => if h : (j : ℕ) < i then t ⟨j, h⟩ else u j

/-- The next-bit experiment, written with `prefixOf` (definitional unfolding). -/
theorem nextBitProb_eq {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    nextBitProb X i A = uprob fun z : σ × ρ => A (prefixOf i (X z.1)) z.2 = X z.1 i :=
  rfl

/-- Completing the prefix of `x` by `u` gives `x` on the first `i` positions and `u` after. -/
theorem completePrefix_prefixOf {ℓ : ℕ} (i : Fin ℓ) (x u : Fin ℓ → Bool) :
    completePrefix i (prefixOf i x) u = fun j : Fin ℓ => if (j : ℕ) < i then x j else u j := by
  funext j
  unfold completePrefix prefixOf
  by_cases h : (j : ℕ) < i
  · simp only [h, dite_true, if_true]
    congr 1
  · simp [h]

/-! ### The hybrids of the proof of Theorem 75.4 -/

/-- The hybrid `H^i_n = {x ← X_n; u ← U_ℓ : x_1 ⋯ x_i u_{i+1} ⋯ u_ℓ}` of the proof of
[PS10, Theorem 75.4]: the first `i` bits from the sample, the remaining bits uniform. All
hybrids share the seed space `σ × {0,1}^ℓ` (the unused coordinates are ignored), so that
`H^0 = U_ℓ` and `H^ℓ = X_n` hold as identities of acceptance probabilities. -/
def nextBitHybrid {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : ℕ) :
    σ × (Fin ℓ → Bool) → Fin ℓ → Bool :=
  fun z j => if (j : ℕ) < i then X z.1 j else z.2 j

/-- The flipped hybrid `H̃^{i+1}_n = {x ← X_n; u ← U_ℓ : x_1 ⋯ x_i x̄_{i+1} u_{i+2} ⋯ u_ℓ}`
of the proof of [PS10, Theorem 75.4] (`0`-indexed: bit `i` is the negation of `x_i`). The
text's display of `H̃^i_n` carries a stray `u_{ℓ(m)}` and mixes the indexings; this is the
distribution its argument uses. -/
def nextBitHybridFlip {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : ℕ) :
    σ × (Fin ℓ → Bool) → Fin ℓ → Bool :=
  fun z j => if (j : ℕ) < i then X z.1 j else if (j : ℕ) = i then !X z.1 j else z.2 j

/-- **`H^0_n = U_ℓ`**: the zeroth hybrid is uniform (the sample is ignored). -/
theorem acceptProb_nextBitHybrid_zero {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    acceptProb (nextBitHybrid X 0) D = acceptProb (id : (Fin ℓ → Bool) → _) D := by
  have h : nextBitHybrid X 0 = fun z : σ × (Fin ℓ → Bool) => z.2 := by
    funext z j
    simp [nextBitHybrid]
  rw [h]
  exact acceptProb_snd (fun u : Fin ℓ → Bool => u) D

/-- **`H^ℓ_n = X_n`**: the last hybrid is the sample itself (the uniform bits are ignored). -/
theorem acceptProb_nextBitHybrid_self {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    acceptProb (nextBitHybrid X ℓ) D = acceptProb X D := by
  have h : nextBitHybrid X ℓ = fun z : σ × (Fin ℓ → Bool) => X z.1 := by
    funext z j
    simp [nextBitHybrid, j.isLt]
  rw [h]
  exact acceptProb_fst X D

/-- **Bit `i` of a uniform string is a uniform bit, independent of everything else**: for
every event `p` on `(σ × {0,1}^ℓ) × ρ` and every bit `g s` depending on the first seed,
`Pr[p] = ½ Pr[p ∘ (plant g s at bit i)] + ½ Pr[p ∘ (plant ḡ s at bit i)]`. This is the
"`H^i` is sampled by drawing from `H^{i+1}` or from `H̃^{i+1}` with probability `1/2`" step of
the proof of [PS10, Theorem 75.4], in a form shared by the mixing identity and the predictor
analysis. (The planting map `(b, (s, u), r) ↦ ((s, update u i (b ⊕ g s)), r)` is 2-to-1, not a
bijection — a run-3 repair, labelled P2-3 here and noted at gate 03c, finding 5 — so the
proof adjoins an ignored uniform bit instead.)

**Proof sketch.** Adjoin an ignored uniform bit `b` (`uprob_fst` after `Equiv.prodComm`),
then apply the involution `ψ (b, (s, u), r) := (u_i ⊕ g s, (s, update u i (b ⊕ g s)), r)` of
`Bool × ((σ × {0,1}^ℓ) × ρ)` (`uprob_comp_equiv`; `ψ ∘ ψ = id` by `Function.update_idem`,
`Function.update_self`, `Function.update_eq_self`) and split on `b` with `uprob_bool_prod`:
the `b = false` section plants `g s`, the `b = true` section plants `!g s`. -/
private theorem uprob_split_bit {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ} (i : Fin ℓ)
    (g : σ → Bool) (p : (σ × (Fin ℓ → Bool)) × ρ → Prop) :
    uprob p = (uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
        p ((z.1.1, Function.update z.1.2 i (g z.1.1)), z.2)) +
      uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
        p ((z.1.1, Function.update z.1.2 i (!g z.1.1)), z.2))) / 2 := by
  have h1 : uprob (fun w : Bool × ((σ × (Fin ℓ → Bool)) × ρ) => p w.2) = uprob p := by
    rw [← uprob_comp_equiv (Equiv.prodComm ((σ × (Fin ℓ → Bool)) × ρ) Bool)
      (fun w : Bool × ((σ × (Fin ℓ → Bool)) × ρ) => p w.2)]
    exact uprob_fst p
  let ψ : Bool × ((σ × (Fin ℓ → Bool)) × ρ) ≃ Bool × ((σ × (Fin ℓ → Bool)) × ρ) :=
    { toFun := fun w => (xor (w.2.1.2 i) (g w.2.1.1),
        ((w.2.1.1, Function.update w.2.1.2 i (xor w.1 (g w.2.1.1))), w.2.2))
      invFun := fun w => (xor (w.2.1.2 i) (g w.2.1.1),
        ((w.2.1.1, Function.update w.2.1.2 i (xor w.1 (g w.2.1.1))), w.2.2))
      left_inv := fun w => by
        obtain ⟨b, ⟨s, u⟩, r⟩ := w
        simp [Function.update_idem]
      right_inv := fun w => by
        obtain ⟨b, ⟨s, u⟩, r⟩ := w
        simp [Function.update_idem] }
  rw [← h1, ← uprob_comp_equiv ψ, uprob_bool_prod]
  simp only [ψ, Equiv.coe_fn_mk, Bool.false_xor, Bool.true_xor]

/-- Planting `x_i` at position `i` of the uniform part of `H^i` gives `H^{i+1}`:
`nextBitHybrid X i (s, update u i (X s i)) = nextBitHybrid X (i+1) (s, u)` (case split on
`j < i`, `j = i`, `j > i`). -/
private theorem nextBitHybrid_update_eq {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ)
    (s : σ) (u : Fin ℓ → Bool) :
    nextBitHybrid X i (s, Function.update u i (X s i)) = nextBitHybrid X (i + 1) (s, u) := by
  funext j
  simp only [nextBitHybrid]
  rcases lt_trichotomy (j : ℕ) i with hj | hj | hj
  · simp [hj, Nat.lt_succ_of_lt hj]
  · have hji : j = i := Fin.ext hj
    subst hji
    simp
  · have hne : j ≠ i := fun h => by rw [h] at hj; exact lt_irrefl _ hj
    simp [not_lt.mpr hj.le, Function.update_of_ne hne, show ¬ ((j : ℕ) < (i : ℕ) + 1) by omega]

/-- Planting `x̄_i` at position `i` of the uniform part of `H^i` gives the flipped hybrid
`H̃^{i+1}`: `nextBitHybrid X i (s, update u i (!X s i)) = nextBitHybridFlip X i (s, u)`. -/
private theorem nextBitHybrid_update_not_eq {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool)
    (i : Fin ℓ) (s : σ) (u : Fin ℓ → Bool) :
    nextBitHybrid X i (s, Function.update u i (!X s i)) = nextBitHybridFlip X i (s, u) := by
  funext j
  simp only [nextBitHybrid, nextBitHybridFlip]
  rcases lt_trichotomy (j : ℕ) i with hj | hj | hj
  · simp [hj]
  · have hji : j = i := Fin.ext hj
    subst hji
    simp
  · have hne : j ≠ i := fun h => by rw [h] at hj; exact lt_irrefl _ hj
    simp [not_lt.mpr hj.le, Function.update_of_ne hne, hj.ne']

/-- Completing the prefix of the sample `X s` by `v` is the hybrid `H^i` at the seed `(s, v)`:
the string `completePrefix i (prefixOf i (X s)) v` fed to `D` by the predictor is
`nextBitHybrid X i (s, v)` (`completePrefix_prefixOf`). -/
private theorem completePrefix_prefixOf_eq {σ : Type*} {ℓ : ℕ} (X : σ → Fin ℓ → Bool)
    (i : Fin ℓ) (s : σ) (v : Fin ℓ → Bool) :
    completePrefix i (prefixOf i (X s)) v = nextBitHybrid X i (s, v) := by
  rw [completePrefix_prefixOf]
  rfl

/-- **The mixing identity** `H^i_n = ½ H^{i+1}_n + ½ H̃^{i+1}_n` of the proof of
[PS10, Theorem 75.4]: the acceptance probability of `D` on the hybrid `H^i` is the average
of its acceptance probabilities on `H^{i+1}` and on the flipped hybrid `H̃^{i+1}`, because
bit `i` of `H^i` is a uniform bit, which equals `x_i` or `x̄_i` each with probability `1/2`
independently of everything else.

**Proof sketch.** `uprob_split_bit` at position `i` with the bit `x_i = X s i`: the
acceptance event on `H^i` is the average of the same event with `x_i` planted at bit `i` of
`u` and with `x̄_i` planted there. Planting `x_i` turns `H^i` into `H^{i+1}`
(`nextBitHybrid_update_eq`) and planting `x̄_i` turns it into `H̃^{i+1}`
(`nextBitHybrid_update_not_eq`); read off the two halves (`OneWay.uprob_congr`). (The
run-2 sketch transported the event along a 2-to-1 "bijection"; see `uprob_split_bit`.) -/
theorem acceptProb_nextBitHybrid_mix {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
    acceptProb (nextBitHybrid X i) D =
      (acceptProb (nextBitHybrid X (i + 1)) D + acceptProb (nextBitHybridFlip X i) D) / 2 := by
  unfold acceptProb
  rw [uprob_split_bit i (fun s => X s i) (fun z => D (nextBitHybrid X i z.1) z.2 = true)]
  have hA : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      D (nextBitHybrid X i (z.1.1, Function.update z.1.2 i (X z.1.1 i))) z.2 = true) =
      uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ => D (nextBitHybrid X (i + 1) z.1) z.2 = true) := by
    apply OneWay.uprob_congr
    intro z
    rw [nextBitHybrid_update_eq]
  have hB : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      D (nextBitHybrid X i (z.1.1, Function.update z.1.2 i (!X z.1.1 i))) z.2 = true) =
      uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ => D (nextBitHybridFlip X i z.1) z.2 = true) := by
    apply OneWay.uprob_congr
    intro z
    rw [nextBitHybrid_update_not_eq]
  rw [hA, hB]

/-! ### The next-bit predictor [PS10, Algorithm 76.5] -/

/-- **The next-bit predictor** `A'(1^n, t_1 ⋯ t_i)` of [PS10, Algorithm 76.5], built from a
distinguisher `D`: draw uniform bits `u` and coins `c` for `D`, run
`g ← D(t_1 ⋯ t_i u_{i+1} ⋯ u_ℓ; c)`, output `u_{i+1}` if `g = 1` and `ū_{i+1}` otherwise;
with `flip = true` the output is negated (the text applies the prediction lemma, which
chooses between a machine and its negation; here the sign is the parameter `flip`,
non-uniform advice in the asymptotic layer, as for `owpPredictor`). It makes one call to
`D`. Coins: `ℓ` uniform bits (of which the first `i` are unused) and `D`'s coins.

**Deviation:** `nextBitPred` draws `ℓ(n)` uniform bits and ignores the first `i` (the text's
`U_{ℓ(n)−1}` is a typo for `U_{ℓ(n)−i}`; a coin polynomial independent of `i` keeps one
coin type per `n` in the machine layer, D3). -/
def nextBitPred {ρ : Type*} {ℓ : ℕ} (D : (Fin ℓ → Bool) → ρ → Bool) (i : Fin ℓ) (flip : Bool) :
    (Fin i → Bool) → (Fin ℓ → Bool) × ρ → Bool :=
  fun t c => xor (if D (completePrefix i t c.1) c.2 then c.1 i else !c.1 i) flip

/-- **Predictor analysis, positive sign**: `nextBitPred D i false` predicts bit `i` of `X`
from the prefix of length `i` with probability exactly
`1/2 + (Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]) / 2` — the last display of the proof of
[PS10, Theorem 75.4] (which writes `A(t) = 1` for `A(t) = b`), i.e. the identity of
[PS10, Lemma 73.8] (`predict_eq`) with `X¹ := H^{i+1}` and `X⁰ := H̃^{i+1}`.

**Proof sketch.** Reassociate the sample space to `(σ × {0,1}^ℓ) × ρ` (`Equiv.prodAssoc`) and
apply `uprob_split_bit` at position `i` with the bit `x_i = X s i` (an adjoined uniform bit and
the involution `ψ`): the success probability is the average of the success event with `x_i`
planted at bit `i` of `u` and with `x̄_i` planted there. With `x_i` planted, the completed
string `completePrefix i (prefixOf i (X s)) u` is `nextBitHybrid X (i+1) (s, u)`
(`completePrefix_prefixOf_eq`, `nextBitHybrid_update_eq`) and the predictor, which outputs
`u_i = x_i` on acceptance, is right iff `D` accepts; with `x̄_i` planted the completed string is
`nextBitHybridFlip X i (s, u)` (`nextBitHybrid_update_not_eq`) and the predictor is right iff
`D` rejects (`uprob_not`, which needs the nonemptiness hypotheses). Average the two:
`(Pr[D(H^{i+1}) = 1] + 1 − Pr[D(H̃^{i+1}) = 1]) / 2`. (The run-2 sketch transported the event
along the 2-to-1 map `(b, (s, u), c) ↦ (s, (update u i (b ⊕ x_i), c))`; see `uprob_split_bit`.) -/
theorem nextBitProb_nextBitPred_false {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    [Nonempty ρ] {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
    nextBitProb X i (nextBitPred D i false) =
      1 / 2 + (acceptProb (nextBitHybrid X (i + 1)) D -
        acceptProb (nextBitHybridFlip X i) D) / 2 := by
  rw [nextBitProb_eq, ← uprob_comp_equiv (Equiv.prodAssoc σ (Fin ℓ → Bool) ρ)
    (fun z : σ × ((Fin ℓ → Bool) × ρ) => nextBitPred D i false (prefixOf i (X z.1)) z.2 = X z.1 i)]
  simp only [Equiv.prodAssoc_apply]
  rw [uprob_split_bit i (fun s => X s i) (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
    nextBitPred D i false (prefixOf i (X z.1.1)) (z.1.2, z.2) = X z.1.1 i)]
  dsimp only
  have hA : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      nextBitPred D i false (prefixOf i (X z.1.1)) (Function.update z.1.2 i (X z.1.1 i), z.2) =
        X z.1.1 i) = acceptProb (nextBitHybrid X (i + 1)) D := by
    unfold acceptProb
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, completePrefix_prefixOf_eq, nextBitHybrid_update_eq,
      Function.update_self, Bool.xor_false]
    cases D (nextBitHybrid X (i + 1) z.1) z.2 <;> cases X z.1.1 i <;> simp
  have hB : uprob (fun z : (σ × (Fin ℓ → Bool)) × ρ =>
      nextBitPred D i false (prefixOf i (X z.1.1)) (Function.update z.1.2 i (!X z.1.1 i), z.2) =
        X z.1.1 i) = 1 - acceptProb (nextBitHybridFlip X i) D := by
    unfold acceptProb
    rw [← uprob_not]
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, completePrefix_prefixOf_eq, nextBitHybrid_update_not_eq,
      Function.update_self, Bool.xor_false]
    cases D (nextBitHybridFlip X i z.1) z.2 <;> cases X z.1.1 i <;> simp
  rw [hA, hB]
  ring

/-- **Predictor analysis, negative sign**: `nextBitPred D i true` predicts bit `i` with
probability exactly `1/2 − (Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]) / 2`, the case the
text's appeal to the prediction lemma covers by choosing the negated machine.

**Proof sketch.** The output of `nextBitPred D i true` is the negation of that of
`nextBitPred D i false` (`Bool.xor_true`), so its success probability is one minus that of
`nextBitProb_nextBitPred_false` (`uprob_not`; nonemptiness is needed for the complement). -/
theorem nextBitProb_nextBitPred_true {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    [Nonempty ρ] {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (D : (Fin ℓ → Bool) → ρ → Bool) :
    nextBitProb X i (nextBitPred D i true) =
      1 / 2 - (acceptProb (nextBitHybrid X (i + 1)) D -
        acceptProb (nextBitHybridFlip X i) D) / 2 := by
  have h : nextBitProb X i (nextBitPred D i true) =
      1 - nextBitProb X i (nextBitPred D i false) := by
    unfold nextBitProb
    rw [← uprob_not]
    apply OneWay.uprob_congr
    intro z
    simp only [nextBitPred, Bool.xor_true, Bool.xor_false]
    cases (if D (completePrefix i (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2.1) z.2.2 then z.2.1 i
      else !z.2.1 i) <;> cases X z.1 i <;> simp
  rw [h, nextBitProb_nextBitPred_false]
  ring

/-- The PRG advantage is the gap between the extreme hybrids: `prgAdv X D =
|Pr[D(H^0) = 1] − Pr[D(H^ℓ) = 1]|`, by `H^0 = U_ℓ` (`acceptProb_nextBitHybrid_zero`) and
`H^ℓ = X` (`acceptProb_nextBitHybrid_self`). -/
private theorem prgAdv_eq_abs_nextBitHybrid {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    {ℓ : ℕ} (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    prgAdv X D = |acceptProb (nextBitHybrid X 0) D - acceptProb (nextBitHybrid X ℓ) D| := by
  unfold prgAdv distAdv
  rw [acceptProb_nextBitHybrid_zero, acceptProb_nextBitHybrid_self, abs_sub_comm]

/-- **No advantage on the empty string**: if `ℓ = 0`, then every distinguisher `D` has PRG
advantage `0` against every sampler `X` into `{0,1}^ℓ` (both `X` and the uniform `U_0` are the
point mass on the empty string). This is the case `ℓ(n) = 0` of [PS10, Theorem 75.4], which
needs no position.

**Proof sketch.** With `ℓ = 0` the two extreme hybrids `H^0` and `H^ℓ` coincide, so the gap
`prgAdv_eq_abs_nextBitHybrid` is `|a − a| = 0`. -/
theorem prgAdv_eq_zero_of_length_eq_zero {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ]
    {ℓ : ℕ} (hℓ : ℓ = 0) (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    prgAdv X D = 0 := by
  subst hℓ
  rw [prgAdv_eq_abs_nextBitHybrid, sub_self, abs_zero]

/-- **The next-bit reduction, concrete form** (the content of the proof of
[PS10, Theorem 75.4] at one parameter): for every sampler `X` into `{0,1}^ℓ` with `ℓ > 0` and
every distinguisher `D` with PRG advantage `ε = prgAdv X D` against `X`, there are a position
`i < ℓ` and a sign `flip` such that the next-bit predictor `nextBitPred D i flip`
[PS10, Algorithm 76.5] predicts bit `i` of `X` from the prefix of length `i` with probability
at least `1/2 + ε/ℓ`. (The text obtains `1/2 + 1/(p(n)ℓ(n))` from `ε = 1/p(n)`.)

**Proof sketch.** `prgAdv X D = |Pr[D(H^0) = 1] − Pr[D(H^ℓ) = 1]|`
(`prgAdv_eq_abs_nextBitHybrid`); the hybrid lemma
`hybrid_lemma` (`exists_hybrid_gap`) over `i ↦ acceptProb (nextBitHybrid X i) D` gives
`i < ℓ` with `ε/ℓ ≤ |Pr[D(H^i) = 1] − Pr[D(H^{i+1}) = 1]|`. By the mixing identity
`acceptProb_nextBitHybrid_mix`, `Pr[D(H^i) = 1] − Pr[D(H^{i+1}) = 1] =
(Pr[D(H̃^{i+1}) = 1] − Pr[D(H^{i+1}) = 1]) / 2`, so
`δ := Pr[D(H^{i+1}) = 1] − Pr[D(H̃^{i+1}) = 1]` has `|δ| ≥ 2ε/ℓ`. If `0 ≤ δ` take
`flip := false` and `nextBitProb_nextBitPred_false` gives success `1/2 + δ/2 ≥ 1/2 + ε/ℓ`;
otherwise `flip := true` and `nextBitProb_nextBitPred_true` gives `1/2 − δ/2 ≥ 1/2 + ε/ℓ`
(`le_total`, `abs_of_nonneg`/`abs_of_neg`, `div_le_iff₀`). -/
theorem exists_nextBitPred {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty σ] [Nonempty ρ]
    {ℓ : ℕ} (hℓ : 0 < ℓ) (X : σ → Fin ℓ → Bool) (D : (Fin ℓ → Bool) → ρ → Bool) :
    ∃ (i : Fin ℓ) (flip : Bool),
      1 / 2 + prgAdv X D / ℓ ≤ nextBitProb X i (nextBitPred D i flip) := by
  have hadv := prgAdv_eq_abs_nextBitHybrid X D
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun j => acceptProb (nextBitHybrid X j) D) hℓ
  have hmix := acceptProb_nextBitHybrid_mix X ⟨k, hk⟩ D
  have hδ : prgAdv X D / ℓ ≤ |acceptProb (nextBitHybrid X (k + 1)) D -
      acceptProb (nextBitHybridFlip X k) D| / 2 := by
    rw [hadv]
    refine hgap.trans (le_of_eq ?_)
    rw [hmix, abs_sub_comm, ← abs_two, ← abs_div]
    congr 1
    ring
  rcases le_total 0 (acceptProb (nextBitHybrid X (k + 1)) D -
      acceptProb (nextBitHybridFlip X k) D) with h | h
  · refine ⟨⟨k, hk⟩, false, ?_⟩
    rw [nextBitProb_nextBitPred_false]
    rw [abs_of_nonneg h] at hδ
    dsimp only
    linarith
  · refine ⟨⟨k, hk⟩, true, ?_⟩
    rw [nextBitProb_nextBitPred_true]
    rw [abs_of_nonpos h] at hδ
    dsimp only
    linarith

/-! ### String forms of prefixes and completions -/

/-- The string form of `completePrefix`: the completed string `t_1 ⋯ t_i u_{i+1} ⋯ u_ℓ` is the
list `ofFn t ++ (ofFn u).drop i` — the word `w` the predictor machine of
[PS10, Algorithm 76.5] hands to `D` (elementwise, `List.ext_getElem`). -/
private theorem ofFn_completePrefix {ℓ : ℕ} (i : Fin ℓ) (t : Fin i → Bool) (u : Fin ℓ → Bool) :
    List.ofFn (completePrefix i t u) = List.ofFn t ++ (List.ofFn u).drop i := by
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_append, List.length_drop]; omega)
    fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_drop,
    completePrefix]
  by_cases hj : j < (i : ℕ)
  · simp [hj]
  · simp only [hj, dite_false]
    congr 1
    ext
    simp
    omega

/-- The string form of `prefixOf`: the prefix of length `i` of `t` is `(ofFn t).take i`
(elementwise, `List.ext_getElem`). -/
private theorem ofFn_prefixOf {ℓ : ℕ} (i : Fin ℓ) (t : Fin ℓ → Bool) :
    List.ofFn (prefixOf i t) = (List.ofFn t).take i := by
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
    fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_take, prefixOf]
  rfl

/-- Bit `i` of `u` is the head of the suffix `(ofFn u).drop i` — the readout
`StateLoop.headBit_poly` of the machines below (`List.head?_drop`, `List.getElem?_ofFn`). -/
private theorem headD_drop_ofFn {ℓ : ℕ} (i : Fin ℓ) (u : Fin ℓ → Bool) :
    ((List.ofFn u).drop i).headD false = u i := by
  rw [List.headD_eq_head?, List.head?_drop, List.getElem?_ofFn]
  simp [i.isLt]

/-- A distinguisher whose coin string is reindexed by a bijection has the same acceptance
probability (`uprob_comp_equiv` on the coin factor of the sample space). -/
private theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (e : ρ ≃ ρ') (D : γ → ρ' → Bool) (D' : γ → ρ → Bool)
    (h : ∀ x r, D x (e r) = D' x r) : acceptProb X D = acceptProb X D' := by
  unfold acceptProb
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl σ) e)]
  apply OneWay.uprob_congr
  intro z
  simp [h]

/-! ### Completeness of the next-bit test [PS10, Theorem 75.4] -/

/-- **The next-bit predictor as a machine** [PS10, Algorithm 76.5]: for a distinguisher
machine `D` and signs `flip n`, a non-uniform PPT `A` with coins `ℓ + D.coins` and advice
`⟨D.advice n, [flip n]⟩` such that, at every parameter `n` and every position `i < ℓ(n)`, `A`
on the prefix `t` with coins `(u, c)` (split by `e n`) is exactly the concrete predictor
`nextBitPred (D.distinguisher n (ℓ n)) i (flip n) t (u, c)`: it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `u_{|t|}` or its negation according to the verdict,
negated once more if `flip n`. The position is read off the prefix length `|t| = i`, so only
the sign is hard-wired, and the identity holds at every position (restated so at gate 03c,
finding 2: no choice of position is needed where `ℓ(n) = 0`).

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨D.advice n, [flip n]⟩⟩, r⟩`
cuts `r` into `u := r.take (ℓ n)` and `c := r.drop (ℓ n)` (`polyTimeComputable_pairTakePoly`/
`pairDropPoly ℓ` on `⟨1^n, r⟩`), forms `w := y ++ u.drop |y|` (`pairDropPoly var` on `⟨y, u⟩`,
`PolyTimeComputable.append`), runs `D.output` on `layout 1^n w (D.advice n) c`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), tests the verdict against
`[true]` (`polyTimeComputable_pairEq`), reads `u_{|y|}` as the head of `u.drop |y|` and the sign
as the head of the advice's second component (`StateLoop.headBit_poly`), and combines them
(`polyTimeComputable_ite`, `StateLoop.not_poly`, `StateLoop.xor_poly`). `A := ofPolyTime` of
it with coins `add ℓ D.coins` and advice bound `2·D.adv + 3` (`length_pairEncode`); the coin
split is `Fin.appendEquiv` composed with `finCongr`, and the identity is `runAtL_ofPolyTime`,
the projection identities of the layout, `List.take_left'`/`List.drop_left'`,
`ofFn_completePrefix` and `headD_drop_ofFn`. -/
private theorem exists_nextBitPredMachine (ℓ : PolyExpr) (D : NUPPT) (flip : ℕ → Bool) :
    ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
      ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
        A.predictor n i t (e n (u, c)) =
          nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n) t (u, c) := by
  -- the coin cut `⟨1^n, r⟩ ↦ u = r.take (ℓ n)`, `c = r.drop (ℓ n)`
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hu : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairTakePoly ℓ).comp hcut using 1
    funext z
    simp
  have hc : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairDropPoly ℓ).comp hcut using 1
    funext z
    simp
  -- the suffix `u.drop |y|` and the completed word `w = y ++ u.drop |y|`
  have hud : PolyTimeComputable fun z =>
      ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop (NUPPT.inArg z).length := by
    convert (polyTimeComputable_pairDropPoly .var).comp
      (NUPPT.polyTimeComputable_inArg.pairEncode hu) using 1
    funext z
    simp
  have hw := NUPPT.polyTimeComputable_inArg.append hud
  -- the call to `D` and its verdict
  have hg := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hw
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice) hc)
  have hgb : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hg.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  -- the bit `u_{|y|}` and the sign
  have hui := StateLoop.headBit_poly.comp hud
  have hflip : PolyTimeComputable fun z => [(pairSndD (NUPPT.inAdvice z)).headD false] :=
    StateLoop.headBit_poly.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice)
  have hsel : PolyTimeComputable fun z => [if decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true]) then
        (((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false
      else !(((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false] := by
    convert polyTimeComputable_ite hgb hui (StateLoop.not_poly hui) using 1
    funext z
    split_ifs <;> rfl
  have hF := StateLoop.xor_poly hsel hflip
  -- the advice `⟨D.advice n, [flip n]⟩`
  have hadv : ∀ n, (pairEncode (D.advice n) [flip n]).length ≤
      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) (.const 1)).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, List.length_singleton]
    have := D.advice_length n
    omega
  let A := NUPPT.ofPolyTime hF (.add ℓ D.coins) _ (fun n => pairEncode (D.advice n) [flip n]) hadv
  have hlen : ∀ n, A.coinLen n = ℓ.eval n + D.coinLen n := fun n => rfl
  let e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n := fun n =>
    (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (hlen n).symm) (Equiv.refl Bool))
  refine ⟨A, e, fun n i t u c => ?_⟩
  have hofn : List.ofFn (e n (u, c)) = List.ofFn u ++ List.ofFn c := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (hlen n).symm (Fin.append u c)).symm
  simp only [NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_eq, hofn, nextBitPred]
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.advInput, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.runAtL, List.take_left', List.drop_left', ofFn_completePrefix]
  split_ifs <;> cases u i <;> cases flip n <;> rfl

/-- **Completeness of the next-bit test** [PS10, Theorem 75.4]: if the ensemble `{X_n}` over
`{0,1}^{ℓ(n)}` passes the next-bit test, then it is pseudorandom.

**Repair (run-3 audit P2-2):** the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` was dropped
(it is the field `Ensemble.nonempty`; with an empty seed type the experiment has probability
`0`, the ensemble passes the next-bit test vacuously, and the always-accepting distinguisher
has advantage `1`); the frozen shape of DESIGN.md §2.12 is restored.

**Repair (gate 03c, finding 2; ruling G3-7b):** the hypothesis `hℓ : ∀ n, 0 < ℓ.eval n`, which
the text does not have, was dropped; the theorem now applies to every ensemble, `ℓ(0) = 0`
included (e.g. `ℓ = n`, `2n`, `n²`).

**Proof sketch.** By contradiction, as in the text. Fix a distinguisher `D` with
`¬ Negligible (fun n => prgAdv (X_n) (D.distinguisher n (ℓ n)))`
(`Ensemble.pseudorandom_iff_prgAdv`); by `not_negligible_iff_exists_polyExpr` there is a
positive syntactic polynomial `p` with `1/p(n) ≤ prgAdv` for infinitely many `n`. At every
`n` with `ℓ(n) > 0`, `exists_nextBitPred` (with the instance `X.nonempty n`) gives a position
`i_n < ℓ(n)` and a sign `flip_n` with
`1/2 + prgAdv/ℓ(n) ≤ nextBitProb (X_n) i_n (nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n)`;
where `ℓ(n) = 0` put `flip_n := false` (`choose` on "a sign, and a position if `ℓ(n) > 0`").
The predictor machine `A` is `exists_nextBitPredMachine ℓ D flip` (advice
`⟨D.advice n, [flip_n]⟩`, coins `ℓ + D.coins`; on `⟨1^n, t⟩` with coins `u ++ c` it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `xor (if g then u_{|t|} else !u_{|t|}) flip_n`, the
position being read off the prefix length). Its functional identity, at every position `i`,
`A.predictor n i t (e (u, c)) = nextBitPred (D.distinguisher n (ℓ n)) i flip_n t (u, c)`
along the coin split `e : (Fin (ℓ n) → Bool) × D.Coins n ≃ A.Coins n` (`Fin.appendEquiv`)
gives `nextBitProb (X_n) i (A.predictor n i) = nextBitProb (X_n) i (nextBitPred …)`
(`uprob_comp_equiv`). Now `h A` gives a negligible `ε` with `nextBitProb … ≤ 1/2 + ε n` for
all `n, i`. At every `n` of the infinite set, `ℓ(n) > 0`, since at `ℓ(n) = 0` the advantage is
`0 < 1/p(n)` (`prgAdv_eq_zero_of_length_eq_zero`); there
`1/(p(n)(ℓ(n) + 1)) ≤ 1/(p(n) ℓ(n)) ≤ prgAdv/ℓ(n) ≤ ε n`, i.e. `¬ Negligible ε` by
`not_negligible_iff_exists_polyExpr` with the positive polynomial `mul p (ℓ + 1)`, a
contradiction. -/
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (h : X.NextBitUnpredictable) : X.Pseudorandom := by
  rw [Ensemble.pseudorandom_iff_prgAdv]
  intro D
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  -- a sign at every `n`, and a position where `ℓ(n) > 0` (the concrete reduction)
  have hex : ∀ n, ∃ flip : Bool, 0 < ℓ.eval n → ∃ i : Fin (ℓ.eval n),
      1 / 2 + prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n) ≤
        nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i flip) := by
    intro n
    by_cases hn : 0 < ℓ.eval n
    · obtain ⟨i, flip, hif⟩ := exists_nextBitPred hn (X.X n) (D.distinguisher n (ℓ.eval n))
      exact ⟨flip, fun _ => ⟨i, hif⟩⟩
    · exact ⟨false, fun hn' => absurd hn' hn⟩
  choose flip hif using hex
  -- the predictor machine, and its identity with the concrete predictor at every position
  obtain ⟨A, e, hA⟩ := exists_nextBitPredMachine ℓ D flip
  obtain ⟨ε, hε, hbound⟩ := h A
  have hprob : ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) =
      nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n)) := by
    intro n i
    unfold nextBitProb
    rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (X.σ n)) (e n))]
    apply OneWay.uprob_congr
    rintro ⟨s, u, c⟩
    simp [hA]
  -- `ε` is not negligible, with the positive polynomial `p · (ℓ + 1)`
  refine (not_negligible_iff_exists_polyExpr.mpr
    ⟨.mul p (.add ℓ (.const 1)), fun n => ?_, fun n₀ => ?_⟩) hε
  · simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
    exact Nat.mul_pos (hp n) (Nat.succ_pos _)
  · obtain ⟨n, hn, hpn⟩ := hinf n₀
    refine ⟨n, hn, ?_⟩
    have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    have h0 : 0 ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    rw [abs_of_nonneg h0] at hpn
    -- on the infinite set `ℓ(n) > 0`: at `ℓ(n) = 0` the advantage is `0`
    have hℓn : 0 < ℓ.eval n := by
      rcases Nat.eq_zero_or_pos (ℓ.eval n) with hz | hz
      · have hzero := prgAdv_eq_zero_of_length_eq_zero hz (X.X n) (D.distinguisher n (ℓ.eval n))
        have := one_div_pos.mpr hppos
        linarith
      · exact hz
    obtain ⟨i, h1⟩ := hif n hℓn
    have h2 := hbound n i
    rw [hprob n i] at h2
    have hℓpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast hℓn
    have hstep : (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ) ≤
        (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := by
      rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, div_div]
      push_cast
      exact one_div_le_one_div_of_le (mul_pos hppos hℓpos)
        (mul_le_mul_of_nonneg_left (by linarith) hppos.le)
    calc (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ)
        ≤ (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := hstep
      _ ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n : ℝ) := by gcongr
      _ ≤ ε n := by linarith
      _ ≤ |ε n| := le_abs_self _

/-! ### Soundness of the next-bit test (the implicit converse) -/

/-- **A uniform string has an unpredictable next bit**: for every predictor `A` and every
position `i`, `nextBitProb id i A = 1/2` exactly, the bit `t_i` of a uniform `t` being
independent of the prefix and of `A`'s coins [PS10, §3.2.2, the intuition behind the test].

**Proof sketch.** Negating bit `i` of `t` (`Function.update t i (!t i)`) is an involution of
the sample space that fixes the prefix and exchanges the success event with its complement,
so `Pr[success] = Pr[failure] = 1 − Pr[success]` (`uprob_comp_equiv`, `uprob_not`). -/
theorem nextBitProb_id {ρ : Type*} [Fintype ρ] [Nonempty ρ] {ℓ : ℕ} (i : Fin ℓ)
    (A : (Fin i → Bool) → ρ → Bool) :
    nextBitProb (id : (Fin ℓ → Bool) → Fin ℓ → Bool) i A = 1 / 2 := by
  let e : (Fin ℓ → Bool) × ρ ≃ (Fin ℓ → Bool) × ρ :=
    { toFun := fun z => (Function.update z.1 i (!z.1 i), z.2)
      invFun := fun z => (Function.update z.1 i (!z.1 i), z.2)
      left_inv := fun z => by
        ext j
        · simp [Function.update_apply]
          split_ifs with hj
          · subst hj; rfl
          · rfl
        · rfl
      right_inv := fun z => by
        ext j
        · simp [Function.update_apply]
          split_ifs with hj
          · subst hj; rfl
          · rfl
        · rfl }
  have hprefix : ∀ (t : Fin ℓ → Bool) (j : Fin i),
      Function.update t i (!t i) (Fin.castLE i.isLt.le j) = t (Fin.castLE i.isLt.le j) := by
    intro t j
    rw [Function.update_of_ne]
    intro hj
    have := congrArg Fin.val hj
    simp at this
    omega
  have hflip : uprob (fun z : (Fin ℓ → Bool) × ρ =>
      A (fun j => id z.1 (Fin.castLE i.isLt.le j)) z.2 = id z.1 i) =
      uprob (fun z : (Fin ℓ → Bool) × ρ =>
        ¬ (A (fun j => id z.1 (Fin.castLE i.isLt.le j)) z.2 = id z.1 i)) := by
    rw [← uprob_comp_equiv e]
    apply OneWay.uprob_congr
    intro z
    simp only [e, Equiv.coe_fn_mk, id, hprefix, Function.update_self]
    cases A (fun j => z.1 (Fin.castLE i.isLt.le j)) z.2 <;> cases z.1 i <;> simp
  unfold nextBitProb
  rw [uprob_not] at hflip
  linarith

/-- **The uniform ensemble passes the next-bit test** (non-vacuity of
[PS10, Definition 75.2]): every predictor succeeds with probability exactly `1/2`, so
`ε := 0` works. -/
theorem Ensemble.uniform_nextBitUnpredictable (ℓ : PolyExpr) :
    (Ensemble.uniform ℓ).NextBitUnpredictable := by
  intro A
  refine ⟨fun _ => 0, negligible_zero, fun n i => ?_⟩
  rw [show (Ensemble.uniform ℓ).X n = id from rfl, nextBitProb_id]
  simp

/-- The distinguisher built from a next-bit predictor `A` at position `i`: accept the string
`t` iff `A(t_1 ⋯ t_i) = t_{i+1}` — the "statistical test" a next-bit predictor induces
[PS10, p. 74, "a pseudorandom distribution needs to pass all efficiently computable
statistical tests"]. -/
def nextBitDist {ρ : Type*} {ℓ : ℕ} (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    (Fin ℓ → Bool) → ρ → Bool :=
  fun t c => decide (A (prefixOf i t) c = t i)

/-- `nextBitDist i A` accepts a sample of `X` exactly when `A` predicts its next bit. -/
theorem acceptProb_nextBitDist {σ ρ : Type*} [Fintype σ] [Fintype ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    acceptProb X (nextBitDist i A) = nextBitProb X i A := by
  unfold acceptProb nextBitProb nextBitDist prefixOf
  apply OneWay.uprob_congr
  intro z
  simp

/-- **Soundness of the next-bit test, concrete form**: the distinguisher induced by a next-bit
predictor `A` at position `i` has PRG advantage exactly `|Pr[A predicts bit i of X] − 1/2|`
(it accepts a uniform string with probability exactly `1/2` by `nextBitProb_id`). Hence a
pseudorandom sampler has no predictor with noticeable next-bit advantage. -/
theorem prgAdv_nextBitDist {σ ρ : Type*} [Fintype σ] [Fintype ρ] [Nonempty ρ] {ℓ : ℕ}
    (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) :
    prgAdv X (nextBitDist i A) = |nextBitProb X i A - 1 / 2| := by
  unfold prgAdv distAdv
  rw [acceptProb_nextBitDist, acceptProb_nextBitDist, nextBitProb_id]

/-- **The next-bit statistical test as a machine**: for a predictor machine `A` and positions
`k n ≤ ℓ(n)`, a non-uniform PPT `Dm` with `A`'s coins and advice `⟨A.advice n, 1^{k n}⟩` which
on `⟨1^n, y⟩` runs `A(1^n, y.take (k n); r)`, reads bit `k n` of `y` and accepts iff the
verdict equals the bit — the untyped form of `nextBitDist (k n) (A.predictor n (k n))`.

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨A.advice n, 1^{k n}⟩⟩, r⟩` cuts
`y` at the unary length of the advice's second component (`polyTimeComputable_pairTakePoly`/
`pairDropPoly var` on `⟨1^{k n}, y⟩`), runs `A.output` on `layout 1^n (y.take (k n)) (A.advice n) r`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), reads the bit as the head of
`y.drop (k n)` (`StateLoop.headBit_poly`) and compares twice with `polyTimeComputable_pairEq`
(verdict against `[true]`, then against the bit). `Dm := ofPolyTime` of it with `A.coins` and
advice bound `2·A.adv + 2 + ℓ` (`length_pairEncode`, `hk`); the identity is
`runAtL_ofPolyTime` plus the projection identities of the layout. -/
private theorem exists_nextBitDistMachine {ℓ : PolyExpr} (A : NUPPT) (k : ℕ → ℕ)
    (hk : ∀ n, k n ≤ ℓ.eval n) :
    ∃ Dm : NUPPT, Dm.coins = A.coins ∧ ∀ n (y r : List Bool),
      Dm.runAtL n y r = [decide ([decide (A.runAtL n (y.take (k n)) r = [true])] =
        [(y.drop (k n)).headD false])] := by
  have hkk := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice
  have hpair := hkk.pairEncode NUPPT.polyTimeComputable_inArg
  have hy₁ : PolyTimeComputable fun z =>
      (NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp hpair using 1
    funext z
    simp
  have hb : PolyTimeComputable fun z =>
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false] := by
    convert StateLoop.headBit_poly.comp ((polyTimeComputable_pairDropPoly .var).comp hpair)
      using 1
    funext z
    simp
  have ha := A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hy₁
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice)
    NUPPT.polyTimeComputable_inCoins)
  have hx : PolyTimeComputable fun z => [decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] := by
    convert polyTimeComputable_pairEq.comp (ha.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  have hG : PolyTimeComputable fun z => [decide ([decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] =
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false])] := by
    convert polyTimeComputable_pairEq.comp (hx.pairEncode hb) using 1
    funext z
    simp
  have hadv : ∀ n, (pairEncode (A.advice n) (List.replicate (k n) true)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) ℓ).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have := A.advice_length n
    have := hk n
    omega
  refine ⟨NUPPT.ofPolyTime hG A.coins _
    (fun n => pairEncode (A.advice n) (List.replicate (k n) true)) hadv, rfl, fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.advInput, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.runAtL]

/-- **Soundness of the next-bit test, asymptotic form** (the converse of
[PS10, Theorem 75.4], implicit in the text's "a pseudorandom distribution needs to pass all
efficiently computable statistical tests", p. 74): a pseudorandom ensemble passes the
next-bit test.

**Proof sketch.** Fix a predictor machine `A` and let
`ε n := max_{i < ℓ n} (nextBitProb (X_n) i (A.predictor n i) − 1/2)` (`0` if `ℓ n = 0`),
attained at some `i_n` (`Finset.exists_max_image`); then `nextBitProb ≤ 1/2 + ε n` for all
`n, i`, and it suffices to show `Negligible ε`. Otherwise `not_negligible_iff_exists_polyExpr`
gives a positive `p` with `1/p(n) ≤ |ε n|` infinitely often. The distinguisher machine `D` is
`exists_nextBitDistMachine A k` with `k n := i_n` (`0` if `ε n` is not attained): advice
`⟨A.advice n, 1^{k n}⟩`, coins `A.coins`; on `⟨1^n, t⟩` it runs `A` on `⟨1^n, t.take (k n)⟩`,
reads bit `k n` of `t` and outputs `[decide (verdict = [bit])]`. At every `n` with `ε n ≠ 0`
(every `n` of the infinite set), `ε n` is attained at `i_n = k n`, and the functional identity
`D.distinguisher n (ℓ n) t (e r) = nextBitDist i_n (A.predictor n i_n) t r` (`ofFn_prefixOf`,
`headD_drop_ofFn`, coins reindexed by `e : A.Coins n ≃ D.Coins n` from `finCongr`) gives, by
`prgAdv_nextBitDist` and `acceptProb_coins_equiv`,
`prgAdv (X_n) (D.distinguisher n (ℓ n)) = |nextBitProb (X_n) i_n (A.predictor n i_n) − 1/2| =
|ε n| ≥ 1/p(n)` — the advantage being an absolute value, no choice between the predictor and
its negation is needed — contradicting `hX D` through `not_negligible_iff_exists_polyExpr`. -/
theorem Ensemble.Pseudorandom.nextBitUnpredictable {ℓ : PolyExpr} {X : Ensemble ℓ}
    (hX : X.Pseudorandom) : X.NextBitUnpredictable := by
  classical
  intro A
  have hmax : ∀ n, ∃ v : ℝ,
      (∀ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 ≤ v) ∧
      (v = 0 ∨ ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = v) := by
    intro n
    rcases isEmpty_or_nonempty (Fin (ℓ.eval n)) with hemp | hne
    · exact ⟨0, fun j => (hemp.false j).elim, Or.inl rfl⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (ℓ.eval n)))
        (fun j => nextBitProb (X.X n) j (A.predictor n j) - 1 / 2) Finset.univ_nonempty
      exact ⟨_, fun j => hj₀ j (Finset.mem_univ j), Or.inr ⟨j₀, rfl⟩⟩
  choose ε hεle hεeq using hmax
  refine ⟨ε, ?_, fun n j => by linarith [hεle n j]⟩
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  let k : ℕ → ℕ := fun n =>
    if h : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n then
      (h.choose : ℕ) else 0
  have hk : ∀ n, k n ≤ ℓ.eval n := by
    intro n
    simp only [k]
    split_ifs with h
    · exact h.choose.isLt.le
    · exact Nat.zero_le _
  obtain ⟨Dm, hc, hDm⟩ := exists_nextBitDistMachine A k hk
  have hlen : ∀ n, A.coinLen n = Dm.coinLen n := fun n => by simp only [NUPPT.coinLen, hc]
  let e : ∀ n, A.Coins n ≃ Dm.Coins n := fun n =>
    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
  have hofn : ∀ n (r : A.Coins n), List.ofFn (e n r) = List.ofFn r := fun n r =>
    (List.ofFn_congr (hlen n) r).symm
  refine (not_negligible_iff_exists_polyExpr.mpr ⟨p, hp, fun n₀ => ?_⟩)
    ((Ensemble.pseudorandom_iff_prgAdv X).mp hX Dm)
  obtain ⟨n, hn, hpn⟩ := hinf n₀
  refine ⟨n, hn, ?_⟩
  have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
  have hε0 : ε n ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hpn
    have := one_div_pos.mpr hppos
    linarith
  have hex : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n :=
    (hεeq n).resolve_left hε0
  obtain ⟨j₀, hkn, hspec⟩ : ∃ j₀ : Fin (ℓ.eval n), k n = j₀ ∧
      nextBitProb (X.X n) j₀ (A.predictor n j₀) - 1 / 2 = ε n :=
    ⟨hex.choose, by simp only [k, dif_pos hex], hex.choose_spec⟩
  have hid : ∀ (t : Fin (ℓ.eval n) → Bool) (r : A.Coins n),
      Dm.distinguisher n (ℓ.eval n) t (e n r) = nextBitDist j₀ (A.predictor n j₀) t r := by
    intro t r
    simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hofn, hDm, hkn, nextBitDist, NUPPT.predictor,
      headD_drop_ofFn, ofFn_prefixOf]
    simp
  have hadv : prgAdv (X.X n) (Dm.distinguisher n (ℓ.eval n)) = |ε n| := by
    rw [← hspec, ← prgAdv_nextBitDist (X.X n) j₀ (A.predictor n j₀)]
    unfold prgAdv distAdv
    rw [acceptProb_coins_equiv (X.X n) (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid,
      acceptProb_coins_equiv id (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid]
  rw [hadv, abs_of_nonneg (abs_nonneg _)]
  exact hpn

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCore.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.NextBit
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.Asymptotic.HardCoreGL
import TCSlib.Cryptography.Asymptotic.HardCoreCollection
import TCSlib.Cryptography.Asymptotic.HardCoreGLFamily
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin
import TCSlib.Cryptography.HardcoreBit.ThreeQuarters
import TCSlib.Cryptography.OneWayFunctions.OutputLength

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core predicates, generators from one-way permutations, Goldreich–Levin

The material of [PS10, §3.3.3–§3.3.5 and §3.4.2–§3.4.3]: hard-core predicates
[PS10, Definition 78.3]; the one-bit-stretch generator `G(s) = f(s) ‖ h(s)` from a one-way
permutation `f` with hard-core predicate `h` [PS10, Theorem 79.4]; the expansion of a
one-bit-stretch generator to `ℓ(n)` bits [PS10, Lemma 80.5]; the iterated generator
`h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` [PS10, Corollary 81.7]; and the Goldreich–Levin theorem:
for every one-way function `f`, `g(x, r) = (f(x), r)` is one-way and `⟨x, r⟩` is hard-core for
`g` [PS10, Theorem 87.3], together with the concrete claims of its proof (the oversimplified
case, the `3/4 + ε` case, the good set, Fact 88.4, Algorithms 88.5 and 89.6, the
pairwise-independence and union-bound claims, the final bound; in
`Asymptotic/HardCoreClaims.lean`) and the version for collections of (trapdoor) permutations
needed by [PS10, Theorem 104.4] (in `Asymptotic/HardCoreCollection.lean`, which this file
imports).

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer is
the frozen Garg development reused verbatim: `owpPredictor`/`exists_owpPredictor`
(`Pseudorandom/GeneratorFromPermutation.lean`), `prgExt`/`prgExtRed`/`exists_prgExtRed_ge`
(`Pseudorandom/Generators.lean`), `HardcoreBit.glPad`, `glBit`, `guessInverter`,
`invProb_guessInverter` (`HardcoreBit/*`); this file adds the bit-string re-encodings the
text's conventions require (`owpPredictorSnoc`, `oneBitStep`, `expandRed`, `prgAdv_fst`) and
the typed-family bridges (`FunFamily.predProb_glPad`, `FunFamily.invProb_glInverter`). The
*asymptotic* layer states the theorems over `Complexity.NUPPT` and `FunFamily`/`PRG`/
`Collection`; every asymptotic theorem is (i) the concrete reduction at each `n`, (ii) a
machine built by the closure calculus of `TCSlib/Complexity/Randomized/`, (iii)
negligible-function arithmetic.

**Deviation:** [PS10, Theorem 87.3] says `⟨x, r⟩` is hard-core "for `f`"; it is hard-core for
`g(x, r) = (f(x), r)` (source error 26 of the plan), which is what is stated.

**Deviation:** [PS10, Definition 78.3] mixes `k` and `n` (`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`,
`∀ k`); the formal statement takes `k = n` (source error 30), on the typed domains of D5, with
the predictor's verdict the string `[true]`.

**Deviation:** [PS10, Theorem 79.4] is proved by the direct reduction of [Gar26, Theorem 3.2]
(one call of the distinguisher on `f(s) ‖ σ` for a random bit `σ`, exact bound `1/2 + ε`)
rather than through the next-bit test (Theorem 75.4), which would lose a factor `1/ℓ`.

**Deviation:** [PS10, Lemma 80.5]: the generator `G'` outputs the bits only (the final seed is
dropped, as in the text); `G(X_i)` is read seed-first/bit-last as in the text (the concrete
`prgExt` reads bit-first; `oneBitStep` is the fixed re-encoding); the expansion clause
`ℓ(n) > n` at every `n` is an explicit hypothesis, see `PRG` (the text's "for any polynomial
`ℓ`": stretches with `ℓ(0) = 0` or `ℓ(1) = 1` are excluded; gate 03c, finding 1, ruling G3-2).
[PS10, Corollary 81.7] lists `ℓ(n) + 1` bits `i = 0, …, ℓ(n)` (source error 38) and needs
`n ≤ ℓ(n)`.

The collection form of [PS10, Theorem 87.3] and its Deviation (the encoding-length hypothesis
`henc` of `Collection.glPad`) are in `Asymptotic/HardCoreCollection.lean` (moved out of this
file for size; gate 03c, finding 11).

**Remarks (not formalized; [PS10, §3.3.2], inventory Constr-77.a, Claim-78.a, Claim-78.b).**
Shamir's generator `G(s) = f^n(s) ‖ ⋯ ‖ f(s) ‖ s` (Constr-77.a) motivates the construction
and is not formalized. Claim-78.a (for a permutation `f` and a uniform `x`, `f^k(x)` is
uniform) is an instance of `uprob_comp_equiv` (the uniform distribution is invariant under a
bijection) applied to the `k`-th iterate of the permutation; it is not stated separately.
Claim-78.b (unpredictable blocks need not have unpredictable bits: a one-way permutation may
leave input bits unchanged) has the concrete witness of [Gar26, Claim 2.3] in
`HardcoreBit/NoFixedBit.lean`: `g(x, y) = f(x_{-y}) ‖ x_y ‖ y` reveals the bits of `y` with
certainty (`predProb_positionBit`) and each fixed input bit `x_i` with advantage
`1/(2(n + 1))` (`predProb_fixedBitPredictor`).

## Main definitions

* `TCSlib.Cryptography.HardCore` — hard-core predicate for a function family
  [PS10, Definition 78.3] (frozen signature).
* `TCSlib.Cryptography.PRG.oneBit`, `TCSlib.Cryptography.owpGenPRG` — the one-bit-stretch
  generator `f(s) ‖ h(s)` [PS10, Theorem 79.4]; `TCSlib.Cryptography.owpPredictorSnoc` — its
  predictor.
* `TCSlib.Cryptography.oneBitStep`, `TCSlib.Cryptography.PRG.expand`,
  `TCSlib.Cryptography.expandRed` — the expansion `G'` of [PS10, Lemma 80.5] and its reduction.
* `TCSlib.Cryptography.PermFamily.iterPRG` — `h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))`
  [PS10, Corollary 81.7].
* `TCSlib.Cryptography.FunFamily.glPad`, `FunFamily.glBit`, `FunFamily.glInverter` — the
  Goldreich–Levin setting `g(x, r) = (f(x), r)`, `h(x, r) = ⟨x, r⟩` [PS10, Theorem 87.3].
* `TCSlib.Cryptography.Collection.glPad`, `Collection.glBit`, `PermCollection.glPad`,
  `TrapdoorCollection.glPad` — the collection form (in `Asymptotic/HardCoreCollection.lean`).

## Main results

* `TCSlib.Cryptography.owp_hardcore_prg` [PS10, Theorem 79.4];
  `TCSlib.Cryptography.exists_owpPredictorSnoc` (concrete, proved).
* `TCSlib.Cryptography.prg_expand` [PS10, Lemma 80.5]; `TCSlib.Cryptography.exists_expandRed_ge`
  (concrete, proved).
* `TCSlib.Cryptography.cor_81_7` [PS10, Corollary 81.7] (proved from the two above and the
  closed form `PermFamily.iterPRG_eq_expand`).
* `TCSlib.Cryptography.goldreich_levin`, `FunFamily.StrongOneWay.glPad`,
  `FunFamily.StrongOneWay.glPad_hardCore` [PS10, Theorem 87.3]; the concrete claims
  `thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`, `fact_88_4`, `thm_87_3_6`, `thm_87_3_7`,
  `thm_87_3_8`, `thm_87_3_9` (proved, instances of `HardcoreBit/*`; they live in the
  sibling file `Asymptotic/HardCoreClaims.lean`, and the machine infrastructure of the fills
  in `Asymptotic/HardCoreLemmas.lean`). The "(OWP)" clause in
  `PermFamily` form (the shape consumed by Theorems 79.4, 81.7, 126.4; `glPad` has input
  length `var + var` and is never a `PermFamily`) is `OneWayPermutation.glHalf` in
  `Asymptotic/HardCorePermutation.lean` (run-3 audit P4-1).
* `TCSlib.Cryptography.goldreich_levin_coll`, `Collection.OneWay.glPad`,
  `Collection.OneWay.glPad_hardCore`, `PermCollection.OneWay.glPad`,
  `TrapdoorCollection.OneWay.glPad` [PS10, Theorem 87.3, collection form] (in
  `Asymptotic/HardCoreCollection.lean`).
* `TCSlib.Cryptography.not_hardCore_const` — a constant predicate is never hard-core
  (non-vacuity of the hardness clause of Definition 78.3).
* `TCSlib.Cryptography.hardCore_iff`, `PRG.oneBit_stretch`, `PRG.oneBit_G`,
  `owpPredictorSnoc_eq`, `oneBitStep_eq`, `expandRed_eq` — the unfoldings of the definitions
  of this file (gate 03c, finding 11).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.3: Definition 78.3; §3.3.4: Theorem 79.4; §3.3.5: Lemma 80.5, Corollary 81.7;
  §3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithms 88.5, 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figures 2.3–2.5), §3.3 (Theorems 3.1, 3.2).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Hard-core predicates [PS10, Definition 78.3] -/

/-- `h` is a **hard-core predicate** for the family `f` [PS10, Definition 78.3]: `h n x` is
computable in deterministic polynomial time from `⟨1^n, x⟩`, and for every non-uniform PPT
`A` there is a negligible `ε` with `Pr[x ← {0,1}^{inLen n} : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)`
for all `n` (the experiment is the concrete `predProb` of [Gar26, Definition 2.3]).

**Deviation:** the text mixes `k` and `n` (`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`, `∀ k`); here
`k = n` (source error 30); `h` is a typed family on `{0,1}^{inLen n}` (D5); the efficiency
clause is a deterministic evaluator on `⟨1^n, x⟩` (as `FunFamily.Easy`, Deviation 3); the
predictor's verdict is the string `[true]` (Deviation 4). -/
def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=
  (∃ H : List Bool → List Bool, PolyTimeComputable H ∧
    ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n

/-- **Hard-core unfolded** [PS10, Definition 78.3]: `h` is hard-core for `f` iff some
polynomial-time `H` computes `[h n x]` from `⟨1^n, x⟩`, and for every non-uniform PPT `A` some
negligible `ε` bounds `Pr[x ← {0,1}^{inLen n} : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)` for all `n`. -/
theorem hardCore_iff (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) :
    HardCore 𝓕 h ↔
      (∃ H : List Bool → List Bool, PolyTimeComputable H ∧
        ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
      ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n :=
  Iff.rfl

/-- The efficiency clause of a hard-core predicate [PS10, Definition 78.3 (1)]. -/
theorem HardCore.easy {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
    (hh : HardCore 𝓕 h) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x] := hh.1

/-- The unpredictability clause of a hard-core predicate [PS10, Definition 78.3 (2)]. -/
theorem HardCore.hard {𝓕 : FunFamily} {h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool}
    (hh : HardCore 𝓕 h) (A : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1 / 2 + ε n := hh.2 A

/-- **A constant predicate is never hard-core** (non-vacuity of the hardness clause of
[PS10, Definition 78.3]): the machine that ignores its input and outputs `[b]` predicts
`h ≡ b` with probability one at every `n`, and `1 ≤ 1/2 + ε(n)` contradicts negligibility.

**Proof sketch.** Take `A := ofPolyTimeUniform (const [b])`; `A.predictor n m y r = b` for
all `y, r` (`NUPPT.output_ofPolyTime`), so `predProb = 1` (`uprob_eq_one_of_forall`); then
`1/2 ≤ ε n` for every `n`, while `|ε n| < 1/n` for large `n`. -/
theorem not_hardCore_const (𝓕 : FunFamily) (b : Bool) : ¬ HardCore 𝓕 (fun _ _ => b) := by
  rintro ⟨-, hA⟩
  obtain ⟨ε, hε, h⟩ := hA (NUPPT.ofPolyTimeUniform (polyTimeComputable_const [b]) (.const 0))
  have hone : ∀ n, predProb (𝓕.f n) (fun _ => b)
      ((NUPPT.ofPolyTimeUniform (polyTimeComputable_const [b]) (.const 0)).predictor n
        (𝓕.outLen.eval n)) = 1 := by
    intro n
    haveI : Nonempty ((Fin (𝓕.inLen.eval n) → Bool) ×
      (NUPPT.ofPolyTimeUniform (polyTimeComputable_const [b]) (.const 0)).Coins n) :=
      ⟨(fun _ => false, fun _ => false)⟩
    refine HardcoreBit.uprob_eq_one_of_forall fun z => ?_
    simp only [NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt, NUPPT.ofPolyTimeUniform,
      NUPPT.output_ofPolyTime]
    cases b <;> simp
  obtain ⟨n₀, hn₀⟩ := hε 1
  have h1 := h (max n₀ 2)
  rw [hone] at h1
  have h2 := hn₀ (max n₀ 2) (le_max_left _ _)
  have h3 : (2 : ℝ) ≤ max n₀ 2 := by exact_mod_cast le_max_right n₀ 2
  have h4 : 1 / ((max n₀ 2 : ℕ) : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]
    exact one_div_le_one_div_of_le (by norm_num) h3
  linarith [le_abs_self (ε (max n₀ 2))]

/-! ## The generator `f(s) ‖ h(s)` [PS10, Theorem 79.4] -/

/-- A one-bit-stretch generator `G n : {0,1}^n → {0,1}^{n+1}` as a `PRG` with stretch
`n + 1` ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG", [PS10, Lemma 80.5]). -/
def PRG.oneBit (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) : PRG where
  stretch := .add .var (.const 1)
  G := G
  expands n := Nat.lt_succ_self n

/-- Field equation: the stretch of `PRG.oneBit G` is `n + 1`. -/
theorem PRG.oneBit_stretch (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (PRG.oneBit G).stretch = .add .var (.const 1) := rfl

/-- Field equation: the generator of `PRG.oneBit G` at seed length `n` is `G n`. -/
theorem PRG.oneBit_G (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (PRG.oneBit G).G n s = G n s := rfl

/-- The generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4] for a permutation family `f`
and a predicate `h`: output length `n + 1`, the bit `h(s)` in the last position. -/
def owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : PRG :=
  PRG.oneBit fun n s => Fin.snoc (P.f n s) (h n s)

/-- Unfolding: the generator of Theorem 79.4 outputs `f(s)` on the first `n` positions. -/
theorem owpGenPRG_G_castSucc (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) (i : Fin n) : (owpGenPRG P h).G n s i.castSucc = P.f n s i := by
  simp [owpGenPRG, PRG.oneBit]

/-- Unfolding: the generator of Theorem 79.4 outputs `h(s)` in the last position. -/
theorem owpGenPRG_G_last (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (s : Fin n → Bool) : (owpGenPRG P h).G n s (Fin.last n) = h n s := by
  simp [owpGenPRG, PRG.oneBit]

/-- The predictor of [Gar26, proof of Theorem 3.2] for a distinguisher of `f(s) ‖ h(s)`: on
input `y = f(s)` it draws a bit `σ` and coins for `D`, outputs `σ` if `D(y ‖ σ) = 1` and
`¬σ` otherwise, negated when `flip`. One call to `D`, one extra coin. -/
def owpPredictorSnoc {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool) (flip : Bool) :
    (Fin n → Bool) → Bool × ρ → Bool :=
  fun y c => owpPredictor (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r)
    flip (y, ()) c

/-- Unfolding: `owpPredictorSnoc D flip` is the concrete `owpPredictor` [Gar26, proof of
Theorem 3.2] for the distinguisher `(y, (), σ) ↦ D(y ‖ σ)`, at the point `(y, ())`. -/
theorem owpPredictorSnoc_eq {ρ : Type*} {n : ℕ} (D : (Fin (n + 1) → Bool) → ρ → Bool)
    (flip : Bool) (y : Fin n → Bool) (c : Bool × ρ) :
    owpPredictorSnoc D flip y c = owpPredictor
      (fun z : (Fin n → Bool) × Unit × Bool => fun r => D (Fin.snoc z.1 z.2.2) r) flip (y, ()) c :=
  rfl

/-- **PRG from a one-way permutation, concrete form** [PS10, Theorem 79.4; Gar26, Theorem 3.2]:
if `D` distinguishes `f(s) ‖ B(s)` from a uniform `(n+1)`-bit string with advantage `ε`, then
for one sign `flip` the predictor `owpPredictorSnoc D flip` predicts `B(s)` from `f(s)` with
probability exactly `1/2 + ε`. Only bijectivity of `f` is used.

**Proof sketch.** Instance of `exists_owpPredictor` with the trivial second component
`β := Unit` and the bit `B'(s, ()) = B(s)`: `owpPair f ≃ f` and `owpGen f B' ≃ f(s) ‖ B(s)`
under the bijections `(s, ()) ↦ s` (seeds, `acceptProb_fst`) and
`(y, (), b) ↦ y ‖ b` (outputs, `prgAdv_comp_equiv`); the prediction experiments correspond
under `(s, c) ↦ ((s, ()), c)` (`uprob_eq_of_equiv`). -/
theorem exists_owpPredictorSnoc {ρ : Type*} [Fintype ρ] [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (B : (Fin n → Bool) → Bool)
    (D : (Fin (n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb f B (owpPredictorSnoc D flip) =
      1 / 2 + prgAdv (fun s => Fin.snoc (f s) (B s)) D := by
  let e : (Fin n → Bool) × Unit × Bool ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun z => Fin.snoc z.1 z.2.2
      invFun := fun t => (Fin.init t, (), t (Fin.last n))
      left_inv := fun z => by
        obtain ⟨a, -, b⟩ := z
        simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun t => by simp [Fin.snoc_init_self] }
  obtain ⟨flip, hflip⟩ := exists_owpPredictor (β := Unit) f (fun w => B w.1)
    (fun z r => D (e z) r)
  refine ⟨flip, ?_⟩
  have h1 : predProb f B (owpPredictorSnoc D flip) =
      predProb (owpPair f) (fun w : (Fin n → Bool) × Unit => B w.1)
        (owpPredictor (fun z r => D (e z) r) flip) := by
    unfold predProb
    exact uprob_eq_of_equiv
      ({ toFun := fun z : (Fin n → Bool) × (Bool × ρ) => ((z.1, ()), z.2)
         invFun := fun z => (z.1.1, z.2)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (Fin n → Bool) × (Bool × ρ) ≃ ((Fin n → Bool) × Unit) × (Bool × ρ))
      fun _ => Iff.rfl
  have h2 : prgAdv (fun s => Fin.snoc (f s) (B s)) D =
      prgAdv (owpGen f fun w : (Fin n → Bool) × Unit => B w.1) (fun z r => D (e z) r) := by
    rw [← prgAdv_comp_equiv e]
    unfold prgAdv distAdv
    rw [← acceptProb_fst (τ := Unit) (fun s => Fin.snoc (f s) (B s)) D]
    rfl
  rw [h1, h2, hflip]

/-- **PRG from a one-way permutation** [PS10, Theorem 79.4]: if `f` is a one-way permutation
and `h` is a hard-core predicate for `f`, then `G(s) = f(s) ‖ h(s)` is a pseudorandom
generator.

**Deviation:** proved by the direct reduction of [Gar26, Theorem 3.2] (one call of `D` on
`f(s) ‖ σ` for a random bit `σ`, exact bound `1/2 + ε`) rather than through the next-bit
test as in the text (which loses a factor `1/(n+1)`); the text's proof writes "predicts
the `i`th bit with probability `1/p(n)`" for "advantage" and "`b` is hard-core" for `h`.

**Proof sketch.** *Easy:* from `hP.easy = ⟨F, hF, hFx⟩` and `hh.easy = ⟨H, hH, hHx⟩` the
evaluator `s ↦ F ⟨1^{|s|}, s⟩ ++ H ⟨1^{|s|}, s⟩` is polynomial-time
(`polyTimeComputable_unary`, `PolyTimeComputable.pairEncode`, `.comp`, `.append`) and
computes `List.ofFn (Fin.snoc (f s) (h s)) = List.ofFn (f s) ++ [h s]` (`List.ofFn_succ'`,
`Fin.snoc_castSucc`, `Fin.snoc_last`). *Pseudorandom:* fix `D : NUPPT`. At every `n`,
`exists_owpPredictorSnoc (P.f n) (h n) (D.distinguisher n (n+1))` gives a sign `flip_n`
(chosen by `Classical.choose`). The predictor machine `A`: advice `⟨[flip_n], D.advice n⟩`
(`NUPPT.exists_withAdvice`, length `≤ D.adv + 6`), coins `1 + D.coins`
(`NUPPT.exists_split (const 1)`: the first coin `σ` is passed as data), on `⟨1^n, y⟩` it forms
`y ++ [σ]` (`PolyTimeComputable.append`), calls `D` once on `⟨1^n, y ++ [σ]⟩` with the remaining
coins (`NUPPT.exists_seq`) and outputs `[xor (if D accepts then σ else !σ) flip_n]`
(`polyTimeComputable_ite`, `polyTimeComputable_pairEq`, `NUPPT.exists_comp`). Functional
identity: `A.predictor n n y r = owpPredictorSnoc (D.distinguisher n (n+1)) flip_n y (c r)`
with `c : A.Coins n ≃ Bool × D.Coins n` the coin split (`Fin.consEquiv`), so
`predProb (P.f n) (h n) (A.predictor n n) = 1/2 + prgAdv ((owpGenPRG P h).G n) (D.distinguisher n (n+1))`
(`uprob_comp_equiv`). Then `hh.hard A` gives a negligible `ε` with the left side `≤ 1/2 + ε n`,
so `0 ≤ prgAdv ≤ ε n` for all `n` and `Negligible.mono` closes `PRG.secure_iff`. -/
theorem owp_hardcore_prg (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) : (owpGenPRG P h).Secure := by
  obtain ⟨F, hF, hFx⟩ := hP.easy
  obtain ⟨H, hH, hHx⟩ := hh.easy
  refine ⟨exists_owpGenEvaluator P h hF hH hFx hHx, fun D => ?_⟩
  have hflip : ∀ n, ∃ flip : Bool,
      predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) flip) =
        1 / 2 + prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) :=
    fun n => exists_owpPredictorSnoc (P.f n) (h n) _
  choose flip hflip using hflip
  obtain ⟨ε, hε, hbound⟩ := hh.hard (owpPredMachine D flip)
  refine hε.mono ⟨0, fun n _ => ?_⟩
  have h1 : predProb (P.f n) (h n) ((owpPredMachine D flip).predictor n n) ≤ 1 / 2 + ε n :=
    hbound n
  rw [owpPredMachine_predProb] at h1
  have h2 := hflip n
  have h3 : predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) (flip n)) =
      predProb (P.f n) (h n) (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := rfl
  rw [← h3, h2] at h1
  show |prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1))| ≤ |ε n|
  have h4 : 0 ≤ prgAdv (fun s => Fin.snoc (P.f n s) (h n s)) (D.distinguisher n (n + 1)) :=
    abs_nonneg _
  rw [abs_of_nonneg h4]
  exact le_trans (by linarith) (le_abs_self _)

/-! ## Expansion of a one-bit-stretch generator [PS10, Lemma 80.5] -/

/-- A one-bit-stretch generator read in the text's order `X_{i+1} ‖ b_{i+1} ← G(X_i)`
[PS10, Lemma 80.5]: the output bit is the last bit of `G(s)` and the next seed is its first
`n` bits (`(Fin.snocEquiv _).symm (G s)`); this is the `S → Bool × S` form of
[Gar26, Construction 3.1], which reads the bit first. -/
def oneBitStep {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (Fin n → Bool) → Bool × (Fin n → Bool) :=
  fun s => (G s (Fin.last n), Fin.init (G s))

/-- Unfolding: one step outputs the last bit of `G(s)` and the next seed `init G(s)`. -/
theorem oneBitStep_eq {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (s : Fin n → Bool) :
    oneBitStep G s = (G s (Fin.last n), Fin.init (G s)) := rfl

/-- The **expanded generator** `G'(s) = b_1 ⋯ b_{ℓ(n)}` of [PS10, Lemma 80.5]: `X_0 = s`,
`X_{i+1} ‖ b_{i+1} ← G(X_i)`, output the `ℓ(n)` bits (the final seed is dropped). Formally
the first component of the concrete `prgExt (oneBitStep (G n)) (ℓ n)` [Gar26,
Construction 3.1]; the expansion clause `n < ℓ(n)`, at every `n` (see `PRG`), is the
hypothesis `hℓ`.

**Deviation:** `G(X_i)` is read seed-first/bit-last as in the text; the output drops the
final seed (as in the text), the concrete `prgExt` keeps it. The text's "for any polynomial
`ℓ`" is restricted to `ℓ(n) > n` at every `n`, `n = 0` included (the cost of `PRG.expands`:
`2n` and `n^c` are excluded, `2n + 1` and `n^c + 1` are not; gate 03c, finding 1, ruling
G3-2). -/
def PRG.expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) : PRG where
  stretch := ℓ
  G n s := (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1
  expands := hℓ

/-- Closed form of the expansion: output bit `i` is the last bit of `G(X_i)`, where
`X_i` is the `i`-th iterate of `s ↦ init (G s)` on the seed (`b_{i+1}` in the text's
1-indexed notation). -/
theorem PRG.expand_G (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (n : ℕ) (s : Fin n → Bool) (i : Fin (ℓ.eval n)) :
    (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := rfl

/-- The hybrid-`k` reduction of [PS10, Lemma 80.5] (the machine `M(y)` of the proof) in the
text's seed-first convention: on `T ∈ {0,1}^{n+1}` read `(b, X) := (T_{n+1}, T_1 ⋯ T_n)`, draw
`k` uniform bits `b_prev`, put `b` at position `k`, iterate `G` on `X` for the remaining
positions and call `D` once on the `ℓ` bits. Cost: that of `prgExtRed` (`l − k − 1` calls to
`G`, one to `D`, `l` coins of which `k` are used). -/
def expandRed {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (l k : ℕ)
    (D : (Fin l → Bool) → ρ → Bool) : (Fin (n + 1) → Bool) → (Fin l → Bool) × ρ → Bool :=
  fun T c => prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c

/-- Unfolding: `expandRed G l k D` on `T` is the concrete hybrid-`k` reduction `prgExtRed`
[Gar26, Theorem 3.1] of `oneBitStep G` against `D ∘ fst`, on the re-encoded input
`(T_{n+1}, T_1 ⋯ T_n)`. -/
theorem expandRed_eq {ρ : Type*} {n : ℕ} (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) (l k : ℕ)
    (D : (Fin l → Bool) → ρ → Bool) (T : Fin (n + 1) → Bool) (c : (Fin l → Bool) × ρ) :
    expandRed G l k D T c =
      prgExtRed (oneBitStep G) l k (fun z r => D z.1 r) (T (Fin.last n), Fin.init T) c := rfl

/-- Dropping an independent uniform component from a generator's output does not change
PRG advantages: `prgAdv (fst ∘ X) D = prgAdv X (D ∘ fst)` (the projection is a deterministic
post-processing and the projection of a uniform pair is uniform). -/
theorem prgAdv_fst {σ γ δ ρ : Type*} [Fintype σ] [Fintype γ] [Fintype δ] [Nonempty δ]
    [Fintype ρ] (X : σ → γ × δ) (D : γ → ρ → Bool) :
    prgAdv (fun s => (X s).1) D = prgAdv X (fun z r => D z.1 r) := by
  unfold prgAdv distAdv
  rw [← acceptProb_fst (τ := δ) (id : γ → γ) D]
  rfl

/-- **Expansion, concrete form** [PS10, Lemma 80.5; Gar26, Theorem 3.1]: if `D` distinguishes
the `l`-bit expansion of `G` (`l ≥ 1`, bits only) from a uniform `l`-bit string with advantage
`ε`, then for some hybrid index `k < l` the reduction `expandRed G l k D` distinguishes
`G` from a uniform `(n+1)`-bit string with advantage at least `ε / l`.

**Proof sketch.** `prgAdv_fst` moves the projection onto the distinguisher;
`exists_prgExtRed_ge` for `oneBitStep G` gives `k`; `prgAdv_comp_equiv` with the bijection
`(Fin.snocEquiv _).symm : {0,1}^{n+1} ≃ Bool × {0,1}^n` re-encodes the reduction's input. -/
theorem exists_expandRed_ge {ρ : Type*} [Fintype ρ] {n : ℕ}
    (G : (Fin n → Bool) → (Fin (n + 1) → Bool)) {l : ℕ} (hl : 0 < l)
    (D : (Fin l → Bool) → ρ → Bool) :
    ∃ k < l, prgAdv (fun s => (prgExt (oneBitStep G) l s).1) D / l ≤
      prgAdv G (expandRed G l k D) := by
  obtain ⟨k, hk, h⟩ := exists_prgExtRed_ge (oneBitStep G) hl (fun z r => D z.1 r)
  refine ⟨k, hk, ?_⟩
  rw [prgAdv_fst]
  refine h.trans_eq ?_
  exact prgAdv_comp_equiv (Fin.snocEquiv fun _ => Bool).symm G
    (prgExtRed (oneBitStep G) l k fun z r => D z.1 r)

/-- **Expansion of a PRG** [PS10, Lemma 80.5]: if the one-bit-stretch generator `G` is a PRG
then so is its `ℓ(n)`-bit expansion `G'` (`ℓ(n) > n` at every `n`, see `PRG`).

The input is a one-bit-stretch `G : {0,1}^n → {0,1}^{n+1}`, as in the text ("Let
`G : {0,1}^n → {0,1}^{n+1}` be a PRG"), not a general `P : PRG` (the shape recorded at DESIGN
§2.12); a general secure `P` reaches it through its truncation to `n + 1` bits, `PRG.truncate`
with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` (`Asymptotic/PRF.lean`; gate 03c,
finding 4).

**Deviation:** `G'` drops the final seed and reads `G(X_i)` seed-first, as the text; the
text's proof interchanges `m(n)` and `ℓ(n)`, starts the hybrids at `i = 1` (they must start
at `0`) and reads `M(y)` bit-first against the construction (source error 34). The text's
"for any polynomial `ℓ`" is restricted to `ℓ(n) > n` at every `n`, `n = 0` included (the cost
of `PRG.expands`; gate 03c, finding 1, ruling G3-2); the security half uses only `ℓ(n) > 0`.

**Proof sketch.** *Easy:* from `h.1 = ⟨F, hF, hFs⟩`, `G'` is computed by
`polyTimeComputable_iterateEmit` with step `x ↦ (F x).dropLast` (the next seed,
`Turing.FinTM.computesFunInTime_stripLast`) and emission `x ↦ [(F x).getLast]`, `R := ℓ`,
orbit bound `P := var` (all seeds have length `n`), truncated to the first `ℓ(n)` bits
(`polyTimeComputable_pairTakePoly ℓ` on `⟨1^{|s|}, ·⟩`); the identity with
`PRG.expand_G` is `List.ofFn_succ'`. *Pseudorandom* (`PRG.secure_iff`): fix `D : NUPPT`.
At every `n`, `exists_expandRed_ge (G n) (hl := Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n))`
with `D.distinguisher n (ℓ n)` gives a hybrid index `k_n < ℓ(n)`. The reduction machine
`M`: advice `⟨⟨1^{k_n}, 1^{ℓ(n) − k_n − 1}⟩, D.advice n⟩` (`NUPPT.exists_withAdvice`,
length `≤ 2ℓ + D.adv + 8`), coins `ℓ + D.coins` (`NUPPT.exists_split ℓ`), on `⟨1^n, T⟩` it
takes the first `k_n` coins as `b_prev` (`pairTakePoly`), the last bit of `T` as `b` and its
first `n` bits as `X` (`stripLast`, `pairDropPoly`), iterates `F` `ℓ(n) − k_n − 1` times
emitting the last bits (`polyTimeComputable_iterateEmit` with the unary advice as fuel),
concatenates `b_prev ++ [b] ++ b_next` and calls `D` once (`NUPPT.exists_seq`). Functional
identity: `M.distinguisher n (n+1) T r = expandRed (G n) (ℓ n) k_n (D.distinguisher n (ℓ n)) T (c r)`
with `c : M.Coins n ≃ (Fin (ℓ n) → Bool) × D.Coins n` (`Fin.appendEquiv`), hence
`prgAdv (G n) (M.distinguisher n (n+1)) ≥ prgAdv ((PRG.expand G ℓ hℓ).G n) (D.distinguisher n (ℓ n)) / ℓ(n)`
(`uprob_comp_equiv`). By `h.2 M` the left side is negligible; `ℓ(n) ≤ C (n+1)^c`
(`PolyExpr.eval_le`), so the right side is negligible by `Negligible.mul_pow`,
`Negligible.const_mul` and `Negligible.mono`. -/
theorem prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure := by
  rw [PRG.secure_iff] at h ⊢
  obtain ⟨⟨F, hF, hFs⟩, hsec⟩ := h
  have hFs' : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s) := hFs
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := exists_expandEvaluator G hFs' hF ℓ
    exact ⟨E, hE, fun n s => by rw [hEs]; rfl⟩
  · have hk : ∀ n, ∃ k < ℓ.eval n,
        prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1) (D.distinguisher n (ℓ.eval n)) /
          ℓ.eval n ≤
        prgAdv (G n) (expandRed (G n) (ℓ.eval n) k (D.distinguisher n (ℓ.eval n))) :=
      fun n => exists_expandRed_ge (G n) (Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)) _
    choose k hk hle using hk
    have hneg : Negligible fun n =>
        prgAdv (G n) ((expandRedMachine D hF ℓ k hk).distinguisher n (n + 1)) :=
      hsec (expandRedMachine D hF ℓ k hk)
    have hred : ∀ n, prgAdv (G n) ((expandRedMachine D hF ℓ k hk).distinguisher n (n + 1)) =
        prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n))) := by
      intro n
      refine prgAdv_coins_equiv _ _ _ (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)) fun T c => ?_
      obtain ⟨a, c⟩ := c
      exact expandRedMachine_distinguisher G hFs' D hF ℓ k hk n T a c _ (ofFn_appendEquiv a c)
    simp only [hred] at hneg
    refine (hneg.polyExpr_mul ℓ).mono ⟨0, fun n _ => ?_⟩
    have hpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le n) (hℓ n)
    have h1 := hle n
    rw [div_le_iff₀ hpos] at h1
    show |prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1) (D.distinguisher n (ℓ.eval n))| ≤
      |(ℓ.eval n : ℝ) * prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n)))|
    have h2 : 0 ≤ prgAdv (fun s => (prgExt (oneBitStep (G n)) (ℓ.eval n) s).1)
        (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    have h3 : 0 ≤ prgAdv (G n) (expandRed (G n) (ℓ.eval n) (k n) (D.distinguisher n (ℓ.eval n))) :=
      abs_nonneg _
    rw [abs_of_nonneg h2, abs_of_nonneg (mul_nonneg hpos.le h3)]
    linarith

/-! ## The iterated generator [PS10, Corollary 81.7] -/

/-- The generator `G(x) = h(x) ‖ h(f(x)) ‖ h(f^{(2)}(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` of
[PS10, Corollary 81.7]: output bit `i` (`0 ≤ i ≤ ℓ(n)`) is `h(f^{(i)}(x))`; output length
`ℓ(n) + 1`, expanding when `n ≤ ℓ(n)`.

**Deviation:** the text's formula lists `ℓ(n) + 1` bits where Lemma 80.5 produces `ℓ(n)`
(source error 38); the stretch is `ℓ + 1` and the expansion hypothesis is `n ≤ ℓ(n)`. -/
def PermFamily.iterPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) : PRG where
  stretch := .add ℓ (.const 1)
  G n s := fun i => h n ((⇑(P.f n))^[i] s)
  expands n := Nat.lt_succ_of_le (hℓ n)

/-- **The closed form of Corollary 81.7**: the iterated generator is the `(ℓ(n) + 1)`-bit
expansion (Lemma 80.5) of the one-bit generator `f(s) ‖ h(s)` (Theorem 79.4), since the seed
update of `oneBitStep (f(s) ‖ h(s))` is `f` (`Fin.init_snoc`) and its output bit is `h`
(`Fin.snoc_last`). -/
theorem PermFamily.iterPRG_eq_expand (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (ℓ : PolyExpr) (hℓ : ∀ n, n ≤ ℓ.eval n) :
    P.iterPRG h ℓ hℓ = PRG.expand (fun n s => Fin.snoc (P.f n s) (h n s)) (.add ℓ (.const 1))
      (fun n => Nat.lt_succ_of_le (hℓ n)) := by
  unfold PermFamily.iterPRG PRG.expand
  congr 1
  funext n s i
  have hstep : prgStep (oneBitStep fun x => Fin.snoc (P.f n x) (h n x)) = ⇑(P.f n) :=
    funext fun x => by
      show Fin.init (Fin.snoc (P.f n x) (h n x) : Fin (n + 1) → Bool) = P.f n x
      exact Fin.init_snoc _ _
  simp only [prgExt]
  rw [hstep]
  simp only [oneBitStep, Fin.snoc_last]

/-- **The iterated generator is a PRG** [PS10, Corollary 81.7]: for a one-way permutation `f`
with hard-core predicate `h`, `G(x) = h(x) ‖ h(f(x)) ‖ ⋯ ‖ h(f^{ℓ(n)}(x))` is a PRG, by
Theorem 79.4 (`owp_hardcore_prg`) and Lemma 80.5 (`prg_expand`) through the closed form
`PermFamily.iterPRG_eq_expand`. -/
theorem cor_81_7 (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (ℓ : PolyExpr)
    (hℓ : ∀ n, n ≤ ℓ.eval n) (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) :
    (P.iterPRG h ℓ hℓ).Secure := by
  rw [PermFamily.iterPRG_eq_expand]
  exact prg_expand _ _ _ (owp_hardcore_prg P h hP hh)

/-! ## Goldreich–Levin for function families [PS10, Theorem 87.3] -/

namespace FunFamily

variable (𝓕 : FunFamily)

/-- The function `g(x, r) = (f(x), r)` of [PS10, Theorem 87.3] (`|x| = |r| = inLen n`) as a
family: input length `2·inLen`, output length `outLen + inLen`, the string `x ‖ r` split by
`Fin.appendEquiv` and `g` the concrete `HardcoreBit.glPad (f n)` [Gar26, Theorem 2.3]. -/
def glPad : FunFamily where
  inLen := .add 𝓕.inLen 𝓕.inLen
  outLen := .add 𝓕.outLen 𝓕.inLen
  f n z := Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
    (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z))

/-- The predicate `h(x, r) = ⟨x, r⟩` of [PS10, Theorem 87.3] on the string `x ‖ r`
(the concrete `HardcoreBit.glBit`, Fact 88.4's inner product). -/
def glBit : ∀ n, (Fin (𝓕.glPad.inLen.eval n) → Bool) → Bool :=
  fun n z => HardcoreBit.glBit ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)

/-- The inverter of `g` built from a recovery procedure `R` for `x` from `f(x)`: on
`f(x) ‖ r` with coins `c` it outputs `R(f(x), c) ‖ r` (the concrete `HardcoreBit.glInverter`;
all inverters of [PS10, §3.4.3] have this shape). -/
def glInverter {γ : Type*} (n : ℕ) (R : (Fin (𝓕.outLen.eval n) → Bool) → γ → Fin (𝓕.inLen.eval n) → Bool) :
    (Fin (𝓕.glPad.outLen.eval n) → Bool) → γ → (Fin (𝓕.glPad.inLen.eval n) → Bool) :=
  fun y c => Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)
    (HardcoreBit.glInverter R ((Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).symm y) c)

/-- Unfolding: `g` on `x ‖ r` is `f(x) ‖ r`. -/
theorem glPad_f (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glPad.f n (Fin.append x r) = Fin.append (𝓕.f n x) r := by
  show Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n)
    ((Fin.appendEquiv _ _).symm (Fin.appendEquiv _ _ (x, r)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Unfolding: `h(x ‖ r) = ⟨x, r⟩`. -/
theorem glBit_append (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glBit n (Fin.append x r) = HardcoreBit.ip x r := by
  show HardcoreBit.glBit ((Fin.appendEquiv _ _).symm (Fin.appendEquiv _ _ (x, r))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- **Bridge to the concrete setting (prediction)**: the prediction probability of `A` for
`h = ⟨x, r⟩` of the family `g` equals that of `A ∘ (append)` for `glBit` of the concrete
`HardcoreBit.glPad (f n)` [Gar26, Theorem 2.3]. -/
theorem predProb_glPad {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) :
    predProb (𝓕.glPad.f n) (𝓕.glBit n) A =
      predProb (HardcoreBit.glPad (𝓕.f n)) HardcoreBit.glBit
        (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) := by
  unfold predProb
  exact uprob_eq_of_equiv (splitPair (𝓕.inLen.eval n) (𝓕.inLen.eval n) ρ) fun _ => Iff.rfl

/-- **Bridge to the concrete setting (inversion)**: the inversion probability of the family
inverter `glInverter n R` against the family `g` equals that of the concrete
`HardcoreBit.glInverter R` against `HardcoreBit.glPad (f n)`. -/
theorem invProb_glInverter {γ : Type*} [Fintype γ] (n : ℕ)
    (R : (Fin (𝓕.outLen.eval n) → Bool) → γ → Fin (𝓕.inLen.eval n) → Bool) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n R) =
      invProb (HardcoreBit.glPad (𝓕.f n)) (HardcoreBit.glInverter R) := by
  unfold invProb
  refine uprob_eq_of_equiv (splitPair (𝓕.inLen.eval n) (𝓕.inLen.eval n) γ) fun z => ?_
  simp only [glPad, glInverter, splitPair, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  exact Equiv.apply_eq_iff_eq _

/-- **`g` is a permutation when `f` is** ([PS10, Theorem 87.3], the "(OWP)" clause): the
family `g(x, r) = (f(x), r)` is bijective at every `n` at which `f` is.

Note (run-3 audit P4-1): bijectivity of a `FunFamily` of input length `var + var` (even
lengths only) does not make `𝓕.glPad` a `PermFamily`; that form is `PermFamily.glHalf` /
`OneWayPermutation.glHalf` (`Asymptotic/HardCorePermutation.lean`, `glHalf_f_even`). -/
theorem glPad_f_bijective (n : ℕ) (hf : Function.Bijective (𝓕.f n)) :
    Function.Bijective (𝓕.glPad.f n) := by
  have e : HardcoreBit.glPad (𝓕.f n) =
      ⇑((Equiv.ofBijective _ hf).prodCongr (Equiv.refl (Fin (𝓕.inLen.eval n) → Bool))) := by
    funext z; rfl
  show Function.Bijective fun z => Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n)
    ((Fin.appendEquiv _ _).symm z))
  rw [e]
  exact (Fin.appendEquiv _ _).bijective.comp
    (((Equiv.ofBijective _ hf).prodCongr _).bijective.comp (Fin.appendEquiv _ _).symm.bijective)

/-- **`g` is one-way** ([PS10, Theorem 87.3], first clause; inventory Thm-87.3.a): if `f` is a
strong one-way function then so is `g(x, r) = (f(x), r)`.

**Proof sketch.** *Easy:* from `h.easy = ⟨F, hF, hFx⟩`, the evaluator on `⟨1^n, x ‖ r⟩` is
`F ⟨1^n, (take (inLen n))⟩ ++ drop (inLen n)` (`polyTimeComputable_pairTakePoly 𝓕.inLen`,
`pairDropPoly`, `PolyTimeComputable.append`; `List.ofFn_fin_append`). *Hard:* for an inverter
`A : NUPPT` of `g`, the inverter `B` of `f`: coins `inLen + A.coins` (`NUPPT.exists_split
𝓕.inLen`: the first `inLen n` coins are the padding `r`), on `⟨1^n, y⟩` it calls `A` once on
`⟨1^n, y ++ r⟩` (`NUPPT.exists_seq`) and outputs the first `inLen n` bits of the answer
(`pairTakePoly 𝓕.inLen`; a wrong-length answer stays wrong). Concretely this is the padding
inverter `OneWay.padInverter` of [Gar26, Lemma 2.3] (`OneWay.pad f = HardcoreBit.glPad f`
definitionally): `𝓕.glPad.invProbAt A n ≤ 𝓕.invProbAt B n` by `invProbAt_eq_uprob`,
`uprob_comp_equiv` on the coin split `splitCoins`, `uprob_mono` (if `A`'s decoded answer
`x' ‖ r'` satisfies `f(x') ‖ r' = f(x) ‖ r` then `f(x') = f(x)`, `Fin.append` injective in
its first argument); then `Negligible.mono` with `h.hard B`. -/
theorem StrongOneWay.glPad {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.glPad.StrongOneWay := by
  obtain ⟨F, hF, hFx⟩ := h.easy
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := exists_glPadEvaluator 𝓕 hF hFx
    refine ⟨E, hE, fun n z => ?_⟩
    obtain ⟨⟨x, r⟩, rfl⟩ := (Fin.appendEquiv _ _).surjective z
    show E (NUPPT.advInput n (List.ofFn (Fin.append x r))) = List.ofFn (𝓕.glPad.f n (Fin.append x r))
    rw [List.ofFn_fin_append, hEs, glPad_f, List.ofFn_fin_append]
  · refine (h.hard (glPadInvMachine A 𝓕.inLen)).mono ⟨0, fun n _ => ?_⟩
    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
    exact invProbOpt_glPad_le 𝓕 A n

/-- **`⟨x, r⟩` is hard-core for `g`** ([PS10, Theorem 87.3], second clause; inventory
Thm-87.3.b): if `f` is a strong one-way function then `h(x, r) = ⟨x, r⟩` is a hard-core
predicate for `g(x, r) = (f(x), r)`.

**Deviation:** the text says hard-core "for `f`" (source error 26); the final constant of the
text is `ε³/(32n)` (with `ε' = ε/2`), the concrete layer's `invProb_guessInverter` gives
`ε/(4·2^k)` with `2n ≤ ε²(2^k − 1)` (source error 37; `[GL89]`).

**Proof sketch.** *Easy:* `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` is the inner-product evaluator `ipFun`
(the selective block XOR `selXorFun` with one-bit blocks, `Asymptotic/HardCoreLoops.lean`) on
the halves cut by `pairTakePoly 𝓕.inLen`/`pairDropPoly 𝓕.inLen` (`exists_glBitEvaluator`).
*Hard:* by contradiction. The hardness function is `ε n := max 0 (predProb − 1/2)`; if it is
not negligible, `not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ predProb (𝓕.glPad.f n)
(𝓕.glBit n) (A.predictor n _)` for infinitely many `n`. Put `ε_n := n^{−c}` and the hard-wired
`k(n) := size (2 m(n) n^{2c})` (`glK`), so that `2m ≤ ε_n²(2^{k(n)} − 1)` (`glK_real`) and
`2^{k(n)} ≤ 4 m(n) n^{2c} + 1` (`two_pow_glK_le`); `predProb_glPad` transfers the hypothesis to
the concrete setting and `HardcoreBit.invProb_guessInverter` gives `ε_n/(4·2^{k(n)}) ≤ invProb
(HardcoreBit.glPad (𝓕.f n)) (guessInverter A' k(n))` [PS10, Algorithm 89.6]. The inverter as
an `NUPPT` is `glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen …`
(`Asymptotic/HardCoreGL.lean`): advice `⟨⟨1^k, ⟨1^{2^k−1}, table⟩⟩, A.advice n⟩` where the
table lists the pairs `⟨e_i, β_L⟩` of all rounds, coins `K m + K + m K A.coins` (the `s_j`,
the `b_j`, one coin block of `A` per round, unread coins), and the voting loop `GLLoop`
(`polyTimeComputable_stateIterate`) that queries `A` on `⟨1^n, y ‖ (S_L ⊕ e_i)⟩` with
`S_L`, `B_L` from `selXorFun`/`ipFun` and takes the `m` majorities by
`polyTimeComputable_blockMap`/`polyTimeComputable_majority`. Its inversion probability is
exactly that of `guessInverter` (`invProbOpt_glFam_eq`, through the coin bijection
`glCoinsEquiv` and `glMachine_runAt_guessRecover`), so `𝓕.glPad.invProbAt B n ≥
n^{−c}/(4(4 m n^{2c} + 1)) ≥ n^{−(c+d+1)}` infinitely often (`PolyExpr.eval_le`),
contradicting `(StrongOneWay.glPad h).hard B`. -/
theorem StrongOneWay.glPad_hardCore {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    HardCore 𝓕.glPad 𝓕.glBit := by
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨H, hH, hHx⟩ := exists_glBitEvaluator 𝓕.inLen
    refine ⟨H, hH, fun n z => ?_⟩
    obtain ⟨⟨x, r⟩, rfl⟩ := (Fin.appendEquiv _ _).surjective z
    show H (NUPPT.advInput n (List.ofFn (Fin.append x r))) = [𝓕.glBit n (Fin.append x r)]
    rw [List.ofFn_fin_append, hHx, glBit_append]
  · refine ⟨fun n => max 0 (predProb (𝓕.glPad.f n) (𝓕.glBit n)
      (A.predictor n (𝓕.glPad.outLen.eval n)) - 1 / 2), ?_, fun n => by
        linarith [le_max_right (0 : ℝ)
          (predProb (𝓕.glPad.f n) (𝓕.glBit n) (A.predictor n (𝓕.glPad.outLen.eval n)) - 1 / 2)]⟩
    by_contra hneg
    obtain ⟨c, hc⟩ := not_negligible_iff.mp hneg
    set K := glKBound 𝓕.inLen c with hK
    set B := glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen K (glK 𝓕.inLen c)
      (two_pow_glK_le 𝓕.inLen c) with hB
    have hBneg := (h.glPad).hard B
    obtain ⟨C, d, hCd⟩ := K.eval_le
    obtain ⟨n₀, hn₀⟩ := hBneg (c + d + 1)
    obtain ⟨n, hn, hgap⟩ := hc (max n₀ (max 1 (4 * C * 2 ^ d)))
    have hn1 : 1 ≤ n := le_of_max_le_left (le_of_max_le_right hn)
    have hnC : 4 * C * 2 ^ d ≤ n := le_of_max_le_right (le_of_max_le_right hn)
    have hε : (0 : ℝ) < 1 / (n : ℝ) ^ c := by positivity
    have hpred : 1 / 2 + 1 / (n : ℝ) ^ c ≤
        predProb (𝓕.glPad.f n) (𝓕.glBit n) (A.predictor n (𝓕.glPad.outLen.eval n)) := by
      rw [abs_of_nonneg (le_max_left _ _)] at hgap
      rcases le_or_gt (predProb (𝓕.glPad.f n) (𝓕.glBit n)
        (A.predictor n (𝓕.glPad.outLen.eval n)) - 1 / 2) 0 with hle | hlt
      · rw [max_eq_left hle] at hgap; linarith
      · rw [max_eq_right hlt.le] at hgap; linarith
    rw [predProb_glPad] at hpred
    have hGL := HardcoreBit.invProb_guessInverter (𝓕.f n)
      (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
        (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c)
      hε (glK_real 𝓕.inLen c n hn1) hpred
    have hid : 𝓕.glPad.invProbAt B n = invProb (HardcoreBit.glPad (𝓕.f n))
        (HardcoreBit.guessInverter (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) (glK 𝓕.inLen c n)) :=
      invProbOpt_glFam_eq 𝓕 A K (glK 𝓕.inLen c) (two_pow_glK_le 𝓕.inLen c) n
        (glK_pos_or 𝓕.inLen c n hn1)
    have hsmall := hn₀ n (le_of_max_le_left hn)
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), hid] at hsmall
    have h2k : ((2 : ℝ) ^ glK 𝓕.inLen c n) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ d := by
      exact_mod_cast (two_pow_glK_le 𝓕.inLen c n).trans (hCd n)
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnCR : (4 : ℝ) * C * 2 ^ d ≤ n := by exact_mod_cast hnC
    have hpow : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hlow : 1 / (n : ℝ) ^ (c + d + 1) ≤ 1 / (n : ℝ) ^ c / (4 * 2 ^ glK 𝓕.inLen c n) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      calc (n : ℝ) ^ c * (4 * 2 ^ glK 𝓕.inLen c n)
          ≤ (n : ℝ) ^ c * (4 * (C * (2 * (n : ℝ)) ^ d)) := by
            gcongr
            exact h2k.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
        _ = (n : ℝ) ^ c * (n : ℝ) ^ d * (4 * C * 2 ^ d) := by ring
        _ ≤ (n : ℝ) ^ c * (n : ℝ) ^ d * n := by gcongr
        _ = (n : ℝ) ^ (c + d + 1) := by ring
    linarith

end FunFamily

/-- **Goldreich–Levin** [PS10, Theorem 87.3; GL89]: if `f` is a strong one-way function then
`g(x, r) = (f(x), r)` is a strong one-way function and `h(x, r) = ⟨x, r⟩` is a hard-core
predicate for `g` (bijectivity of `g` at each `n` is `FunFamily.glPad_f_bijective`).

**Deviation:** hard-core for `g`, not "for `f`" (source error 26).

Repair (run-3 audit P4-1): statement unchanged. The text's "(OWP)" reading — "the existence
of OWPs implies the existence of OWPs with a hard-core bit" (p. 86), i.e. a `PermFamily` with
a `HardCore` predicate feeding `owp_hardcore_prg`, `cor_81_7` and `Commitment.owp_commitment` —
is **not** derivable from this theorem: `𝓕.glPad` has input length `var + var` and is never a
`PermFamily`. That route is `OneWayPermutation.glHalf` (`Asymptotic/HardCorePermutation.lean`):
the balanced permutation `PermFamily.glHalf`, `x ‖ w ↦ f_{⌊n/2⌋}(x) ‖ w`, whose one-wayness and
hard-core bit reduce to `StrongOneWay.glPad` and `StrongOneWay.glPad_hardCore` at parameter
`⌊n/2⌋` through `predProb_glHalf_even`/`predProb_glHalf_odd`, `invProb_glHalf_even`/
`invProb_glHalf_odd_le` and `Negligible.comp_div_two`. -/
theorem goldreich_levin {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    𝓕.glPad.StrongOneWay ∧ HardCore 𝓕.glPad 𝓕.glBit :=
  ⟨h.glPad, h.glPad_hardCore⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCoreClaims.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The concrete claims of the proof of the Goldreich–Levin theorem

The concrete claims of the proof of [PS10, Theorem 87.3] (§3.4.3): the oversimplified case,
the `3/4 + ε` case, the good set, Fact 88.4, the pairwise-independence and union-bound
claims about Algorithm 89.6, and the final bound — each a re-export of the corresponding
concrete lemma of the Garg layer (`TCSlib/Cryptography/HardcoreBit/*`). The claims about
the prediction and inversion experiments of `g` (`thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`,
`thm_87_3_9`) are stated at the family level (`FunFamily.glPad`, `FunFamily.glBit`,
`FunFamily.glInverter` of `TCSlib.Cryptography.Asymptotic.HardCore`), through the bridges
`FunFamily.predProb_glPad` and `FunFamily.invProb_glInverter`; the claims about the inner
product and the samples of Algorithm 89.6 (`fact_88_4`, `thm_87_3_6`, `thm_87_3_7`,
`thm_87_3_8`) do not involve the family and are stated concretely, for an arbitrary
`f : {0,1}^n → β` (gate 03c, finding 7). The declaration names encode the inventory ids
(Thm-87.3.x), not [PS10] numbers. (Moved out of `Asymptotic/HardCore.lean` for size; the
statements are those of the audited statement phase.)

## Main definitions

None.

## Main results

* `TCSlib.Cryptography.fact_88_4` — `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` [PS10, Fact 88.4].
* `TCSlib.Cryptography.thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3` — the oversimplified case, the
  `3/4 + ε` case (Algorithm 88.5) and the good set [PS10, §3.4.3].
* `TCSlib.Cryptography.thm_87_3_6`, `thm_87_3_7`, `thm_87_3_8`, `thm_87_3_9` — pairwise
  independent samples, subset sums, the guessing step and the final bound of
  Algorithm 89.6 [PS10, §3.4.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithms 88.5, 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figures 2.3–2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The concrete claims of the proof of Theorem 87.3 [PS10, §3.4.3]

The setting (inventory Thm-87.3.c) is `FunFamily.glPad`, `FunFamily.glBit`,
`FunFamily.glInverter` over the concrete `HardcoreBit.ip`, `glPad`, `glBit`, `glInverter`,
`secProb` (`Pr_r[A(f(x), r) = ⟨x, r⟩]` for a fixed `x`). Algorithm 88.5 is
`HardcoreBit.majorityInverter` (`majorityRecover`, `trialBit`); Algorithm 89.6 is
`HardcoreBit.guessInverter` (`guessRecover`, the subroutine `C` realised by guessing the
`k = log m` bits `b'_j` and forming subset sums). Each claim below re-exports the
corresponding concrete lemma: at the family level for the claims about `g`, concretely for
`fact_88_4` and `thm_87_3_6/7/8`. -/

/-- **Fact 88.4** [PS10]: `⟨a, b ⊕ c⟩ = ⟨a, b⟩ ⊕ ⟨a, c⟩` (bit strings as a Boolean ring, `+` is
XOR); the concrete `HardcoreBit.ip_add`. -/
theorem fact_88_4 {n : ℕ} (a b c : Fin n → Bool) :
    HardcoreBit.ip a (b + c) = HardcoreBit.ip a b + HardcoreBit.ip a c :=
  HardcoreBit.ip_add a b c

/-- **The oversimplified case** [PS10, §3.4.3; inventory Thm-87.3.1]: if `A` predicts `⟨x, r⟩`
from `g(x, r)` with probability one, the inverter querying `e_1, …, e_n` (the concrete
`perfectRecover`, `⟨x, e_i⟩ = x_i`) inverts `g` with probability one. -/
theorem thm_87_3_1 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool)
    (h : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = 1) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.perfectRecover
      fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r)) = 1 := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  exact HardcoreBit.invProb_perfectInverter _ _ h

/-- **The less simplified case** [PS10, §3.4.3, Algorithm 88.5; inventory Thm-87.3.2]: if `A`
predicts `⟨x, r⟩` with probability `3/4 + ε` and `n ≤ 2ε²T`, the inverter taking the majority
of `T` guesses `A(y, r) ⊕ A(y, r ⊕ e_i)` per bit inverts `g` with probability at least `ε/4`
(the text's Chernoff bound is Chebyshev with pairwise independence). -/
theorem thm_87_3_2 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {T : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hT : (𝓕.inLen.eval n : ℝ) ≤ 2 * ε ^ 2 * T)
    (h : 3 / 4 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / 4 ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.majorityRecover
      (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) T)) := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  exact HardcoreBit.invProb_majorityInverter _ _ hε hT h

/-- **The good set is large** [PS10, §3.4.3; inventory Thm-87.3.3]: if `A` predicts `⟨x, r⟩`
with probability `c + ε` (`c = 3/4` or `1/2`), then `Pr_x[Pr_r[A(f(x), r) = ⟨x, r⟩] ≥ c + ε/2] ≥ ε/2`
(the text's displayed chain `< ε/2 + (1 − ε/2)(c + ε/2) < c + ε`). -/
theorem thm_87_3_3 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (h : c + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / 2 ≤ uprob fun x => c + ε / 2 ≤ HardcoreBit.secProb (𝓕.f n)
      (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) x := by
  rw [FunFamily.predProb_glPad] at h
  exact HardcoreBit.half_le_uprob_good _ _ hc hε h

/-- **Pairwise-independent samples suffice** [PS10, §3.4.3; inventory Thm-87.3.6]: for a good
`x` (`secProb ≥ 1/2 + ε/2`) and `k ≥ 1`, each bit of the ideal recovery procedure (correct
guesses `b_L = ⟨x, S_L⟩`) is wrong with probability at most `1/(ε²(2^k − 1))`, by the
pairwise-independent sampling inequality (`chebyshev_pairwise`); the concrete
`uprob_idealRecover_ne_le`, stated for an arbitrary `f`. The text bounds this probability by
`(1 − 4ε'²)/(4mε'²) ≤ 1/(mε'²)` with `ε' = ε/2`; the formal `1/(ε²(2^k − 1)) = 1/(4mε'²)` lies
between the two, with `m` read as the number `2^k − 1` of samples, one per nonempty `L ⊆ [k]`
(the text draws the `m − 1` samples `r_1, …, r_{m−1}` from `log m` seeds and writes `m`; its
`m` is the `2^k` of `thm_87_3_8`). -/
theorem thm_87_3_6 {n : ℕ} {β ρ : Type*} [Fintype ρ] [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (hk : 0 < k) (x : Fin n → Bool) (i : Fin n)
    {ε : ℝ} (hε : 0 < ε) (hx : 1 / 2 + ε / 2 ≤ HardcoreBit.secProb f A x) :
    uprob (fun ω : (Fin k → Fin n → Bool) × (Fin n → HardcoreBit.NESubset k → ρ) =>
      HardcoreBit.idealRecover f A x ω.1 ω.2 i ≠ x i) ≤ 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) :=
  HardcoreBit.uprob_idealRecover_ne_le f A hk x i hε hx

/-- **Subset sums are pairwise independent and uniform** [PS10, §3.4.3, "show this!";
inventory Thm-87.3.7]: for uniform `s_1, …, s_k ∈ {0,1}^n`, the `2^k − 1` strings
`r_L = ⊕_{j ∈ L} s_j` over nonempty `L ⊆ [k]` are each uniform and pairwise independent
(the concrete `pairwiseUniform_subsetSum`; `card_nonempty_finset` counts them). -/
theorem thm_87_3_7 {n k : ℕ} :
    HardcoreBit.PairwiseUniform fun (L : HardcoreBit.NESubset k) (s : Fin k → Fin n → Bool) =>
      HardcoreBit.subsetSum L.1 s :=
  HardcoreBit.pairwiseUniform_subsetSum

/-- **All guesses are right with probability `1/m = 2^{−k}`, and then every `b_L` is right**
[PS10, §3.4.3; inventory Thm-87.3.8]: the guessed bits `b'_1 ⋯ b'_k` equal `⟨x, s_1⟩ ⋯ ⟨x, s_k⟩`
with probability `1/2^k` (`uprob_guess_eq`), and under that event the recovery procedure
computes `b_L = ⟨x, S_L⟩` for every `L`, i.e. it is the ideal procedure
(`guessRecover_correct_guess`); stated for an arbitrary `f`. Here `m = 2^k` is the text's `m`
(`log m` guessed bits), while `thm_87_3_6` counts the `2^k − 1` samples. -/
theorem thm_87_3_8 {n : ℕ} {β ρ : Type*} [Fintype ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (x : Fin n → Bool) (s : Fin k → Fin n → Bool)
    (cs : Fin n → HardcoreBit.NESubset k → ρ) :
    uprob (fun b : Fin k → Bool => b = fun j => HardcoreBit.ip x (s j)) = 1 / 2 ^ k ∧
      HardcoreBit.guessRecover A k (f x) (s, fun j => HardcoreBit.ip x (s j), cs) =
        HardcoreBit.idealRecover f A x s cs :=
  ⟨HardcoreBit.uprob_guess_eq _, HardcoreBit.guessRecover_correct_guess f A x s cs⟩

/-- **The final bound of the general case** [PS10, §3.4.3, Algorithm 89.6; inventory
Thm-87.3.9]: if `A` predicts `⟨x, r⟩` from `g(x, r)` with probability `1/2 + ε` and
`2n ≤ ε²(2^k − 1)`, the inverter of Algorithm 89.6 with `k` guessed bits inverts `g` with
probability at least `ε/(4·2^k)`; with `ε² 2^k ≤ 4n` this is at least `ε³/(16n)`.

**Deviation:** the text's constant is `ε'/(2m) = ε³/(32n)` with `ε' = ε/2`, `m = 2n/ε'²`
(source error 37); the concrete bound is stronger. -/
theorem thm_87_3_9 (𝓕 : FunFamily) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 2 * (𝓕.inLen.eval n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ predProb (𝓕.glPad.f n) (𝓕.glBit n) A) :
    ε / (4 * 2 ^ k) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.guessRecover
      (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) k)) ∧
    (ε ^ 2 * (2 : ℝ) ^ k ≤ 4 * 𝓕.inLen.eval n →
      ε ^ 3 / (16 * 𝓕.inLen.eval n) ≤ invProb (𝓕.glPad.f n) (𝓕.glInverter n
        (HardcoreBit.guessRecover
          (fun y r => A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r) k))) := by
  rw [FunFamily.predProb_glPad] at h
  rw [FunFamily.invProb_glInverter]
  exact ⟨HardcoreBit.invProb_guessInverter _ _ hε hk h,
    fun hk' => HardcoreBit.invProb_guessInverter_cubic _ _ hε hk hk' h⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Goldreich–Levin for collections

The collection form of the Goldreich–Levin theorem [PS10, Theorem 87.3], the one the text uses
for [PS10, Theorem 104.4] and Chapter 4: for a collection `{f_i : D_i → R_i}` of one-way
functions, the padded collection `g_i(x, r) = (f_i(x), r)` is a collection of one-way functions
and `⟨x, r⟩` is hard-core for it; and the same for collections of permutations and of trapdoor
permutations. The machine side is `Asymptotic/HardCoreGLColl.lean` and
`Asymptotic/HardCoreLemmas.lean`. (Moved out of `Asymptotic/HardCore.lean` for size, gate 03c,
finding 11; the declarations, their names and statements are unchanged, and `HardCore.lean`
imports this file, so its importers see them as before.)

**Deviation:** [PS10, Theorem 87.3] for collections (unnumbered): the padded collection
`Collection.glPad F m` pads each element by `|encD_i(default)|` uniform bits; its one-wayness
and hard-core theorems assume length-regular encodings at generated indices
(`∀ n r x, |encD_{index n r} x| = m(n)`), which the text's "`|x| = |r|`" presupposes, at the
cost stated at `Collection.glPad` (no candidate of the library satisfies it as parametrized;
gate 03c, finding 3, ruling G3-7c). Its hard-core proof uses the encoded-domain
Goldreich–Levin lemma `HardcoreBit.invProb_guessInverter_enc_pad`
(`Asymptotic/GoldreichLevinDomain.lean`): the cube lemma does not transfer to a domain `D_i`
whose encoding is a strict subset of the cube (run-3 audit P4-2).

## Main definitions

* `TCSlib.Cryptography.Collection.glPad`, `TCSlib.Cryptography.Collection.glBit` — the padded
  collection `g_i(x, r) = (f_i(x), r)` and the predicate `⟨x, r⟩`.
* `TCSlib.Cryptography.PermCollection.glPad`, `TCSlib.Cryptography.TrapdoorCollection.glPad` —
  the padded collection of (trapdoor) permutations.

## Main results

* `TCSlib.Cryptography.goldreich_levin_coll`, `TCSlib.Cryptography.Collection.OneWay.glPad`,
  `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` [PS10, Theorem 87.3, collection form].
* `TCSlib.Cryptography.PermCollection.OneWay.glPad`,
  `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore`,
  `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad`,
  `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` — the (trapdoor) permutation
  forms, for [PS10, Theorem 104.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5: Definition 41.1; §2.10: Definition 55.1; §2.11: Definition 56.1; §3.4.2–3.4.3:
  Theorem 87.3; §3.10: Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Goldreich–Levin for collections [PS10, Theorem 87.3, collection form] -/

namespace Collection

variable (F : Collection)

/-- The **padded collection** `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] for a
collection `{f_i : D_i → R_i}` whose elements have encoding length `m(n)` at the indices
generated at parameter `n` (`henc`): the domain `D'_i = D_i × {0,1}^{|encD_i(default)|}` (the
padding has the length of the encoded elements), elements encoded as `⟨encD_i x, r⟩`, the
same index generator `Gen`, the sampler `Sample'(1^n, i) = ⟨Sample(1^n, i), r⟩` with `m(n)`
fresh coins `r`, and the evaluator `⟨i, ⟨x, r⟩⟩ ↦ ⟨eval ⟨i, x⟩, r⟩`. The sampler's outputs
decode (`sample_spec`): the first component by `F.sample_spec`, the padding because it has
exactly `m(n) = |encD_i(default)|` bits by `henc`.

Repair (run-3 audit P3-1): the hypothesis `henc` (previously carried by the theorems only) is
now an argument of the definition, since without it the padding of the sampled string need not
have the length the decoder expects and `Collection.sample_spec` would fail.

**Deviation:** the text's "`|x| = |r|`" presupposes that all elements of `D_i` have the same
encoding length; `glPad` assumes `|encD_i x| = m(n)` at generated indices (`henc`). Cost (gate
03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly increasing, so an index
generated at two parameters forces `m` constant, and no candidate of the library satisfies `henc`
as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements; `rabinBlumTrapdoor`: `2·max(n, 3)`;
`expCollection`: `dlDefaultIndex` below `n₀`). A per-index form (`|encD_i x| = |encD_i default|
≤ m(n)`) would admit them; it is not formalized. -/
noncomputable def glPad (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    Collection where
  D i := F.D i × (Fin (F.encD i default).length → Bool)
  encD i z := pairEncode (F.encD i z.1) (List.ofFn z.2)
  decD i w := match pairDecode w with
    | some (a, b) => match F.decD i a, decodeFin (F.encD i default).length b with
      | some x, some r => some (x, r)
      | _, _ => none
    | none => none
  decD_encD i z := by simp [pairDecode_pairEncode, F.decD_encD, decodeFin_ofFn]
  encD_decD i w z h := by
    rcases hw : pairDecode w with _ | ⟨a, b⟩
    · simp [hw] at h
    cases ha : F.decD i a <;> cases hb : decodeFin (F.encD i default).length b <;> simp [hw, ha, hb] at h
    rw [eq_pairEncode_of_pairDecode w a b hw, ← h, F.encD_decD i a _ ha, ofFn_of_decodeFin_eq_some hb]
  f i z := pairEncode (F.f i z.1) (List.ofFn z.2)
  gen := F.gen
  gen_uniform := F.gen_uniform
  sample := NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval w := pairEncode (F.eval (pairEncode (pairFstD w) (pairFstD (pairSndD w))))
    (pairSndD (pairSndD w))
  eval_poly := (F.eval_poly.comp (polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  eval_spec i z := by simp [F.eval_spec]
  sample_spec n r s := by
    obtain ⟨⟨s₁, s₂⟩, hs⟩ := (Fin.appendEquiv (F.sample.coins.eval n) (m.eval n)).surjective s
    have hofn : List.ofFn s = List.ofFn s₁ ++ List.ofFn s₂ := by
      rw [← hs]
      exact List.ofFn_fin_append s₁ s₂
    have hA : (List.ofFn s).take (F.sample.coinLen n) = List.ofFn s₁ := by
      rw [hofn, List.take_left' List.length_ofFn]
    have hB : (List.ofFn s).drop (F.sample.coinLen n) = List.ofFn s₂ := by
      rw [hofn, List.drop_left' List.length_ofFn]
    obtain ⟨x, hx, hev⟩ := F.sample_spec n r s₁
    have hL : (F.encD (pairFstD (F.gen.runAt n [] r)) default).length = m.eval n := henc n r default
    have hs₂ : List.ofFn s₂ = List.ofFn
        fun j : Fin (F.encD (pairFstD (F.gen.runAt n [] r)) default).length => s₂ (Fin.cast hL j) :=
      List.ofFn_congr hL.symm s₂
    refine ⟨(x, fun j => s₂ (Fin.cast hL j)), ?_, ?_⟩
    · simp only [glPadSample_runAt, hA, hB, pairDecode_pairEncode, ← NUPPT.runAt_eq, hx, hs₂,
        decodeFin_ofFn]
    · simp only [glPadSample_runAt, hA, hB, pairFstD_pairEncode, pairSndD_pairEncode,
        ← NUPPT.runAt_eq, hev, hs₂]

/-- The predicate `h_i(x, r) = ⟨x, r⟩` for the padded collection: the inner product of the
encoding of `x` (padded or truncated to the padding length) with `r`. -/
def glBit : ∀ i, F.D i × (Fin (F.encD i default).length → Bool) → Bool :=
  fun i z => HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2

/-- Unfolding: `h_i(x, r)` is the inner product `⟨padFin(encD_i x), r⟩`, the encoding of `x`
padded or truncated to the padding length `|encD_i(default)|`. -/
theorem glBit_eq (i : List Bool) (z : F.D i × (Fin (F.encD i default).length → Bool)) :
    F.glBit i z = HardcoreBit.ip (padFin _ (F.encD i z.1)) z.2 := rfl

variable {F} in
/-- Unfolding: the padded collection keeps the index generator. -/
theorem glPad_gen (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) :
    (F.glPad m henc).gen = F.gen := rfl

variable {F} in
/-- Unfolding: `g_i(x, r) = ⟨f_i(x), r⟩`. -/
theorem glPad_f (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) (z : (F.glPad m henc).D i) :
    (F.glPad m henc).f i z = pairEncode (F.f i z.1) (List.ofFn z.2) := rfl

variable {F} in
/-- Unfolding: the sampler of the padded collection runs `Sample(1^n, i)` on its first
`|Sample's coins|` coins and appends the remaining coins. -/
theorem glPad_sample_runAtL (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (n : ℕ) (i r : List Bool) :
    (F.glPad m henc).sample.runAtL n i r =
      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)) := by
  simp only [glPad, NUPPT.runAtL, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
    NUPPT.coinLen]

variable {F} in
/-- Unfolding: the decoder of the padded collection is `glPadDecode` at the padding length
`|encD_i(default)|` (propositional: the two `match` expressions are compiled separately). -/
theorem glPad_decD_eq (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (i : List Bool) : (F.glPad m henc).decD i = glPadDecode F i (F.encD i default).length := by
  funext w
  unfold Collection.glPad glPadDecode
  dsimp only
  cases pairDecode w with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    dsimp only
    cases F.decD i a <;> cases decodeFin (F.encD i default).length b <;> rfl

/-- **The padded collection is one-way** ([PS10, Theorem 87.3], collection form, first clause):
if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at the
indices generated at parameter `n`, then `F.glPad m` is a collection of one-way functions.

**Proof sketch.** *Sampling:* with `h.sampleClose = ⟨δ, hδ, hS⟩`, at index `i = index n r`
the decoded sampler output is `(decD i (Sample(1^n, i; s₁)), decodeFin _ (ofFn s₂))` on the
coin split `splitCoins (Sample.coins n) (m n)` (`glPad_sample_runAtL`, `List.ofFn` of the
split, `uprob_comp_equiv`); `henc` gives `(encD i default).length = m n`, so the second
component decodes exactly (`decodeFin_ofFn`) and `StatClose.prod (hS n r) (StatClose.refl _)`
with `StatClose.map` to the pair gives `SampleClose δ`. *Hard:* for `A : NUPPT` against
`F.glPad m`, the inverter `B` against `F`: coins `m + A.coins` (`NUPPT.exists_split m`, the
first `m n` coins are `r`), on `⟨1^n, ⟨i, y⟩⟩` it calls `A` once on `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`
(`NUPPT.exists_comp`, `NUPPT.exists_seq`) and returns the first component of the answer
(`pairFstD`). Then `(F.glPad m).invProbAt A n ≤ F.invProbAt B n`: unfold both `uexp` over
`Gen`'s coins (`OneWay.uexp_mono`), split the inner `uprob` over `D_i × ({0,1}^{m n} × A.Coins n)`
against `D_i × B.Coins n` by `uprob_comp_equiv` on `splitCoins`, and `uprob_mono`: a decoded
answer `(x', r')` with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)`
(`pairEncode_injective`). `Negligible.mono` with `h.hard B`. -/
theorem OneWay.glPad {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).OneWay := by
  obtain ⟨δ, hδ, hS⟩ := h.sampleClose
  refine ⟨⟨δ, hδ, fun n r => ?_⟩, fun A => ?_⟩
  · have key := statClose_glPadSampler F m (F.glPad m henc).sample rfl (glPad_sample_runAtL m henc)
      hS n r _ (henc n r default)
    simp only [glPad_decD_eq] at key ⊢
    exact key
  · refine (h.hard (glPadCollInvMachine A m)).mono ⟨0, fun n _ => ?_⟩
    rw [abs_of_nonneg (invProbAt_nonneg _ _ _), abs_of_nonneg (invProbAt_nonneg _ _ _)]
    have key := glPad_invProbAt_le F m A n (fun r => (F.encD (F.index n r) default).length)
      (fun r => henc n r default)
    unfold Collection.invProbAt at key ⊢
    simp only [glPad_decD_eq]
    exact key

/-- **`⟨x, r⟩` is hard-core for the padded collection** ([PS10, Theorem 87.3], collection form,
second clause; inventory Thm-87.3.coll, needed by Theorem 104.4): if `F` is a collection of
one-way functions with encoding length `m(n)` at generated indices, then
`h_i(x, r) = ⟨encD_i x, r⟩` is a hard-core predicate for `F.glPad m` (`Collection.HardCore`).

Repair (run-3 audit P4-2): statement unchanged. The run-2 sketch transferred the cube lemma
`HardcoreBit.invProb_guessInverter` to `D_i` by "identifying `D_i` with `{0,1}^{m n}` through
the injective encoding"; that step is invalid — the image of `encD_i` is in general a strict
subset of the cube (`Z_N^*`, `QR_N`), the uniform `x ∈ D_i` is not a uniform cube element and
the predictor's behaviour off the image is uncontrolled. The transfer is replaced by the
encoded-domain lemma `HardcoreBit.invProb_guessInverter_enc_pad`
(`Asymptotic/GoldreichLevinDomain.lean`), stated for `x` uniform on an arbitrary finite type
with an arbitrary encoding into `{0,1}^m`.

**Proof sketch.** *Easy:* `⟨i, ⟨a, b⟩⟩ ↦ ipFun ⟨padToLen a b, b⟩` — pad `a = encD_i x` to the
length of `b = r` and apply the inner-product evaluator (`exists_glBitCollEvaluator`,
`Asymptotic/HardCoreGLColl.lean`). *Hard:* `glColl_negligible` with the padding length
`L n r = |encD_i(default)| = m(n)` (`henc`) and the one-wayness of the padded collection
(`OneWay.glPad`, its inversion experiment rewritten by `glPad_decD_eq`): by contradiction,
`not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ E_r[Pr[A(1^n, ⟨i, ⟨f_i x, r⟩⟩) = ⟨encD_i x, r⟩]]`
infinitely often; the good indices (`HardcoreBit.half_le_uprob_threshold`) have per-index
success `≥ 1/2 + n^{−c}/2`, where `HardcoreBit.invProb_guessInverter_enc_pad` with
`enc := padFin (m n) ∘ encD_i` and the hard-wired `k(n) = size (8 m(n) n^{2c})` (`glKc`) makes
the recovery procedure of [PS10, Algorithm 89.6] output `encD_i x` with probability
`≥ ε/(4·2^{k(n)})`, `ε = n^{−c}/2`; the inverter `glCollMachine` (the recovery machine `glMachine`
on the pre-processed predictor `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`, output `⟨x', r⟩`) realises it
(`glColl_uprob_le`); averaging over the good indices (`HardcoreBit.uprob_mul_le_uexp`) gives
inversion probability `≥ ε²/(4·2^{k(n)})`, inverse polynomial infinitely often, contradicting
`(OneWay.glPad m henc h).hard`. -/
theorem OneWay.glPad_hardCore {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).HardCore F.glBit := by
  refine ⟨?_, fun A => ?_⟩
  · obtain ⟨H, hH, hHx⟩ := exists_glBitCollEvaluator F
    exact ⟨H, hH, fun i x => hHx i x.1 x.2⟩
  · have hmax : ∀ x : ℝ, x ≤ 1 / 2 + max 0 (x - 1 / 2) := fun x => by
      linarith [le_max_right (0 : ℝ) (x - 1 / 2)]
    refine ⟨_, glColl_negligible F m (fun n r => (F.encD (F.index n r) default).length)
      (fun n r => henc n r default) henc A (fun B => ?_), fun n => hmax _⟩
    have key := (OneWay.glPad m henc h).hard B
    unfold Collection.invProbAt at key
    simp only [glPad_decD_eq] at key
    exact key

end Collection

/-- **Goldreich–Levin for collections** ([PS10, Theorem 87.3], the collection form the text
uses for Theorem 104.4 and Chapter 4): for a collection `F` of one-way functions with
encoding length `m(n)` at generated indices, `g_i(x, r) = (f_i(x), r)` is a collection of
one-way functions and `⟨x, r⟩` is hard-core for it. -/
theorem goldreich_levin_coll {F : Collection} (m : PolyExpr)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n)
    (h : F.OneWay) : (F.glPad m henc).OneWay ∧ (F.glPad m henc).HardCore F.glBit :=
  ⟨Collection.OneWay.glPad m henc h, Collection.OneWay.glPad_hardCore m henc h⟩

/-- The padded collection of a collection of permutations is a collection of permutations
[PS10, Theorem 87.3, "(OWP)"]: `g_i = perm_i × id` on `D_i × {0,1}^{|encD_i default|}`. -/
noncomputable def PermCollection.glPad (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
    PermCollection :=
  { P.toCollection.glPad m henc with
    perm := fun i => (P.perm i).prodCongr (Equiv.refl _)
    f_perm := fun i z => by simp [Collection.glPad, P.f_perm] }

/-- Unfolding: the underlying collection of `P.glPad m henc` is `P.toCollection.glPad m henc`. -/
theorem PermCollection.glPad_toCollection (P : PermCollection) (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) :
    (P.glPad m henc).toCollection = P.toCollection.glPad m henc := rfl

/-- **The padded permutation collection is one-way** when the original is (collection form of
[PS10, Theorem 87.3] for Definition 55.1). -/
theorem PermCollection.OneWay.glPad {P : PermCollection} (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (h : P.OneWay) : (P.glPad m henc).OneWay :=
  Collection.OneWay.glPad m henc h

/-- **`⟨x, r⟩` is hard-core for the padded permutation collection**. -/
theorem PermCollection.OneWay.glPad_hardCore {P : PermCollection} (m : PolyExpr)
    (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
    (h : P.OneWay) : (P.glPad m henc).toCollection.HardCore P.glBit :=
  Collection.OneWay.glPad_hardCore m henc h

/-- The padded collection of a collection of trapdoor permutations is a collection of
trapdoor permutations [PS10, Theorem 87.3 for Definition 56.1, as used in Theorem 104.4]:
`Inv'(1^n, ⟨t, ⟨y, r⟩⟩) = ⟨Inv(1^n, ⟨t, y⟩), r⟩`.

**Proof sketch** (of `inv_spec`). Unfold the activation of the `ofPolyTimeUniform` machine
(`NUPPT.output_ofPolyTime`, the layout projections); `T.inv` is uniform so its activation is
its output on the layout with empty advice; `T.inv_spec` decodes the first component to
`(perm i).symm y.1` and `decodeFin_ofFn` the second to `y.2`. -/
noncomputable def TrapdoorCollection.glPad (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    TrapdoorCollection :=
  { T.toPermCollection.glPad m henc with
    inv := NUPPT.ofPolyTimeUniform (glPadInvFun_poly T) T.inv.coins
    inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
    inv_spec := fun n r y s => by
      have hspec := T.inv_spec n r y.1 s
      simp only [NUPPT.runAt, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime, glPadInvFun,
        NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
        pairFstD_pairEncode, pairSndD_pairEncode, PermCollection.glPad, Collection.glPad,
        pairDecode_pairEncode, decodeFin_ofFn, T.inv_uniform n] at hspec ⊢
      rw [hspec]
      rfl }

/-- Unfolding: the underlying permutation collection of `T.glPad m henc` is
`T.toPermCollection.glPad m henc`. -/
theorem TrapdoorCollection.glPad_toPermCollection (T : TrapdoorCollection) (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) :
    (T.glPad m henc).toPermCollection = T.toPermCollection.glPad m henc := rfl

/-- **The padded trapdoor collection is one-way** when the original is ([PS10, Theorem 87.3]
for Definition 56.1 (5)). -/
theorem TrapdoorCollection.OneWay.glPad {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) : (T.glPad m henc).OneWay :=
  Collection.OneWay.glPad m henc h

/-- **`⟨x, r⟩` is hard-core for the padded trapdoor collection**: the hypothesis "trapdoor
permutations with a hard-core predicate" of [PS10, Theorem 104.4] is satisfiable from trapdoor
permutations whose generated indices encode elements in exactly `m(n)` bits (`henc`; no
candidate of the library satisfies it as parametrized, see `Collection.glPad`). -/
theorem TrapdoorCollection.OneWay.glPad_hardCore {T : TrapdoorCollection} (m : PolyExpr)
    (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n)
    (h : T.OneWay) : (T.glPad m henc).toCollection.HardCore T.glBit :=
  Collection.OneWay.glPad_hardCore m henc h

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03c-pack.md =====

# Gate 03c ([PS10] ch. 2–4, hard-core bits and PRGs): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/c/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers pseudorandom ensembles, next-bit unpredictability, pseudorandom generators and their expansion, and hard-core predicates up to the Goldreich–Levin theorem.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03c-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §3.2–§3.4 (book pp. 74–90).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- a "PRG" whose output length is not larger than its seed at some lengths;
- a predicate that is hard-core only because the function is not efficiently computable;
- a next-bit predictor that uses its advice to hard-wire the seed.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{Pseudorandom, NextBit, HardCore, HardCoreClaims}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03b's files (the machine model, ensembles, one-wayness, collections): earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.12 the frozen definition shapes, §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch3.md`: Claim-67.a, Def-74.1, Def-75.2, Rem-75.3, Thm-75.4 (with .conv, .c, .1, .2), Alg-76.5, Def-77.1, Claim-107.c, Constr-77.a, Claim-78.a, Claim-78.b, Def-78.3 (and .coll), Thm-79.4, Claim-79.a, Lem-80.5, Cor-81.7, Constr-82.a, Thm-87.3 (with .a, .b, .coll) |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the proofs of Goldreich–Levin and of the hard-core lemmas (`HardCoreLemmas`, `HardCoreLoops`, `HardCoreGL*`, `GoldreichLevinDomain`, `HardCorePermutation`), whose statements pack 03i audits |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/c/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 338 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 22 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 22 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 4 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these four files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `PRG`, `PRG.Secure` and `prg_expand`.

## Specific questions

1. **Pseudorandomness (Def 74.1) and PRGs (Def 77.1).**
   - Is `PRG.Secure` indistinguishability of `G(U_n)` from `U_{ℓ(n)}` against every n.u.p.p.t.
     distinguisher, with `ℓ(n) > n`?
   - Are the length conditions stated for every `n`, or only eventually, and does it matter?
2. **Next-bit unpredictability (Def 75.2, Thm 75.4).**
   - Is the predictor's index `i` chosen as the source has it (adaptively, per `n`)?
   - Are both directions of Thm 75.4 stated, and at what loss?
3. **Expansion (Lem 80.5, Cor 81.7, `prg_expand`).** Does `prg_expand` give any polynomial
   stretch from a one-bit-stretch PRG, with the right composition and the right loss?
4. **Hard-core predicates (Def 78.3 and its collection form; Thm 79.4).**
   - Is "hard-core" stated against n.u.p.p.t. predictors with advantage `1/2 + negl`?
   - Does Thm 79.4 (a one-way permutation with a hard-core bit gives a PRG) need the permutation
     property where it uses it?
5. **Goldreich–Levin (Thm 87.3, the collection form).** Is the hard-core bit `⟨x, r⟩` stated for
   `g(x, r) = (f(x), r)` with `|r| = |x|`, for every strong OWF `f`, at the source's strength?
6. **`HardCoreClaims.lean`** has no inventory row. Say what its declarations claim and whether
   each is true and correctly attributed.

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
    (ruling G3-5).

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
    24.6 proper is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
    unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
    question 5, ruled outside the core on 2026-10-27).

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
carries the cost of §5.25);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
   by point tests, not formalized; gate 03a, note 14).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length. The honest
   messages are polynomially bounded in `|x|` (`Protocol.ProverBounded`, in
   `InteractiveProof(Err).complete` and the field `EfficientProverProof(Err).boundedP`): the
   source's p.p.t. prover writes at most `t(|x|)` bits. Against a cheating prover the verifier's
   work is polynomial in the message length, not in `|x|` (gate 03e, finding 1; ruling G3-3).
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges /
    colour permutations); one-iteration ZK, `n`-fold protocols get soundness only (sequential
    composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are stated, but no
    source protocol attains them under D8/D10; GI is `StatZK` with negligible δ, and
    `PerfectZKAbort.statZK` turns the abort form into statistical ZK with error `2^{-|x|}`
    (gate 03e, finding 2; ruling G3-4).
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
    of ch. 2–8 is vacuous by it.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least"; Lemma 50.15: "`N > 2`
    composite" should be odd composite.
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary.
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).
51. Definition 121.2 read literally (`∀ z ∈ {0,1}*`, the distinguisher polynomial-time in its
    input) fails for every protocol whose hiding is only computational: with `|z| ≥ 2^n` the
    distinguisher, whose input (the view) contains `z`, may run in time `2^n`, invert the OWP on
    `n`-bit inputs and open the unopened commitments. So the bound `∀ Lz : PolyExpr` on `|z|`, and
    indexing the distinguisher's advice by `|x|` rather than by its input length, are necessary,
    not only convenient (gate 03e, finding 9; `ZeroKnowledge/Defs.lean`'s module docstring).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (deferred); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
   The one admission in this area is the optional bridge
   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | The `j`-th block of `c` bits of a coin string, `(r.drop (j * c)).take c`, stated three times: `coinSlice` (`ZeroKnowledge/GraphIsomorphism.lean`, ch. 2–4), `Authentication.coinBlock` (`Authentication/Lamport.lean`, prong A), `Protocol.phaseSlice` (`Composability/SequentialZK.lean`, prong C) | found by the Lamport worker and the maintainer | Before the ch. 5–8 statement gate: one copy in a shared upstream module, with its length lemma, used by all three. |
| DL-7 | `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`: `Authentication.ofFn_padFin_of_length` (`Lamport.lean`) is the equal-length case of ch. 2–4's `ofFn_padFin_of_le` (`Asymptotic/Collections.lean`); `Composability.length_eval_of_length` (`CCA2Scheme.lean`) repeats the step inline | found by the Lamport worker | Before the ch. 5–8 statement gate: use `ofFn_padFin_of_le (le_of_eq h)`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, six copies plus an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`; with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; scheduled (G3-5) | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | accepted; scheduled (R-03l-1: clean up in gate 03's PR) | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | accepted; scheduled (R-03l-1) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | noted | Rename or merge in the same PR. |
