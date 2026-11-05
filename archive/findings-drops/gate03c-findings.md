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
