# Report · external ingest job `dw8-ingests` (four sources)

Deferred-work item **DW-8**. Documentation only: no Lean was run and no `.lean` file was
changed. Four scoped source ingests — [BGZ09], [Sho04], [Gen09], [Vad12] — mirroring the
DW-7 format (`.raw.md` scoped mechanical extraction + `.md` scoped transcription with
proofmatch anchors), plus their `sources.json` rows.

- **Exchange branch read:** `exchange/pass-shelat-ch5-8` at `6f06e06b78367ab24bed7f59d3d28b8ca336bebe`
  ("Ingest DW-8: record the uploaded PDF file names"), which has
  `f9f9d5e31e992d06ec3be5b3123bf9d185c3557d` as an ancestor, as required.
  `outbox/ingests/dw8/` verified with its `SHA256SUMS`: `brief.md: OK`, `README.md: OK`.
- **Records base:** `cryptography/pass-shelat-ch2-4` at
  `6f08055d5cc533c70c0c91bf7e92aa899466c323` ("Records: DW-8 PDFs go to exchange
  inbox/sources/pdfs/; brief updated"). Work done on a local branch `ingest/dw8` with
  `commit.gpgsign=false`; the branch was not pushed.
- **No PDF is in this delivery**, and the records series touches only
  `blueprint/src/references/`.
- Tooling: `pdftotext`/`pdfinfo`/`pdftoppm` from Poppler 24.02.0 — the same `pdftotext`
  version DW-7 used — and Python run as `python3 -I`, with every script kept in a scratch
  directory outside the PDF folder. No script is committed.

---

## 1. The uploads

All four PDFs named in the brief are present in `inbox/sources/pdfs/` on the exchange
branch, under the file names the README gives. **Nothing is missing.** The two hashes the
brief lists both verify; the other two are recorded here.

| Tag | File in `inbox/sources/pdfs/` | Pages | SHA-256 | Status |
|---|---|---|---|---|
| [BGZ09] | `barthe-gregoire-zanella-2009-popl.pdf` | 12 | `216f8cd86ce5e077730bcf9d5ed1a90131f0107d23e64f249c7df02690b4678a` | **verified against the brief** |
| [Sho04] | `shoup-2004-332.pdf` | 33 | `fde1f65e83ec85297f58840bf87de15fb68e91ada8aefaf77db3b153cf826820` | **verified against the brief** |
| [Gen09] | `craig-thesis.pdf` | 209 | `9e7f32f1b8543416fc6c2fcbfedd5d2d69150226b9bbd2cccac57840a5db7b66` | **recorded** (brief said "record it") |
| [Vad12] | `pseudorandomness-published-Dec12.pdf` | 339 | `bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c` | **recorded** (brief said "record it") |

The two file names differ from the brief's table exactly as the README says: [Gen09] is
`craig-thesis.pdf` (not `gentry-2009-thesis.pdf`) and [Vad12] is
`pseudorandomness-published-Dec12.pdf` (not `vadhan-2012-pseudorandomness.pdf`). The
hashes above are recorded under the uploaded names.

The anchor prefix of each ingest is `pdf-` + the first 12 hex characters of its upload's
SHA-256, as in DW-7 and as `proofmatch.document.stable_block_id` computes it:

| Tag | Ingest key | Anchor prefix |
|---|---|---|
| BGZ09 | `barthe-gregoire-zanella-2009-certified-proofs` | `pdf-216f8cd86ce5-` |
| Sho04 | `shoup-2004-sequences-of-games` | `pdf-fde1f65e83ec-` |
| Gen09 | `gentry-2009-fhe-thesis` | `pdf-9e7f32f1b854-` |
| Vad12 | `vadhan-2012-pseudorandomness` | `pdf-bf2ce5422088-` |

## 2. The delivered files

Under `src/`; identical to what the patch series writes under
`blueprint/src/references/`.

| File | SHA-256 |
|---|---|
| `barthe-gregoire-zanella-2009-certified-proofs.raw.md` | `8090e1f784b39d8f8d2336f21f3e767cf83b19db5c734d2944b2060a839ed117` |
| `barthe-gregoire-zanella-2009-certified-proofs.md` | `92511dcba1022cc96483ebe96356883937cacb85a589a41a0b770c6a1cab0372` |
| `shoup-2004-sequences-of-games.raw.md` | `3a8041908b0975057a34ef0ee21df74603e5ca0bc484f8927152b6ecc7b224f8` |
| `shoup-2004-sequences-of-games.md` | `3dfc581404fcadc57a5cf62e72040817b9ee278c3bd0cbc43de8bdf0e5bc983f` |
| `gentry-2009-fhe-thesis.raw.md` | `c88465ed38124ad78a9c2814c14b06f9fd74c0e8ec96d83f54f77e90f48ce064` |
| `gentry-2009-fhe-thesis.md` | `078db24941b2d00f6f307747ecff87a15d96878fdaab6a008b6c0de14a781d0d` |
| `vadhan-2012-pseudorandomness.raw.md` | `e4cb725446a2afeaadda73cf4bfdd13faa8c05b62158df1eb2e150772905f192` |
| `vadhan-2012-pseudorandomness.md` | `74faefebc6a67a3be3fa398ff11786fb821d153ae3062cf402ab6034c54a4964` |
| `sources.json` | `2e80ff54cbf15451556c75333826a1be0c48f38b52734bbd9aabfee009defee4` |

**Checks run.** All four new `.md` files parse with the repository's own
`proofmatch.document.parse_validated_markdown`, and all four `.raw.md` files with
`proofmatch.document._raw_payload`; the DW-7 pairs were run alongside as a baseline and
behave the same. Every anchor in the four new `.md` files equals
`stable_block_id(fingerprint, page, sequence)` for its own provenance comment — 53 anchors
checked, 0 mismatches.

| File | Blocks parsed | Kinds |
|---|---|---|
| `barthe-gregoire-zanella-2009-certified-proofs.md` | 15 | 11 prose, 1 definition, 2 theorem, 1 proof |
| `shoup-2004-sequences-of-games.md` | 10 | 8 prose, 2 theorem |
| `gentry-2009-fhe-thesis.md` | 15 | 10 prose, 2 definition, 3 theorem |
| `vadhan-2012-pseudorandomness.md` | 13 | 3 prose, 6 definition, 4 theorem |

---

## 3. [BGZ09] — citation locations, anchors and assessment

**Cited for:** the new `Games.ProbComp.expect_simulate_rel` — two oracle implementations
with states related by an invariant, where each call preserves the invariant and gives
equal answer laws, so that whole runs agree. Sources for the ask:
`briefs/pairings/fills/bb1-sim/design-r1.md` §2.2 (the module's `## References` block,
which carries `⟨location to pin, Q11⟩`) and §5 risk 7; `briefs/pairings/fills/bb1-sim/rulings.md`
Q11 ("Ingest and cite [BGZ09] and [Sho04] … the citations are a docstring-only follow-up
after the ingest").

**Pages ingested (physical = printed):** 6, 7, 8, 9, 10.

| Citation, in the library's form | Anchor | What it gives |
|---|---|---|
| `[BGZ09, §4.1, Def. 5]` | `pdf-216f8cd86ce5-p007-b002` | pRHL judgments: `⊨ G₁ ∼ G₂ : Ψ ⇒ Φ ≝ ∀ m₁ m₂. m₁ Ψ m₂ ⇒ ⟦G₁⟧m₁ ∼_Φ ⟦G₂⟧m₂` |
| `[BGZ09, §4.1, lifting to distributions]` | `pdf-216f8cd86ce5-p007-b001` | `range P μ`, `μ₁ ∼_Φ μ₂`, the projections |
| **`[BGZ09, §4.1, lemma (=⟦⟧)]`** | **`pdf-216f8cd86ce5-p007-b005`** | **`f =_Φ g ≝ ∀m₁m₂. m₁ Φ m₂ ⇒ f(m₁)=g(m₂)`, and the judgment plus `f =_Φ g` plus `m₁ Ψ m₂` give `⟦G₁⟧m₁ f = ⟦G₂⟧m₂ g`** |
| `[BGZ09, §4.1, lemma (≤⟦⟧)]` | `pdf-216f8cd86ce5-p008-b002` | the `≤` variant, and termination sensitivity at `f = g = 𝟙` |
| `[BGZ09, §4.1, Fig. 5]` | `pdf-216f8cd86ce5-p008-b001` | the derived rules [R-Skip], [R-Seq], [R-Ass], [R-Rand], [R-Cond], [R-Whl], [R-Sub], [R-Sym], [R-Tr], [R-Case] |
| `[BGZ09, §4.1, [R-Rand] bijection premise]` | `pdf-216f8cd86ce5-p007-b004` | `⟦d₁⟧m₁ =_g ⟦d₂⟧m₂`: a bijection of supports matching masses |
| `[BGZ09, §4.1, [R-Comp]/[R-Inv]]` | `pdf-216f8cd86ce5-p007-b003` | composition of relations; one-sided variants |
| **`[BGZ09, §4.2, ⊨_φ G₁ ≃ᴵ_O G₂]`** | **`pdf-216f8cd86ce5-p008-b003`** | **the invariant-carrying observational equivalence `⊨ G₁ ∼ G₂ : =_I ∧ φ ⇒ =_O ∧ φ`, and the `Ψ,Φ` variant** |
| `[BGZ09, §3.4, well-formed adversaries]` | `pdf-216f8cd86ce5-p006-b001` | "A well-formed adversary is free to call oracles, but any other procedure it calls must be a well-formed adversary itself." |
| `[BGZ09, §4, opening]` | `pdf-216f8cd86ce5-p006-b002` | Shoup's three categories; a bridging step is valid only in the context where it is done |
| `[BGZ09, §5.2, Lemma 1]` | `pdf-216f8cd86ce5-p009-b002` | lazy/eager sampling over an arbitrary context `C[·]` |
| `[BGZ09, §5.2, context]` | `pdf-216f8cd86ce5-p009-b001` | "a program context with multiple holes that may appear either in the main program or any of the procedures in the environment" |
| `[BGZ09, §5.2, O_l → O_e]` | `pdf-216f8cd86ce5-p009-b003`, `pdf-216f8cd86ce5-p010-b001` | replacing a lazy random oracle by an eager one "in the environment of a program" |
| `[BGZ09, §5, opening]` | `pdf-216f8cd86ce5-p008-b004` | bridging steps are what CertiCrypt's tactics automate |

### Assessment — partial, and one gap to report

**The design note asked for "the rule for adversary calls with oracles that keep a
relational invariant" (design-r1.md §2.2, §5 risk 7). This paper contains no such named
rule.** Figure 5 is the complete list of derived rules it states, and it has no adversary
rule; the only named rules in the paper are [R-Skip], [R-Seq], [R-Ass], [R-Rand],
[R-Cond], [R-Whl], [R-Sub], [R-Sym], [R-Tr], [R-Trans], [R-Case], [R-Comp], [R-Inv] and
[R-Opt]. I searched the whole text for a rule keyed to adversary or oracle calls and found
none; the word "invariant" occurs once in the paper, in the §4 opening sentence recorded
above. This is the gap that design-r1.md §5 risk 7 anticipated ("the locations … are not
pinned here … nothing was read to confirm a section number").

What the paper does give, and what I would cite instead, is a close two-part match:

1. **`(=⟦⟧)` (p. 7, `…p007-b005`) is the conclusion shape of `expect_simulate_rel`,
   almost literally.** In CertiCrypt a distribution *is* a function `(X → [0,1]) → [0,1]`
   (the measure monad, §3.2, p. 5), so `⟦G⟧ m f` is the expectation of `f`. The lemma then
   reads: from a judgment with postcondition `Φ`, and two test functions that *agree along
   `Φ`*, the two runs give equal expectations. The Lean target states exactly this with
   `Φ := R` on states and `G₁, G₂ :=` the two simulations. This is a direct, strong
   support — stronger than what the design note asked for, because it is the very
   "expectations of test functions agreeing along the relation" form that ruling Q3 chose.
2. **`⊨_φ G₁ ≃ᴵ_O G₂` (p. 8, `…p008-b003`) is the invariant half**: an equivalence that
   carries a relation `φ` through as both pre- and postcondition, which is what "each call
   preserves the invariant" means. The paper calls these variants "widely used in
   game-based proofs".

The adversary-call aspect is supported *indirectly but soundly*: §3.4 fixes that an
adversary is an arbitrary well-formed procedure whose only privileged calls are to oracles,
and §5.2's Lemma 1 is stated over a context `C[·]` whose holes "may appear either in the
main program or any of the procedures in the environment" — i.e. the equivalence is proved
once and holds whatever the adversary does. The worked `O_l → O_e` replacement is the
paper's own instance of "swap one oracle implementation for another with a different
internal state, inside an arbitrary program". That is the same move `expect_simulate_rel`
makes, but the paper proves it for that one pair of oracles, not as a general rule over a
relational invariant.

**Recommendation.** Cite `[BGZ09, §4.1, lemma (=⟦⟧), p007-b005]` and
`[BGZ09, §4.2, ⊨_φ, p008-b003]` for the lemma's *form*, and
`[BGZ09, §5.2, Lemma 1, p009-b002]` for the arbitrary-context/adversary aspect. Do **not**
cite a "rule for adversary calls": there is none to pin in this paper. If the maintainer
wants a named adversary rule with a relational invariant, it is in the later EasyCrypt /
CertiCrypt literature rather than in this POPL 2009 paper; that would be a new ingest and a
new ruling, and it is outside this job's scope.

---

## 4. [Sho04] — citation locations, anchors and assessment

**Cited for:** the same `Games.ProbComp.expect_simulate_rel`; specifically the
game-hopping transition types, and in particular **bridging steps** (a change of a game
that does not change its distribution).

**Pages ingested (physical = printed):** 1, 2, 3, and 11–13 for the worked example.

| Citation, in the library's form | Anchor | What it gives |
|---|---|---|
| **`[Sho04, §1.1, bridging steps]`** | **`pdf-fde1f65e83ec-p003-b002`** | **"a way of restating how certain quantities can be computed in a completely equivalent way. The change is purely conceptual, and `Pr[S_i] = Pr[S_{i+1}]`."** |
| `[Sho04, §1.1, the three transition types]` | `pdf-fde1f65e83ec-p002-b001` | "transitions between successive games can be restricted to one of three types" |
| `[Sho04, §1.1, transitions based on indistinguishability]` | `pdf-fde1f65e83ec-p002-b002` | the hybrid/distinguisher construction |
| `[Sho04, §1.1, transitions based on failure events]` | `pdf-fde1f65e83ec-p002-b003` | `S_i ∧ ¬F ⟺ S_{i+1} ∧ ¬F` |
| `[Sho04, §1.1, Lemma 1 (Difference Lemma)]` | `pdf-fde1f65e83ec-p003-b001` | `A ∧ ¬F ⟺ B ∧ ¬F ⟹ |Pr[A] − Pr[B]| ≤ Pr[F]`, with proof |
| `[Sho04, §1.1, one probability space]` | `pdf-fde1f65e83ec-p003-b003` | all games on one space; the generalized Difference Lemma |
| `[Sho04, §1, Introduction]` | `pdf-fde1f65e83ec-p001-b002` | what the technique is and is not |
| `[Sho04, §1.1, attack games]` | `pdf-fde1f65e83ec-p001-b003` | the game/event `S`/target-probability setting |
| `[Sho04, §4.2, Game 2]` | `pdf-fde1f65e83ec-p013-b001` | a worked bridging step: the "gnome" reformulation of a random oracle, `Pr[S₂] = Pr[S₁]` |

### Assessment — direct

This is the most directly supportive of the four. The cited notion is defined in one
sentence and matches the lemma's content precisely: `expect_simulate_rel` says two
implementations that answer alike from related states make the two runs agree, which is
exactly "a way of restating how certain quantities can be computed in a completely
equivalent way … purely conceptual, and `Pr[S_i] = Pr[S_{i+1}]`". The companion
`prob_simulate_rel`, which gives equal acceptance probabilities for games returning a bit,
is literally the `Pr[S_i] = Pr[S_{i+1}]` conclusion.

The worked Game 2 at `p013-b001` strengthens this: the step replaces a random function
oracle by a "gnome" that keeps a table — **two implementations with different internal
state that answer identically** — and Shoup justifies the equality by the change being
"purely conceptual". That is the informal version of the Lean lemma's hypothesis and
conclusion.

One useful cross-link for the docstrings: [BGZ09] §4 opening (`…p006-b002`) cites this
paper as "[31]" and names the same three categories, so the two tags agree on the
vocabulary.

**Note on the uploaded copy.** The brief and `design-r1.md` describe [Sho04] as the
"revision of 18 January 2006"; the uploaded PDF's title page carries exactly that date,
with "First public version: Nov. 30, 2004" in a footnote. The `sources.json` title records
both facts.

---

## 5. [Gen09] — citation locations, anchors and assessment

**Cited for:** GSW phase 6b's leveled scheme — the key chain (one evaluation key per
level, each encrypting the previous level's secret key) and its security hybrid.
Sources for the ask: `briefs/lattice-gsw/phase6/plan-section.md` r3 §H1 gap 1 and §H3.11;
`briefs/lattice-gsw/phase6/rulings.md` P6-Q14 and P6-Q19 with its refinement.

**Pages ingested:** physical 53–62, i.e. printed 43–52 (anchors use the physical page;
printed = physical − 10).

| Citation, in the library's form | Anchor | What it gives |
|---|---|---|
| **`[Gen09, §4.1, KeyGen_{E^(d)}]`** | **`pdf-9e7f32f1b854-p056-b003`** | **the key chain: `(sk_i,pk_i) ← KeyGen(λ)` for `i ∈ [0,d]`, and `sk̄_ij ← Encrypt(pk_{i−1}, sk_ij)` for `i ∈ [1,d]`, `j ∈ [1,ℓ]`** |
| `[Gen09, §4.1, overview]` | `pdf-9e7f32f1b854-p053-b001` | "`d+1` public keys … together with a chain of encrypted `E` secret keys"; "we base the semantic security of `E^(d)` on that of `E` using a hybrid argument … the reduction loses a factor linear in `d`" |
| **`[Gen09, Thm 4.2.3]`** | **`pdf-9e7f32f1b854-p060-b001`** | **the security hybrid: Game `k` replaces, for `i ∈ [1,k]`, `sk̄_ij` by an encryption of a random `sk′_i` unrelated to `sk_i`; `ε′ ≥ ε/ℓ(d+1)`** |
| `[Gen09, Thm 4.2.3, reduction]` | `pdf-9e7f32f1b854-p061-b001` | `B` plants its challenge key at index `k`, simulating Game `k+β` |
| `[Gen09, Thm 4.2.1]` | `pdf-9e7f32f1b854-p059-b001` | correctness: `E^(d)` compactly evaluates all depth-`d` circuits over `Γ` |
| `[Gen09, §4.1, refreshing]` | `pdf-9e7f32f1b854-p054-b001` | re-encrypt under `pk_{i+1}`, then homomorphically decrypt using `sk_i` encrypted under `pk_{i+1}` |
| `[Gen09, §4.1, Recrypt]` | `pdf-9e7f32f1b854-p054-b002` | the Recrypt algorithm |
| `[Gen09, Def. 4.1.2]` | `pdf-9e7f32f1b854-p055-b001` | `g`-augmented decryption circuits, `D_E(Γ)` |
| `[Gen09, Def. 4.1.3]` | `pdf-9e7f32f1b854-p056-b001` | bootstrappable: `D_E(Γ) ⊆ C_E`; trivial gate + NAND suffice |
| `[Gen09, §4.1, reverse order]` | `pdf-9e7f32f1b854-p056-b002` | "we encrypt the secret keys in reverse order; the only reason is that this ordering simplifies our description of the recursion in Evaluate" |
| `[Gen09, §4.1, Evaluate]` | `pdf-9e7f32f1b854-p057-b001` | the per-level recursion, and **"each wire in `C_δ` connects gates at consecutive levels; if not, add trivial gates to make it so"** |
| `[Gen09, §4.1, Augment/Reduce]` | `pdf-9e7f32f1b854-p057-b002` | the per-level machinery |
| `[Gen09, §4.1, high-level review]` | `pdf-9e7f32f1b854-p058-b001` | per gate: `sk_d` under `pk_{d−1}`, plus re-encryptions of `ψ_w` under `pk_{d−1}` |
| `[Gen09, §4.3, acyclic chain]` | `pdf-9e7f32f1b854-p061-b002` | "Using an acyclic chain of encrypted secret keys allowed us to base the security of `E^(d)` on `E` using a hybrid argument; this hybrid argument breaks down when there is a cycle" |
| `[Gen09, Rem. 4.3.1]` | `pdf-9e7f32f1b854-p062-b001` | Canetti proposed the acyclic, leveled approach |

### Assessment — direct for the construction, direct but differently arranged for the hybrid

**The key chain (P6-Q14, §H3.11 "Evaluation key: the consecutive chain") is exactly this
passage.** The plan's "`evk_d` holds the encryptions under `pk_d` of the `N` key bits of
`s_{d−1}`, that is `N·L` ciphertexts, and only the evaluation key depends on `L`" is
Gentry's `sk̄_ij ← Encrypt(pk_{i−1}, sk_ij)` for `i ∈ [1,d]`, `j ∈ [1,ℓ]` — `ℓ·d`
ciphertexts, with only that part of the public key growing with `d` (§4.3 opening says so
in as many words). §H1 gap 1's "reconstructed" status can be closed against
`p056-b003`. P6-Q14's "textbook chain" is a fair name for it.

**Two differences the docstrings should state rather than paper over:**

1. **Index direction.** Gentry encrypts `sk_i` under `pk_{i−1}`, encrypts the message
   under `pk_d` and decrypts under `sk_0`, so evaluation runs *down* the index; the plan
   encrypts `s_{d−1}` under `pk_d`, puts fresh ciphertexts at level 0 and decrypts under
   `s_{depth}`, running *up*. It is the same chain with the opposite convention, and
   Gentry says the direction is a presentational choice (`p056-b002`), so this is not a
   mathematical difference — but a reader comparing the two will trip on it, and the
   transcription records the convention explicitly at the top of the file.
2. **What the hybrid substitutes, and in which direction.** Gentry's Game `k` replaces
   `sk̄_ij` for `i ∈ [1,k]` by encryptions of an *unrelated random secret key* `sk′_i`,
   stepping `k = 0 … d` upward, with a final Game `d+1` that randomizes the challenge; the
   plan's §H3.11 hybrid runs "from the top level down" and replaces the `N` encryptions
   under `pk_d` by **encryptions of `0`**. Both are legitimate and both are justified by
   the same observation — that `s_d`'s bits occur only in `evk_{d+1}`, already replaced —
   but they are not the same hybrid, and the `ε/ℓ(d+1)` loss is stated for Gentry's.
   `[Gen09, Thm 4.2.3]` supports the *existence and shape* of a level-by-level hybrid over
   an acyclic key chain; it does not literally state the plan's zero-substitution variant.

**Bonus finding for §H3.13 / P6-Q14's layering conversion.** Gentry's `Evaluate`
(`p057-b001`) already *assumes* the circuit is layered — "We assume that each wire in `C_δ`
connects gates at consecutive levels; if not, add trivial gates to make it so" — which is
precisely the plan's new generic layering conversion that "pads uneven paths with
double-NAND identity chains". So [Gen09] supports P6-Q14's layering requirement too, as
an assumption discharged by padding, and `p057-b001` is the anchor for it.

Per P6-Q19's refinement, nothing waited on this ingest and no Lean docstring cites
`[Gen09]` yet; adding the citations above is the docstring-only follow-up recorded in
§H10.

---

## 6. [Vad12] — citation locations, anchors, and the check against the three `.lean` files

**Cited for:** Theorem 6.18, the leftover hash lemma, and the definitions it needs.

**Pages ingested:** physical 67, 88, 172, 174, 176, 179, 181, 182, 183, 184, 212, 213 —
i.e. printed 64, 85, 169, 171, 173, 176, 178, 179, 180, 181, 209, 210 (anchors use the
physical page; printed = physical − 3).

| Citation, in the library's form | Anchor | What it gives |
|---|---|---|
| **`[Vad12, Thm 6.18]`** | **`pdf-bf2ce5422088-p182-b002`** | **the Leftover Hash Lemma, with its proof opening** |
| `[Vad12, Thm 6.18, proof]` | `pdf-bf2ce5422088-p183-b001` | the three steps, ending "we have in fact obtained a strong `(k, ε/2)`-extractor" |
| `[Vad12, Def. 6.16]` | `pdf-bf2ce5422088-p181-b001` | strong extractors; `Ext′(x,y) = (y, Ext(x,y))` is a standard extractor |
| `[Vad12, Def. 6.13]` | `pdf-bf2ce5422088-p179-b001` | seeded `(k,ε)`-extractors |
| `[Vad12, Def. 6.9]` | `pdf-bf2ce5422088-p176-b001` | `k`-source: `H_∞(X) ≥ k`, i.e. `Pr[X=x] ≤ 2^{−k}` |
| `[Vad12, Def. 6.7]` | `pdf-bf2ce5422088-p174-b001` | Shannon, Rényi and min-entropy |
| `[Vad12, Def. 6.2]` | `pdf-bf2ce5422088-p172-b001` | statistical difference `Δ(X,Y)`, `ε`-close, and Lemma 6.3 |
| `[Vad12, Def. 3.21]` | `pdf-bf2ce5422088-p067-b001` | pairwise independent hash functions |
| **`[Vad12, §3.5, 2-universal]`** | **`pdf-bf2ce5422088-p067-b002`** | **2-universal: `Pr[H(x₁)=H(x₂)] ≤ 1/M` for all `x₁ ≠ x₂`; "strongly 2-universal" is the pairwise independent notion** |
| `[Vad12, Def. 4.7]` | `pdf-bf2ce5422088-p088-b001` | collision probability `CP(π) = Σ_x π_x²`, and Lemma 4.8 |
| `[Vad12, Thm 6.17]` | `pdf-bf2ce5422088-p182-b001` | the existence bound 6.18 is stated against |
| `[Vad12, §6.2.1, Rényi remark]` | `pdf-bf2ce5422088-p184-b001` | the proof also gives a strong Rényi-entropy extractor; seed length is necessarily large |
| `[Vad12, ch. 6 notes]` | `pdf-bf2ce5422088-p212-b001` | Theorem 6.18 is due to Impagliazzo, Levin and Luby; the proof is Rackoff's |

### The check against the three existing `.lean` citations — **the number and statement match**

All three files cite it identically, as `* [Vad12] S. Vadhan, *Pseudorandomness*, 2012,
Theorem 6.18.`:

| File | Line | What the module uses it for |
|---|---|---|
| `TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean` | 38 | `extractionError`, "the explicit strong leftover-hash error"; the uniform-key view is within that error of a fully independent uniform view |
| `TCSlib/Cryptography/Hashing/SIS/Columns.lean` | 33 | `distAdv_hashColumns_uniform_le`, a column-by-column hybrid over the single-column leftover-hash error |
| `TCSlib/Cryptography/Hashing/SIS/Universality.lean` | 30 | "a strong, seed-published leftover-hash bound"; "The proofs use the owner-side universality and min-entropy equivalences to apply the strong leftover-hash lemma" |

**Result: no mismatch. The theorem number is right and the statement is the right one, on
four points that matter.**

1. **Number and name.** In the uploaded published edition, Theorem 6.18 is titled
   "(Leftover Hash Lemma)" — printed page 179, physical page 182, verified against the page
   image at 150 dpi. There is exactly one Theorem 6.18 in the monograph.
2. **It is the *strong* form, which is what all three modules need.** The theorem states
   `Ext(x,h) ≝ h(x)` is a **strong** `(k,ε)`-extractor, and "Equivalently,
   `Ext(x,h) = (h, h(x))` is a standard `(k,ε)`-extractor". Definition 6.16
   (`…p181-b001`) defines a strong extractor by `(U_d, Ext(X,U_d))` being `ε`-close to
   `(U_d, U_m)` — the seed is published alongside the output. That is precisely
   `Universality.lean`'s "strong, seed-published leftover-hash bound" and
   `Columns.lean`'s `(A, A R)` close to `(A, U)` with the matrix `A` (the seed) published
   on both sides. Had the citation been to a non-strong form, the published-seed use would
   have been wrong; it is not.
3. **The hypothesis covers collision-universality, not just pairwise independence.**
   `Universality.lean` is explicit that "The family is collision-universal, not pairwise
   independent: its zero input always hashes to zero." Theorem 6.18's hypothesis is "a
   pairwise independent **(or even 2-universal)** family", and §3.5 (`…p067-b002`) defines
   2-universal as just `Pr[H(x₁)=H(x₂)] ≤ 1/M` for `x₁ ≠ x₂` — no uniformity of `H(x)` is
   required, so a family whose zero input always hashes to zero is admissible. The proof
   uses only that weaker property: step (1) invokes it as
   `Pr[H(X)=H(X′) | X ≠ X′] ≤ 1/M` "by 2-universality" (`…p183-b001`). **The citation is
   therefore correct for exactly the reason `Universality.lean` flags**, and that file's
   caveat is not a divergence from [Vad12] but an instance of its stated generality.
4. **Parameters.** The theorem's `m = k − 2log(1/ε)` matches the modules' use of an
   explicit extraction error with a min-entropy input and an output length short of the
   entropy by twice the log of the error.

**Two points worth carrying into the docstrings, neither a mismatch:**

- Theorem 6.18 is stated for `(k,ε)` but its proof ends "Thus, we have in fact obtained a
  strong `(k, ε/2)`-extractor" (`…p183-b001`). The theorem as stated is the weaker,
  correct claim; anyone comparing the Lean error term against the proof's arithmetic
  should know the proof delivers a factor 2 better than the headline. If the Lean
  `extractionError` was calibrated to the proof rather than the statement, that is
  consistent, not a conflict.
- The citation string in all three files is "S. Vadhan, *Pseudorandomness*, 2012,
  Theorem 6.18" with no edition. Theorem numbering can differ between the circulating
  draft and this published Now Publishers edition; the number checks out **in the uploaded
  published edition**, whose hash is recorded above, and the ingest pins it to printed page
  179. If the maintainer wants the citation to be edition-proof, adding the page or the
  anchor would do it — but **no change is required**, and the brief's instruction not to
  edit `.lean` files was followed.

### Assessment — direct

The most clear-cut of the four: the cited theorem exists under the cited number, says the
strong-extractor statement the modules rely on, and its hypothesis is the weaker
2-universality the modules actually satisfy.

---

## 7. The `sources.json` diff

Four rows added; nothing else changed. The registry goes from 22 to 26 tags. The rows were
created with the repository's own tool,
`python3 -I scripts/reference_coverage.py --register TAG=DOCUMENT` (the same path
`scripts/sources.py register` takes, which DW-7 used), so key ordering and formatting are
the tool's; the titles were then filled in to match the existing style.

```diff
--- a/blueprint/src/references/sources.json
+++ b/blueprint/src/references/sources.json
@@ -20,6 +20,12 @@
         "boneh-boyen-2004-selective-id-ibe"
       ]
     },
+    "BGZ09": {
+      "title": "G. Barthe, B. Grégoire, S. Zanella Béguelin, Formal Certification of Code-Based Cryptographic Proofs, POPL 2009 (the uploaded version's byline reads “Santiago Zanella”).",
+      "documents": [
+        "barthe-gregoire-zanella-2009-certified-proofs"
+      ]
+    },
     "BV11": {
       "title": "Z. Brakerski, V. Vaikuntanathan, Efficient Fully Homomorphic Encryption from (Standard) LWE, FOCS 2011; full version (39 pages).",
       "documents": [
@@ -68,6 +74,12 @@
         "gentry-sahai-waters-2013-fhe"
       ]
     },
+    "Gen09": {
+      "title": "C. Gentry, A Fully Homomorphic Encryption Scheme, PhD thesis, Stanford University, September 2009.",
+      "documents": [
+        "gentry-2009-fhe-thesis"
+      ]
+    },
     "Jou00": {
       "title": "A. Joux, A One Round Protocol for Tripartite Diffie–Hellman, ANTS-IV, LNCS 1838, pp. 385–393, Springer, 2000.",
       "documents": [
@@ -137,6 +149,18 @@
         "roughgarden-cc-oneway"
       ]
     },
+    "Sho04": {
+      "title": "V. Shoup, Sequences of Games: A Tool for Taming Complexity in Security Proofs, Cryptology ePrint Archive 2004/332, revision dated 18 January 2006.",
+      "documents": [
+        "shoup-2004-sequences-of-games"
+      ]
+    },
+    "Vad12": {
+      "title": "S. Vadhan, Pseudorandomness, Foundations and Trends in Theoretical Computer Science 7(1–3):1–336, 2012.",
+      "documents": [
+        "vadhan-2012-pseudorandomness"
+      ]
+    },
     "Ver18": {
       "title": "",
       "documents": [
```

**On "with the PDF hashes".** The brief asks for the rows to be "in the existing schema,
with the PDF hashes", but the existing schema has no hash field: all 22 pre-existing rows
are exactly `{"title": …, "documents": […]}`. I kept the schema unchanged, as DW-7 did,
and the hashes are recorded where DW-7 records them — in each document's own
`<!-- source-pdf-sha256: … -->` header, in both the `.raw.md` and the `.md`, and in §1 of
this report (the phase-6 plan's §H1 table is populated the same way). **If a hash field in
`sources.json` was actually wanted, that is a schema change touching
`reference_coverage.py` and all 26 rows, and it needs a ruling; say the word and it is a
small follow-up.**

---

## 8. Missing, illegible, or otherwise worth flagging

- **Nothing is missing.** All four PDFs were present and all four were ingested. No gap to
  report under the brief's "if a file is missing" clause.
- **One illegible glyph, [Sho04].** The paper's random-assignment arrow carries a small
  mark above it. `pdftotext` renders the mark as the two characters `c|`; on the page image
  read at 600 dpi it is a cent-like sign (a "c" with a vertical stroke) and is **not**
  legibly an "R". I did not identify it, and did not guess: it is written as
  `\stackrel{\scriptscriptstyle ?}{\leftarrow}` with a transcription note saying so, and
  its *meaning* (uniform random choice from the set on the right) is established from the
  paper's own prose and its parallel use in §4.1, not assumed.
- **Printed typos transcribed as printed, not silently fixed** — each carries a
  transcription note: [Sho04] abstract "This paper is brief tutorial … as sequences games",
  and "cryptograptic", "probabilstic", "probabilty", "prodceeds", "succesive",
  "auxilliary", "auxiallary" (pp. 1–2); [Gen09] "Recrypt takes as these things as input"
  (p. 44) and the incomplete final clause of the proof of Theorem 4.2.3 (p. 51);
  [Vad12] p. 180, where the "if and only if" sentence prints `(H,H(X)) = (H′,H′(X))` with
  an unprimed `X`, although the surrounding argument uses `(H′,H′(X′))`.
- **Glyphs dropped by `-layout` and restored from page images** (each noted in place, and
  each checked at 150 dpi or better): `≠` throughout [Vad12]; the `ℓ₁`/`ℓ₂` norm bars and
  subscripts in [Vad12] Lemma 4.8 and the proof of Theorem 6.18; `M ≪ K` and the prime on
  `Ext′` in [Vad12] Definition 6.16; the overbars marking encrypted values in [Gen09]
  (`sk̄_ij` vs `sk_ij`), which matter because without them the KeyGen line reads as
  circular; and [Gen09]'s `ε`, which the extraction prints as `²`.
- **Two-column reading order, [BGZ09].** Poppler interleaves the columns around figures, so
  in the `.raw.md` a heading can appear after the text it heads (§3.4 on p. 6 is the
  clearest case). The raw file is left exactly as Poppler produced it; the `.md` restores
  the reading order, and both the raw header and the `.md` scope note say so. For this
  source the raw was taken one page at a time without `-layout` (reading order per page)
  rather than with `-layout` (which puts both columns side by side); the header records
  the exact command shape.
- **Author byline, [BGZ09].** The uploaded version's byline is "Gilles Barthe, Benjamin
  Grégoire, Santiago Zanella", without the third author's later surname "Zanella Béguelin"
  that the brief and the design note use. Both forms are recorded (the `sources.json` title
  and a transcription note).
- **`validation-status` line.** The four `.md` files carry
  `scoped transcription for DW-8; awaiting Codex source review`, mirroring DW-7's line
  verbatim as instructed. Flagging it only because the brief also says "write no model
  identifiers"; the files carry no identifier for the worker that produced them, and the
  word here is DW-7's own name for the review step. Say the word if you would rather it
  read differently.
- **No `.lean` file was read for anything but the [Vad12] check, and none was changed.**
  No Lean was run. No `briefs/` file was changed. The local `ingest/dw8` branch was not
  pushed, and no PDF was copied anywhere.
