# Public-key implications pilot — proposed contents

**Draft, 2026-11-07 PST.** Names below are proposals, not declarations claimed to exist.
Proof snippets are source-level drafts and have not been elaborated as a new module.

## First-class endpoints — selected by the user, 2026-11-07 PST

| Endpoint | Intended guarantee | Why include it |
|---|---|---|
| Multi-message IND-CPA public-key encryption | Correct efficient public-key encryption on a meaningful message space, indistinguishable under chosen-plaintext attack for polynomially many encryptions under one public key. State whether the theorem uses a batch or adaptive experiment. | The basic confidential-channel primitive; the first end-to-end target for RSA, factoring and DDH routes. |
| Multi-message IND-CCA2 public-key encryption | Correct efficient public-key encryption with adaptive decryption access, excluding all challenge ciphertexts in a multi-challenge formulation. | The robust encryption endpoint when the adversary can submit ciphertexts for decryption. |

**User ruling:** adopt these two endpoints, with IND-CCA1 documented as an intermediate.
Always write CCA1 or CCA2 explicitly;
“CCA” alone does not choose a game. CCA1 permits decryption queries only before the challenge;
CCA2 permits them afterwards subject to the challenge restriction. The taxonomy is reviewed
in [Pass, Cornell CS 6830, lecture 13 (2009), §1](https://www.cs.cornell.edu/courses/cs6830/2009fa/scribes/lecture13.pdf).

Do not add separate first-class entries for single-bit encryption, single-message security,
the bitwise construction, every weaker notion, or each padding stage. These are supporting
APIs. Non-malleability variants and stronger public-key functionalities can be considered
later when they provide a distinct endpoint required by a construction, rather than an
extra name for an already indexed guarantee.

No multi-message IND-CCA2 public-key construction is currently established in the surveyed
campaign source. Gate 06's encrypt-then-tag CCA2 construction is **private-key encryption**.
A public-key CCA2 row is a future target requiring its own construction/bridge work; no new
external audit or fill is prepared here.

## Shape of a catalog theorem

Each theorem has the form `(assumption A) → (assumption B) → … → ∃ S, targetSecurity S`, with
correctness and algorithmic efficiency bundled or explicitly conjoined. Use named concrete
hardness assumptions when available, keep all remaining premises visible, and show that S
has a meaningful message space. For the fixed-length model, a constraint such as
`S.msgLen = PolyExpr.var` prevents a vacuous empty-message-only witness. The exact final
Lean header and multi-message predicate still require design and checking.

Several assumption sets can lead to the same endpoint; those are useful separate theorems.
A chain of intermediate predicates for the same route is not a separate set of catalog
entries. RSA plus its retained infrastructure, factoring plus its retained infrastructure,
and DDH plus its retained infrastructure are the candidate rows below. Generic hard-core-TDP
facts remain available as the composition API behind these entries.

## Existing APIs and their exact security models

| Existing predicate | Meaning and source | Role here |
|---|---|---|
| `BitPublicKeyScheme.SingleBitSecure` | Indistinguishability of encryptions of bits; `Asymptotic/PublicKey.lean:250`. | Intermediate. |
| `PublicKeyScheme.Secure` | Indistinguishability for every equal-length pair of messages, public key included; `Asymptotic/PublicKey.lean:142`. | Input to the existing many-message lifting. |
| `PublicKeyScheme.MultiMessageSecure` | Polynomially many-message experiment; `Asymptotic/PublicKey.lean:166`. | Existing generic endpoint; do not silently equate this batch predicate with an adaptive oracle game. |
| `Composability.FixedLengthPKScheme.INDSecure .cpa` | Gate 06's two-stage, key-visible CPA oracle game; `Composability/PublicKey.lean` on integration only. | Precise CPA bridge, currently admitted. |
| `Candidates.GroupPKScheme.Secure` | ElGamal's key-dependent group-message selector model; `Candidates/ElGamal.lean:458`. | Separate current model; retain admissible-message correctness and prove the required conversion. |

## Existing generic chain — supporting material, not new catalog tiers

The hard-core-TDP → single-bit → bitwise → multi-message chain is already proved by existing
components. For T : TrapdoorCollection, one-wayness hT and ordinary hard-core security hHC,
the complete composition has the short source-level term:

```lean
  obtain ⟨E⟩ := hHC.nonempty_predEvaluator
  exact ⟨(T.tdpBitScheme E).bitwise,
    (T.tdpBitScheme_singleBitSecure E hT hHC).bitwise.multiMessageSecure⟩
```

This snippet has not been elaborated as a new wrapper. Reuse/index the existing APIs instead
of adding four theorem tiers. Sources: `Asymptotic/PublicKey.lean:749`, `:911`, `:353`,
`:471`, `:529`; [PS10, Algorithm 104.3, Theorem 104.4 and p. 103].
The public-key single-to-many-message hybrid argument also appears in
[Pass, Cornell CS 6830, lecture 13 (2009), Theorem 2](https://www.cs.cornell.edu/courses/cs6830/2009fa/scribes/lecture13.pdf).
This CPA-style bitwise construction must not be reused as a CCA2 length-extension argument.

`OneWay.exists_glPad_singleBitSecure` supplies the hard-core step for fixed-width encodings,
retaining m : PolyExpr and the exact premise

```lean
henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)),
  (T.encD (T.index n r) x).length = m.eval n
```

Sources: `Asymptotic/HardCoreCollection.lean:92`, `:489`, `:498` and
`Asymptotic/PublicKey.lean:1059`; [PS10, Theorems 87.3 and 104.4]. This is a useful generic
API on its actual domain, not an RSA instantiation.

## Exact CPA bridge: statement-gated, proof still missing

`BitPublicKeyScheme.exists_padBound` supplies L, its ciphertext padding bound and
`1 ≤ L.eval n`; then `hS.padded_cpa L hL hmsg` supplies the CPA claim for
`S.padded L hL hmsg`. `TrapdoorCollection.tdpBitScheme_padded_cpa` already composes this
route. These remain supporting APIs; the catalog theorem should start from its assumption
set and end at the chosen primitive.

`BitPublicKeyScheme.SingleBitSecure.padded_cpa` is an admission on the integration branch.
Gate06C is now closed at the frozen statement source; its admitted bridge still needs a fill before any claim of a completed exact CPA implication. The
many-message endpoint still needs its precise game and a checked lifting in that model.

## Concrete assumptions: index their actual current endpoints

| Assumption | Existing endpoint | Extra premises | Missing work before a generic CPA-PKE existence theorem |
|---|---|---|---|
| `RSAAssumption` | `(rsaTrapdoor H).OneWay`, via `rsaCollection_oneWay` and `rsaTrapdoor_oneWay` (`Candidates/RSA.lean:2206`, `:2221`) | `H : ArithmeticFP` (`Candidates/Arithmetic.lean:314`) | Goldreich–Levin padding needs a genuine length bridge; exact CPA then needs the Gate 06C bridge. |
| `FactoringAssumption` | `(rabinBlumTrapdoor H).OneWay` (`Candidates/Rabin.lean:3392`) | `ArithmeticFP`, `BlumDensity` remains a hypothesis | Same encoding-length issue and CPA bridge. The plain factoring collection is not itself a trapdoor-permutation conclusion. |
| `DDHAssumption (egGroupGen H G)` | `(elGamal H G).Secure` in `GroupPKScheme` (`Candidates/ElGamal.lean:2211`) | `ArithmeticFP`, `G : SafePrimeGen`, negligible full-length-exception bound `hbig` | Preserve the group-message security/correctness model; a conversion to another PKE record/security game is separate work. |

RSA's construction is `Candidates/RSA.lean:1493`; its concrete RSA root-extraction assumption
is `:105`/`:118`. The generic padding documentation explicitly states the cost:
`Asymptotic/HardCoreCollection.lean:85–91`. Generated RSA elements have width `2*max(n,2)`,
Rabin's width is `2*max(n,3)`; no current candidate satisfies the exact `PolyExpr` equality as
parameterized. The documented per-index-width/bounded-length version is not formalized.

A smaller proposed normalization route is now in `normalization-design.md`: run RSA at n+2
and Blum Rabin at n+3, so their widths become exact polynomials. Existing machine-level
parameter-change APIs and the existing `Negligible.comp_of_le` closure theorem are available.
Collection construction, one-wayness transport and candidate-home width readers remain missing;
the general negligibility theorem needs relocation to Foundations for the lower-layer use.
This is a source-level design, not a completed bridge or a new catalog tier.

**Do not declare a candidate-level theorem by adding that impossible premise.** A future
normalization or generalized padding construction must have a real public contract and proof.
Its statement/fill work is separate from the short Implications wrappers.

## Review and implementation checks

- Every final theorem has an explicit mathematical header, an accurate source docstring and
  all retained hypotheses. Use source-level proof terms through public APIs only.
- Show each witness's actual scheme and security model. Keep the paired correctness theorem
  when the source record does not contain it (GroupPKScheme).
- Check axiom dependencies of the entire composition. Distinguish existing admissions from
  proof completion, even if the new wrapper has no local sorry.
- Use an isolated PR worktree, precise imports, topic facade/root exports and serial module
  checks. No new host is needed for the generic pilot.

**Not yet clear to merge — proposed contents, no new Lean wrapper module checked yet.**
