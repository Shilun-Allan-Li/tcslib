# Claude fill · public-key CPA bridge (`padded_cpa`)

**Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`
(the merge of #284 and #285; later campaign commits are records only).
**Unit** `padded-cpa`. **Worker** Claude. **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `BitPublicKeyScheme.SingleBitSecure.padded_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean`: single-bit security of a
ch. 2–4 public-key scheme gives IND-CPA security of its padded fixed-length form
[PS10, Definition 171.5 and the claim after it, book pp. 171–172]. It is the CPA dependency of
the first catalog route. `TrapdoorCollection.tdpBitScheme_padded_cpa`
(`PublicKey/TrapdoorCPA.lean`) inherits it. The statement passed Gate 04. The shared machine
reduction T1 (`Games.exists_handlerMachine`) it needs was proved in #285.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/padded-cpa` at the exact
  issue base above. Record the base in `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/padded-cpa/` on
  `exchange/pass-shelat-ch5-8`. Include `REPORT.md`, `patches/` containing the whole
  `git format-patch` series from the issue base, `src/` with the owned paths, and `evidence/`.
  Use commit messages `fill padded-cpa: checkpoint N` and `fill padded-cpa: final`. Pull the
  exchange with rebase before pushing. Push only your delivery path; never force-push. Keep the
  proof branch local. Campaign changes land by a maintainer PR for Seyoon's approval.

## Target

The source declaration is frozen. This quote comes directly from the issue base (line 697).

```lean
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  sorry
```

Write `S' := S.padded L hL hmsg` below. Its messages are one bit (`msgLen = .const 1`), its
ciphertexts `L(n)` bits. The CPA game `S'.indGame .cpa A q b n` samples key-generation coins and
`A`'s coins and simulates `A` against `Dec` (always `⊥` under CPA) and `Challenge` (encrypts
`m_b` with fresh coins on the first query `⟨m₀, m₁⟩` and repeats the recorded ciphertext
afterwards).

## Published interfaces

Read every definition of another file through these published lemmas (policy §1, rule 10).
`OracleSecurity.lean`'s own definitions (`padCt`, `isPadded`, `padEncFun`, `padDecFun`,
`FixedLengthPKScheme`, `ofPadded`, `padded`, `inLens`, `outLens`, `indImpl`, `indCodec`,
`indGame`, `INDSecure`) may be unfolded, but prefer their readers.

| Interface | Provider |
|---|---|
| `padCt_eq`, `length_padCt`, `pairFstD_padCt`, `isPadded_padCt`, `padEncFun_eq`, `padEnc_coins`, `runAt_padEnc`, `BitPublicKeyScheme.padded_msgLen/_ctLen/_gen/_enc/_dec`, `inLens_zero/_one`, `outLens_zero/_one`, `indSpec_eq`, `indSpec_dom/_rng`, `indImpl_dec_cpa`, `indImpl_challenge_none(_onSpec)`, `indImpl_challenge_repeat(_onSpec)`, `indCodec_decodeMove`, `indCodec_encodeEntry`, `indCodec_timeout`, `indGame_eq`, `INDSecure_iff` | `Encryption/PublicKey/OracleSecurity.lean` (owned) |
| `BitPublicKeyScheme.singleBitSecure_iff`, `pkEncDist_eq` | `Encryption/PublicKey/EnsembleSecurity.lean` |
| `FixedLengthScheme.splitHalf` and its readers, `decOpen_cpa`, `decAnswer` | `Encryption/PrivateKey/OracleSecurity.lean` |
| `Games.exists_handlerMachine` (T1); `PolyHandler.input_eq`, `advInput_eq`, `result_eq`, `answer_of_pairDecode_eq_some/_none`, `answer_of_run_eq`, `impl_apply`, `bitSpecAt_eq`, `seedIn_eq` | `Games/Efficiency.lean` |
| `NUPPT.distinguisherL_eq` | `Asymptotic/Adversary.lean` |
| `NUPPT.runAt_eq`, `coinLen_eq`, `runAtL_eq_output_layout`, `exists_comp` and the closure combinators | `Complexity/Randomized/PPT.lean`, `NonUniform.lean`, `Closure.lean` |
| `NUPPT.toCompOn_eq`, `toCompOn_costBoundedBy`, `buildComp` case equations | `Games/Machines.lean` |
| `bitCodec_decodeMove`, `bitCodec_encodeEntry`, `bitCodec_timeout`, `decodeBitMove_*` | `Games/BitCodec.lean` |
| `simulate` equations and `OracleComp` pure/bind/query laws | `Games/Simulate.lean`, `Games/OracleComp.lean` |
| `accept_eq`, `advantage_eq`, `advantage_comm`, `prob_*`, `expect_*`, `sample_eq`, `dist_apply` | `Games/Advantage.lean`, `Games/Probability.lean` |
| `Bridge.distAdv_eq`, `acceptProb_eq`, `acceptGame_eq`, `prob_sample_pair`, `expect_sample_pair` | `Games/Bridges/Experiments.lean` |
| `abs_prob_sub_le_of_agree`, `prob_split`, identical-until-bad lemmas | `Games/Hopping.lean` |
| `Negligible.mono` and the negligible-function API | `Foundations/Negligible.lean` |
| `pairDecode_pairEncode`, `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairEncode`, `decodeFin_ofFn`, `padFin` readers | `Complexity/TuringMachine/Encoding.lean`, `Asymptotic/Adversary.lean` |

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryImpl`, `OracleSpec.add` and `indSpec` are
abbreviations; `PolyExpr.eval` is notation. If a needed equation has no published reader,
record it in `REPORT.md` and use the escalation route below; do not unfold the foreign
definition.

## Proof route and checkpoints

The sketch in the docstring is the route. The intended identity is exact, not only a bound:
for the distinguisher `D` built below, at every `n`,

`advantage (S'.indGame .cpa A q false n) (S'.indGame .cpa A q true n) =
  distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n)`.

Then `singleBitSecure_iff` gives a negligible right side, and `INDSecure_iff` closes the goal
with `ε` that right side.

1. **Eager challenge coins.** Under CPA the oracle state only records the challenge. Prove that
   simulating `S'.indImpl .cpa b n pk sk` from `none` has the same output distribution as first
   sampling encryption coins `re`, then simulating the deterministic oracle that answers the
   first challenge with `padFin _ (S'.enc.runAt n ⟨pk, m_b⟩ re)` (same state discipline). This is
   the lazy-to-eager step; prove it by induction on the computation, using the sampling and
   bind laws (`expect_bind`, `expect_sample`, `prob_bind`). Unused coins marginalize out. If a
   generic "sampling commutes with an independent simulation" lemma is missing, prove it as a
   helper (see Scope). Send checkpoint 1.
2. **First-challenge congruence.** For a deterministic challenge answer `g : messages → ciphertext`,
   the simulation's result depends on `g` only through `g (mm⋆)`, where `mm⋆` is the first
   challenge query (or not at all when there is none), and `mm⋆` does not depend on `g`. State it
   for the deterministic simulation of step 1 and prove it by induction. This replaces the
   informal "conditioning on `A`'s choice". Send checkpoint 2.
3. **The distinguisher `D` (T1).** Apply `Games.exists_handlerMachine` with `k = 2`, `din`/`dout`
   chosen so that `(fun i => (din i).eval n) = S'.inLens n`, `(fun i => (dout i).eval n) =
   S'.outLens n`, `dα = .const 1`, and a handler `H` with:
   - `seedLen = .const 0`; `advIn ⟨1^n, ⟨z, ω⟩⟩ = pairFstD z` (the public key of `z = ⟨pk, c⟩`);
   - a state that records whether a challenge was asked and its two message bits;
   - `Dec` answers all-`false` (as `indImpl_dec_cpa`); `Challenge ⟨m₀, m₁⟩` answers
     `padCt L(n) (pairSndD z)` at width `L(n)` and records `⟨m₀, m₁⟩` on the first query;
   - `out` returns `[a]` when the recorded pair is `(0, 1)`, `[!a]` when it is `(1, 0)`, and
     `[false]` when the pair is equal or no challenge was asked.

   All four functions must be polynomial-time; build them from the closure combinators and the
   pairing/padding lemmas already used in `OracleSecurity.lean` (`polyTimeComputable_isPadded`,
   `polyTimeComputable_padEncFun`). **Codec alignment** is a known obligation: T1 states its
   simulation with `bitCodec (fun i => (din i).eval n) …` while `indGame` uses
   `S'.indCodec n = bitCodec (S'.inLens n) (S'.outLens n) 1`. Choose `din`/`dout` so the two are
   definitionally equal if possible; otherwise transport along the propositional equality
   once, in a helper. Send checkpoint 3.
4. **The identity.** Fix `n`, key coins and `A`'s coins. By steps 1–2, game `b`'s output is `A`'s
   bit when the challenge is answered with `Enc(m⋆_b)`. By T1, `D`'s output on
   `⟨pk, Enc_pk(β)⟩` is `A`'s bit with the challenge answered by `Enc(β)`, post-processed by `out`.
   The pointwise case split on `mm⋆ ∈ {(0,1), (1,0), equal, none}` gives equal differences
   (for `(1, 0)` both sides are `A(Enc 1) − A(Enc 0)`). Transport coins: `S'.enc.Coins n` versus
   `S.enc.Coins n` (`padEnc_coins`), and `D`'s coins `φ (ω, r)` with the empty seed. Read
   `distAdv` with `Bridge.distAdv_eq` and `NUPPT.distinguisherL_eq`. Send checkpoint 4, then
   the final payload.

Check the edge cases: a run with no challenge query; repeated challenge queries (the repeat
returns the recorded ciphertext, which `H` reproduces because its answer depends only on `z`);
budget `q = 0`; and the timeout output `zeroBits 1`.

## Scope and proof discipline

- Own `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean`. Replace the one proof body
  and add helpers there. Helper modules are permitted under
  `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/` if they are generic (they must not
  import `OracleSecurity`, which would be a cycle) and imported precisely by it. Keep every file
  below 1000 lines. If the proof cannot fit without moving the theorem to a new module, stop and
  escalate with a proposal: moving a statement needs a ruling.
- You may edit the target's proof sketch to describe the proof actually delivered. Preserve the
  statement, every other declaration, the statement prose in docstrings and the global simp
  attributes. New helpers are public only when another file needs them; each public helper
  gets a docstring with its formula and a proof sketch when nontrivial (policy §3).
- Use published readers for other files' definitions in tactics and in term elaboration, including
  generated matchers and projections. For core and Mathlib use their equation lemmas in `simp`,
  `rw` and `unfold`.
- Do not edit `TrapdoorCPA.lean` or any other file outside the owned paths.
- **Escalation.** If the target appears false, or a required reader is missing with no clean
  route, write the exact failing obligation and the smallest proposed correction in `REPORT.md`
  and push a checkpoint. At a partial delivery identify each remaining admission and the
  checked frontier.

## Checks and report

- Bootstrap from `order.txt` and the narrow `roots.txt` using the environment addendum. Insert any
  new helper module before its consumer and recalculate roots if imports change. Check one module
  per `scripts/lean_check_tree.sh` invocation; one Lean process per olean tree.
- Recheck `PublicKey/OracleSecurity` and `PublicKey/TrapdoorCPA`, then sweep the rest of the
  supplied order (it includes every module downstream of the owned file). Compare `sorry` warnings
  with `base-sorries.txt`: the only change must be the removed `padded_cpa`.
- Print the axioms of `padded_cpa` (only `propext`, `Classical.choice`, `Quot.sound`) and of
  `TrapdoorCollection.tdpBitScheme_padded_cpa` (report exactly what it prints; it may inherit
  admissions from other providers).
- Collect foreign references from the elaborated new proofs, including generated matcher and
  projection helpers. Run an instance-aware seal of the touched declarations with the full
  candidate list, plus a control that passes before sealing and fails after sealing. Report the
  candidates, controls and any findings. Include the explicit-unfold scan and
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- Report the issue base, the target's status, exact changed files and sketch edits, new helper
  declarations, any reader requests, and the resource, cache, bootstrap, sweep, axioms, seals and
  lint evidence.

**Ready to dispatch**
