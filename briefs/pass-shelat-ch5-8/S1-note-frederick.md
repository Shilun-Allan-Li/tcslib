# S1 coordination note to Frederick Dehmel (draft for Seyoon to forward)

Drafted 2026-11-04 by the ch. 5–8 maintainer session. Status: **superseded, never sent** (2026-11-05: Frederick has left the branch, and the ch. 5–8 maintainer owns ch. 2–4; its requests became the maintainer's own work items, listed in `PassShelatChapter5-8Plan.md`, "Ch. 2–4 ownership"). Every name below
was resolved by a text-level scan (namespaces tracked) of the ch. 2–4 Lean at
`a7a3e0af0ecd261bd8643fcf96a2cfcbaa5757b7`, the last commit touching `TCSlib/Cryptography` or
`TCSlib/Complexity/Randomized`. A Lean import probe follows once the base builds.

---

Hi Frederick,

Seyoon is starting [PS10] chapters 5–8 (authentication, secure computation, composability,
randomness) as a separate line on top of your ch. 2–4 layer. It cites your definitions and almost
never your proofs: your open sorries block no ch. 5–8 statement. Seyoon has ruled on how the line
runs, and a few points need your agreement.

**1. A base that builds (the one blocking request).** By static reading, the head does not build
because of one public-name clash. `TCSlib.Cryptography.zipWith_xor_ofFn` is declared twice:
- `Asymptotic/Encryption.lean:288`, the truncated-pad form `(h : n ≤ L)`;
- `Asymptotic/HardCoreLoops.lean:144`, the equal-length form `a + b`.

The `Asymptotic` facade imports both files. Could you rename one, for example the
`HardCoreLoops` copy, or make one cite the other, in a commit we can stack on?

The second pair the planning notes reported is not a clash: `zipWith_xor_ofFn_eq_add` is declared
in `MultiMessage.lean:445` (`TCSlib.Cryptography`) and in `MultiMessageLemmas.lean:330`
(`TCSlib.Cryptography.MultiMsg`). That is the same statement twice, and consolidating it is up to
you.

**2. Records and PRs on your branch.** Seyoon ruled that the ch. 5–8 records live on
`cryptography/pass-shelat-ch2-4`:
- the records are pushed directly, and only touch `PassShelatChapter5-8Plan.md` and
  `briefs/pass-shelat-ch5-8/`;
- ch. 5–8 Lean arrives by PRs into your branch, in **new directories only**:
  `Cryptography/Games/`, `Authentication/`, `SecureComputation/`, `Composability/`,
  `Randomness/`, plus `LearningTheory/` for the PAC learning game.

Your files are not edited, except under point 4 and only with your agreement. Heads-up:
- Seyoon uploaded the notes as `Pass–Shelat.pdf` at the root of your branch;
- the repository is public, and the PDF will travel with any merge of your branch to `main`
  unless it is moved first.

**3. The frozen interface list.** These are the declarations ch. 5–8 statements will cite. We ask
that a change to any of them be announced to Seyoon, especially after your external gate, so the
ch. 5–8 statements can re-sync once. Full names, all in `TCSlib.Cryptography` unless written
out:

| Area | Declarations (file) |
|---|---|
| machines | `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`, `NUPPT.ofPolyTime` (`Complexity/Randomized/PPT.lean`); the closure calculus of `Complexity/Randomized/Closure.lean` |
| probability | `Negligible` (`Foundations/Negligible.lean`); `Ensemble`, `Ensemble.Indist`, `Ensemble.Samplable` (`Asymptotic/Ensembles.lean`); `StatClose` (`Asymptotic/Sampling.lean`) |
| one-wayness, PRGs | `FunFamily`, `FunFamily.StrongOneWay` (`Asymptotic/OneWay.lean`); `PRG`, `PRG.Secure` (`Asymptotic/Pseudorandom.lean`); `prg_expand` (`Asymptotic/HardCore.lean`) |
| PRFs, oracles | `PRF` (security is its field `pseudorandom`), `PRF.negligible_prfAdv`, `OracleEnsemble`, `OracleEnsemble.Indist`, `OracleMove`, `prfAdv_toOracleAdversary` (`Asymptotic/PRF.lean`) |
| encryption | `PrivateKeyScheme`, `PrivateKeyScheme.SingleMessageSecure`, `PrivateKeyScheme.MultiMessageSecure` (`Asymptotic/Encryption.lean`); the §3.9 scheme `prfScheme` and `prfScheme_multiMessageSecure` (`Asymptotic/MultiMessage.lean`); `PublicKeyScheme`, `BitPublicKeyScheme`, `tdpBitScheme`, `TrapdoorCollection.tdpBitScheme_singleBitSecure` (`Asymptotic/PublicKey.lean`) |
| collections | `Collection`, `Collection.HardCore`, `PermCollection`, `TrapdoorCollection` (`Asymptotic/Collections.lean`); `TrapdoorCollection.OneWay.glPad_hardCore` (`Asymptotic/HardCore.lean`) |
| candidates | `Candidates.ExpGroupGen`, `Candidates.DLAssumption` (`Candidates/DiscreteLog.lean`); `Candidates.ArithmeticFP` (`Candidates/Arithmetic.lean`) |
| interaction | `Strategy`, `View`, `Protocol` (`ZeroKnowledge/Interaction.lean`); `InteractiveProof` (`ZeroKnowledge/InteractiveProofs.lean`); `ZK`, `PerfectZK`, `PerfectZKAbort` (`ZeroKnowledge/Defs.lean`); `Commitment` (`ZeroKnowledge/Commitment.lean`) |

Anything ch. 5–8 finds missing in your layer is requested from you, or stated in our own file
with a note to fold it into yours later.

**4. The oracle-game layer (needs your agreement).** Chapters 5 and 7 need two experiment shapes:
- search games: MAC and signature forgery, collision finding;
- two-phase distinguishing games: CPA/CCA, non-malleability.

Both generalize your `OracleEnsemble`: a family of oracles, a game predicate over the
transcript, and a challenge phase. Seyoon ruled for a **common base**, with `OracleEnsemble`
restated over it, rather than a parallel layer that only cites yours. That touches
`Asymptotic/PRF.lean`, so we need your view on two points:
- (a) who restates `OracleEnsemble`: you, or us in your file with your review;
- (b) when: before or after your external gate.

The proposal: we draft the base in `Cryptography/Games/` with a proved bridge to the current
`OracleEnsemble.Indist`, so nothing of yours moves until you agree.

**5. `main` into your branch.** Prong D (Thm 180.1, PRGs derandomize BPP) states its result
against `main`'s `Randomized/Classes` (`InBPP`) and `ClassP/DTIME`. `Randomized/Classes` is not
on your branch, which forked from `main` on 2026-10-08. Is a merge of `main` into your branch
acceptable, and on what timing?
- By path, the only textual conflict is the facade `TCSlib/Complexity/Randomized.lean`.
- Your `Randomized/*` modules are in namespace `Complexity` and `main`'s are in `Randomized`, so
  no name clash is expected.
- Seyoon also ruled for one small bridge lemma (a `main` BPP verifier gives a `NUPPT` running
  it); unifying the two models is left for later.

**6. Landing order.** Do you plan for ch. 2–4 to reach `main` first, with ch. 5–8 stacked behind
it, or the other way round?

**7. Courtesy notes on `main`.**
- Shamir is already proved there, in your `SecretSharing/` files (2026-09-30), so ch. 5–8 does
  not redo it. PR [Shilun-Allan-Li/tcslib#183](https://github.com/Shilun-Allan-Li/tcslib/pull/183)
  adds [PS10] citations and deviation notes to the **docstrings** of `SecretSharing/Defs.lean`
  and `Shamir.lean`. Their code is byte-identical once comments are stripped.
- The same PR adds `InformationTheory/Entropy.lean` and `Extractors.lean`, including `EpsClose`,
  a distinguisher-form closeness of `FinDist`s that is equivalent to `statDist ≤ ε`. It parallels
  your sampler-based `StatClose`; a bridge between the two belongs in the eventual integration
  of ch. 2–4 with `main`.

Thanks. Point 1 is the only blocking request; the rest can wait for your convenience.
