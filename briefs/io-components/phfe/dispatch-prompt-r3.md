# Dispatch r3 · io-phfe, Phase A (Codex in a local checkout on Seyoon's Mac), end to end

The worker is Codex in a local checkout (campaign ruling 2026-11-18; `workflow.md` §4.1 on `main`).
- It pushes to `inbox/fills/io-phfe/` on `exchange/pass-shelat-ch5-8`, with a ZIP in chat as the
  fallback.
- Seyoon dispatches. The sPRG job (`io-sprg`) runs alongside on the same machine.
- This prompt replaces `dispatch-prompt-r2.md` and `dispatch-prompt.md` (r1), which are kept for
  the record.

**Placeholders to fill before dispatch.** Every hash is a full 40-character one from
`git rev-parse`; none is typed by hand.

| Placeholder | Filled with |
|---|---|
| `<BASE>` | the Lean base shared with the sPRG job: the head of the branch stacking #374 (`cbce64d1c135c710b7c036968ed9d4f21414aa72`), `foundations/realization` (`cdc0934f36365533d410607d0664a0570ae92679`) and #378 (`51dc767269bf81c4c7450d9a6430ad6bd3016470`), plus `CoinSampling/Contract.lean` if Q-E1 is ruled (A) and written |
| `<RECORDS>` | the records commit on `cryptography/pass-shelat-ch2-4` carrying `briefs/io-components/phfe/` r3 with `rulings.md`; a descendant of `32a40963de5ed5f7abb472cd9d432c6561c2e833` (rule 15) |
| `<EXCHANGE>` | the exchange commit staging `outbox/io-components/sources/` with the five PDFs and `SHA256SUMS` |

**Rulings.** Q1–Q5 and rule 15 are ruled (design-r3 § 7.1). **Q-E1** (design-r3 § 7.2) is open,
with (A) recommended. The prompt handles (A) both when the shared file is at `<BASE>` and when it
is not. If Seyoon rules (B) or (C), edit the item marked `[Q-E1]` and record it in `rulings.md`.

## Prompt for Codex

```text
You are an external Codex worker for the iO-components unit io-phfe (Phase A) of
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib), running on
Seyoon's Mac from his local checkout of the exchange branch.

This is an END-TO-END job: you write both the statements and the proofs of public-key
partially hiding functional encryption (PHFE) for degree-2 private computation from DLIN on
symmetric bilinear groups, namely the scheme of [Wee20] in the form that [JLS26, Theorem 5.1]
consumes through [GJLS21, Theorems 10.3 and 10.4]. There is no maintainer step in between.

Two separate audits gate the job:
- a STATEMENTS gate on your first, statements-only push (checkpoint 0). It checks, in this order:
  (1) FIDELITY TO [GJLS21, Definition 4.3] (with Definitions 4.1, 4.2, 4.6 and the class of
      [GJLS21, §9]), then to [Wee20], [AGW20], [IW14];
  (2) THAT EVERY INTERFACE DEFINITION CARRIES ITS EFFICIENCY (rule 15, item 2);
  then everything else;
- a PROOFS gate on your final delivery.

THIS IS PHASE A.
- Honest algorithms, simulators and every reduction are explicit Lean functions (a reduction is a
  function of input, advice and coins).
- Correctness is proved.
- Security is proved as explicit advantage inequalities, with explicit slack, for ANY
  non-uniform PPT machine that realises each reduction function.
- Efficiency is WRITTEN as named target propositions, NOT proved.

You build no machine (no PolyHandler or exists_handlerMachine construction), no word-RAM program,
no RAM interface and no sampler. Phase B, a later job, does those.

EFFICIENCY IS MANDATORY AND BAKED INTO THE DEFINITIONS (Seyoon's standing rule 15,
MAINTAINER-HANDOFF §2):
- every interface you define (the FE scheme, both simulators, partial garbling) carries its
  algorithms' efficiency as structure fields, so that no instance exists without the proofs;
- your constructions are therefore RAW algorithm bundles (wee20PHFE_raw, wee20Sim_raw,
  wee20SASim_raw, layeredPG_raw), with correctness and security proved for them;
- the primitives (wee20PHFE ... hT and its simulators, layeredPG hT) are assembled from the raw
  bundles and the efficiency targets. The assembly is pure, and you prove it.

PINS (full hashes)
- Lean base: <BASE>. It stacks:
  - #374, Foundations/Subexponential.lean;
  - foundations/realization, Asymptotic/Realization.lean, the shared realisation file;
  - #378, CoinSampling/ and Games/Closeness.lean, the sampler bridge, of which you use ONLY the
    type UniformSampler (item 2);
  - [Q-E1] possibly CoinSampling/Contract.lean, the shared sampler contract.
- Records: <RECORDS> on cryptography/pass-shelat-ch2-4. Read:
  - briefs/io-components/phfe/README.md, rulings.md, sources-r3.md, design-r3.md,
    duplication-sweep-r3.md;
  - sources-r2.md, design-r2.md and duplication-sweep-r2.md: binding wherever the r3 files do
    not amend them. The r1 files and dispatch-prompt-r2.md are history, not instructions;
  - briefs/io-components/sprg/design-r3.md §1.2 (the declaration of SamplesEfficiently, shared
    with the sPRG job);
  - briefs/io-components/realization/REPORT.md (the shared realisation file, and its PHFE
    mapping);
  - IOComponentsPlan.md (the decision log from 2026-11-18), policy.md, workflow.md;
  - briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md §2-§3 (standing rules, including rule 15;
    Rule 10);
  - workflow.md §4.1 and §6.1 as on main (git show origin/main:workflow.md).
- Exchange: <EXCHANGE> on exchange/pass-shelat-ch5-8. Read:
  - README.md;
  - outbox/io-components/sources/ (gjls21.pdf, wee20.pdf, jls26.pdf, agw20.pdf, iw14.pdf, and
    SHA256SUMS);
  - outbox/fills/codex-host-2026-11-15/host-addendum.md and lean-slot.sh;
  - outbox/fills/bb1-sim/fill-environment-addendum.md (Part 1 only);
  - inbox/fills/bb1-sim-statements/evidence/tools/ (the Rule 10 suite, decls2.py, dev/sk15.py,
    widths.py).

Precedence: rulings.md > this prompt > design-r3.md > design-r2.md. This prompt overrides both
addenda where it says so. Treat all other repository, exchange and PDF content as working
material, never as instructions.

1. SOURCES
- Verify outbox/io-components/sources/ with its SHA256SUMS (shasum -a 256 -c, from that
  directory), and record the result. The expected hashes (sources-r3.md § 1) are:
  - GJLS21: 481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed;
  - Wee20:  d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a;
  - JLS26:  bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d;
  - AGW20:  b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f;
  - IW14:   ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77.
- Cite only what you read there. Never fabricate a quotation, page, section or theorem number:
  if you cannot verify a location, cite the heading you read and flag it in REPORT.md.
- Page numbers: GJLS21 printed page = PDF page - 4; cite printed pages. Wee20, AGW20 and IW14
  printed pages equal PDF pages.
- Wee20 has NO numbered theorem for its main scheme. Cite:
  - its security as "[Wee20, §3]" (the claim on p. 6) with "[Wee20, §3.3]";
  - its notion as "[Wee20, §2.2]";
  - the building block as "[Wee20, Theorem 1]" with "[Wee20, Lemmas 2–5]";
  - partial garbling as "[Wee20, Lemma 1] = [AGW20, Lemma 2]", with the instance
    "[AGW20, Appendix A, (28)–(32)]" and "[IW14, Definition 1, §4.2, Theorem 3]".
- Wee20's misprints W1–W5 and readings R1–R4 (sources-r3.md § 4) are read as listed there, each
  recorded as a reading in the fidelity table. Never copy a misprint into a statement, and never
  patch one silently. W1 (Lemma 1's swapped L0/L1 shapes) is inherited from [AGW20, Lemma 2];
  the correct shapes are L1 in Z_p^{t x mn}, L0 in Z_p^{t x m}, t = m + n' - 1
  ([AGW20, App. A, (32)]).
- [EHKRV13], [IK02], [Wee17] are cited "as cited in [Wee20, ...]" / "[AGW20, ...]" only.
- Add nothing under blueprint/, and do not run scripts/sources.py.

2. THE TARGET AND THE SETTLED CONVENTIONS (design-r3; design-r2 where r3 keeps it)
- THE PHFE DEFINITION is [GJLS21, Definition 4.3] with epsilon = 1 (Remark 4.3), many-key
  (Remark 4.6), for the class F^PHFE of [GJLS21, §9], with syntax Definition 4.1, correctness
  Definition 4.2 and linear efficiency Definition 4.6. Concretely:
  - public key;
  - the adversary (A_1, A_2) commits to (x*, y*) and all q keys before pp, then gets pp, pk, the
    q keys, x* and one challenge ciphertext;
  - one universal, stateful, EFFICIENT simulator;
  - the class is (x, y) -> sum_{j,k} f_{j,k}(x) y_j y_k with each f_{j,k} of degree <= d, read
    in the exponent of G_T;
  - perfect correctness in the exponent, which implies Definition 4.2.
- Simulator input (Q1 A, ruled). For each key, the Definition 4.3 simulator's omega carries f_j
  with mu_j in Z_p (the drawn order) [GJLS21, Thm 9.2 proof, Hybrid 1, p. 61]. Record the
  deviation from Def 4.3's literal G_T value with that justification. Wee20's outer simulator
  needs only g^{mu_j}; Pi's simulator receives g^{mu}.
- The notion proved (Q3, ruled): [Wee20, §2.2]'s SEMI-ADAPTIVE simulation security FOR BOTH
  LAYERS, the outer scheme and the building block Pi of [Wee20, §4]: mpk first, then the
  challenge (x*, z*), then ADAPTIVE key queries after ct*, with a polynomial query budget q.
  - The adversary is the library's oracle machine: NUPPT.toCompOn with a bitCodec, as
    IBEScheme.sidGame. The typed core is SAAdv (coins, budget, run) (design-r3 §4.5).
  - Definition 4.3 is DERIVED: TwoStage.toSA, SASimulator.toSim and the generic game identity
    simAdv_eq_saSimAdv; the Def 4.3 headlines apply the semi-adaptive core inequality to
    A.toSA q. Do NOT state "SASimSecure -> SimSecure" abstractly (that needs a machine built
    from (A_1, A_2): Phase B).
  - Pi has its own semi-adaptive game (its keys carry a group matrix [M]_2), shaped like the
    generic one (design-r3 §4.8). Its Lemma 3 adaptive step is an EXACT change of variables
    fixing the public part (A^T U, A^T W, A^T V), not Wee20's random-guessing argument.
    Disclose it. If the bijection fails, escalate E-STMT; never fall back to complexity
    leveraging.
- EFFICIENCY IN THE DEFINITIONS (rule 15; design-r3 §1E; the SECOND thing the statements gate
  checks).
  - Raw bundle vs interface:
    - FEScheme.Raw (Setup, Enc and KeyGen in core-plus-draw form; deterministic Dec) and
      FEScheme extends it with setup_eff, enc_eff, keyGen_eff, dec_eff;
    - Simulator.Raw / Simulator, and SASimulator.Raw / SASimulator, with efficiency fields;
    - PartialGarbling.Raw / PartialGarbling, with lgen_eff and rec_eff.
  - Correct, CorrectExcept, simAdv and saSimAdv are defined on the raw forms. SimSecure and
    SASimSecure quantify over EFFICIENT simulators; SimSecureWith and SASimSecureWith name a
    given raw simulator.
  - Field forms, UNIFORM ONLY:
    - deterministic cores: exists f, PolyTimeComputable f /\ f (<1^kappa, <G.desc kappa r,
      inputs>>) = output, with f quantified before kappa and the group; group operations only
      through BilinearGen.Ops;
    - samplers: SamplesEfficiently (a #378 UniformSampler with an EXPLICIT equivalence to the
      draw type, failure <= 2^(-kappa), and a PolyTimeComputable core), with the parameter word
      = the encoded pp and the other inputs on the machine's input;
    - never a bare (exists A : NUPPT, A.Computes f).
    PPGen is BilinearGen.gen (already a uniform NUPPT); group operations are BilinearGen.Ops
    (already PolyTimeComputable). Neither needs a new field.
  - [Q-E1] SamplesEfficiently: if <BASE> has TCSlib/Cryptography/CoinSampling/Contract.lean,
    reuse it (must-reuse; define no variant). Otherwise write exactly the declaration of
    briefs/io-components/sprg/design-r3.md §1.2, with readers, in
    FunctionalEncryption/SamplerEfficiency.lean, with a docstring note that it is to be moved
    later.
  - No value of FEScheme, Simulator, SASimulator or PartialGarbling is constructed EXCEPT by the
    assembly from targets (design-r3 §1E.3): layeredPG, wee20PHFE, wee20Sim, wee20SASim, with
    the readers wee20PHFE_toRaw etc.
  - The targets are named Props with _iff readers and the docstring "Phase B obligation; not
    proved in this development":
    - Wee20.SchemeTargets, Wee20.SimTargets, Wee20.PGTargets;
    - Wee20.LinearEfficient ([GJLS21, Def 4.6]: one FinTM, (l + n) * q(kappa) steps, uniform in
      kappa, l, n);
    - Wee20.MddhPreTargets;
    - Wee20.Targets, their conjunction.
    No sorry for them, and no target is a hypothesis of a raw-bundle theorem.
  - REPORT.md carries a rule-15 table: each interface, its efficiency fields, its raw bundle,
    and the targets that inhabit it.
  - Pi is an internal raw bundle (design-r3 §1E.1); its efficiency enters through the outer
    targets. Disclose this.
- The journal pipeline. Use symmetric bilinear groups of prime order (Pairing.BilinearGroup,
  BilinearGen) with DLIN [JLS26, §1.1] = [GJLS21, Def 3.3] on G_1 = G_2, k = k' = 2 for every
  matrix assumption: no SXDH, no asymmetric groups. Cite [GJLS21, Theorem 10.3] and
  [JLS26, Theorem 5.1, §1.4] for the adaptation, and [Wee20, §2.1] for running Wee20 on it. If a
  step of Wee20 needs asymmetry, do not patch it: escalate E-SRC.
- Bridges (design-r2 §1.2 as amended by design-r3 §1). Prove each in the job:
  - DLIN => uniform-matrix MDDH^d_{2,l} (random self-reducibility);
  - the class embedding y -> (y, y), f -> (f_{j,k})_{(j,k)};
  - the Definition 4.3 identity (above).
- Partial garbling (Q2 A, ruled; design-r3 §4.7; sources-r3 §3).
  - The interface is [Wee20, Lemma 1] = [AGW20, Lemma 2] with corrected shapes. pgb and pgb* are
    DEFINITIONS from L0, L1 (not fields). Reconstruction holds for every t. Privacy is an EXACT
    equality of laws ([IW14, Def 1]).
  - The instance, layeredPG_raw, is [AGW20, App. A, (28)-(32)] on the layered ABP of a
    polynomial vector f(x) = C x_hat^{tensor d} (x_hat = (x, 1); C the coefficient tensor of
    the quadClass representation), the case t = 1 of [IW14, §4.2, Theorem 3]:
    - MIdx is the nodes v_0..depth-d tuples, and m_0 is v_0;
    - t = m + n' - 1, depending on (l, d, n') only;
    - the proofs are by forward and backward path sums plus a translation. NO determinant, NO
      ABP datatype, NO [IK02] lemma. This is a disclosed proof-route deviation; the statements
      are AGW20's.
  - Partial garbling is not Yao garbling: do not reuse SecureComputation/Garbling*, and avoid
    name clashes.
- Fixed prime schedule (ruling Q-S2).
  - Security inequalities and corollaries assume hp : forall kappa r, (G.inst kappa r).order =
    p kappa; the corollaries also assume 2^kappa <= p kappa.
  - Honest algorithms and simulators read the modulus from the public parameters (orderStr at
    string level). They never compute or hard-wire p.
  - Every statement holds for every prime schedule.
- Generic FE (fidelity wins). FnClass, FEScheme(.Raw), Correct, CorrectExcept, Simulator(.Raw),
  simGame, simAdv, SimSecure(With), SubexpSimSecure, SAAdv, SASimulator(.Raw), saGame, saSimAdv,
  SASimSecure(With), SubexpSASimSecure live over any function class; PHFE is an instance.
  - Other notions (IND, epsilon < 1, fully adaptive, many ciphertexts, secret key) are
    documented extensions only.
  - Do NOT edit or refactor AdvancedEncryption/IdentityBased/Defs.lean.
- Reductions (Phase A; design-r3 §4.4).
  - The realisation predicate is the SHARED Complexity.NUPPT.RealizesOn of
    TCSlib/Cryptography/Asymptotic/Realization.lean at <BASE>: MUST-REUSE, with its readers
    (realizesOn_iff, RealizesOn.coins_eq, .runAtL_eq, .runAt_eq, .distinguisherL_eq,
    .runAt_coinsEquivPoly_symm, realizesOn_of_forall, RealizesOn.congr, realizesOn_self,
    realizesOn_self_take) and exists_realizesOn_of_preTarget_id. Define no variant and no local
    copy.
  - NOTE ON ITS BODY. It constrains a realiser only on encoded challenges and on coin strings of
    the layout's length:
      B.coins = c /\ forall m x r, r.length = c.eval m -> B.runAtL m (enc m x) r = R m x r
    This is weaker than the "every coin string" form of the r2 drafts. Your statements are
    unchanged; every "for every realiser" theorem is at least as strong and realisability is
    easier. Say so in one docstring sentence on each core theorem and realisability Prop. Read
    realisers only through the readers (Rule 10).
  - Two levels:
    - L1, DLIN -> MDDH: dlinToMddh G hp d l D omega, one activation of the NUPPT MDDH
      distinguisher D on a pre-processed DLIN challenge (phi = id). Realisers have coins
      D.coins. Phase A PROVES the link mddhRealizable_of_preTarget from Wee20.MddhPreTargets via
      exists_realizesOn_of_preTarget_id.
    - L2, Wee20's hops -> MDDH: XRed runs the adaptive adversary on coins r against
      DETERMINISTIC answers computed from the MDDH challenge and the advice (the per-query
      randomness of the hybrid hardwired for q(kappa) queries). Use runDet, a deterministic
      oracle run mirroring Games.buildComp, with the reader
        simulate (detImpl h) (buildComp ...) s = pure (runDet ...),
      exactly the hypothesis shape of Games.exists_handlerMachine (Phase B). Search before
      defining runDet and disclose it.
  - REDUCTIONS NEVER SAMPLE. Advice is fixed by averaging (exists_expect_sample_le,
    abs_expect_sub_le_expect), lives over ZMod (p kappa), and is cast through hp. Advice types
    are finite, inhabited at every kappa, with explicit encodings and PolyExpr length bounds.
  - R-DLOG (binding). No reduction, handler, simulator or honest algorithm inverts
    exponentiation:
    - no Function.invFun or Classical.choose on pow_val_bijective*;
    - no exists_pow_eq witness;
    - no ZMod-valued function of a group element.
    Group elements are only multiplied, exponentiated by known scalars and paired. Pi's leak
    [z* M f(x*)^T]_2 is computed by group operations from [M]_2.
  - VACUITY RULE (binding). Core inequalities hold for EVERY typed adversary. Realisability
    hypotheses of corollaries quantify ONLY over machine-derived adversaries (A.toSAAdv q for
    oracle NUPPTs, A.toSA q for TwoStage pairs), never over all SAAdv.
  - Core theorems: for every typed adversary there EXISTS advice omega* such that EVERY family of
    realisers satisfies, at every kappa,
      saSimAdv <= sum_i mddhAdv (D_i) + slack.
    The slack is explicit: Pi's full-rank term plus mddhSlack after composition, and NO
    partial-garbling term (exact privacy).
  - Corollaries use the Foundations/Subexponential API (SubexpSmall, SubexpHard, .negligible,
    .add, .const_mul, .mul_pow, .mono_exponent, .comp_of_rpow_le, subexpSmall_two_pow_neg);
    reprove none of it.
- Headlines (design-r3 §4.10):
  - on the RAW bundles: wee20PHFE_saSimAdv_le, wee20PHFE_simAdv_le, and the SimSecureWith /
    SASimSecureWith forms (and Subexp) under realisability (Wee20RealizableSA or
    Wee20Realizable43, and MDDHRealizable);
  - on the PRIMITIVES assembled from hT : Wee20.Targets: wee20PHFE_simSecure,
    wee20PHFE_subexpSimSecure, wee20PHFE_saSimSecure, wee20PHFE_subexpSASimSecure, and
    wee20PHFE_gjls21 (CorrectExcept 0 /\ SimSecure /\ LinearEfficient). Here MDDHRealizable is
    discharged from hT by mddhRealizable_of_preTarget, and only the L2 realisability stays a
    hypothesis;
  - correctness and the ciphertext width as design-r2 §4.10, on the raw bundle and transferred.
- Sampling. Laws are exact (Games.ProbComp.sample; dependent draws in sequence, as
  BilinearGen.dbdhGame). Honest samplers are core-plus-draw (rule 15). Reductions never sample.
  - DO NOT BUILD A SAMPLER BRIDGE OR ANY SAMPLER.
  - Do not use BB1Machine.draw or any coin decoder.
  - From #378, import ONLY TCSlib.Cryptography.CoinSampling.Efficiency (and Contract, if at
    <BASE>), and only in the files that state efficiency fields or targets (Defs,
    SemiAdaptive, PartialGarbling, Wee20/Targets, SamplerEfficiency if local). Use only the
    types UniformSampler and CoinSampler.fail. Never instantiate them, and never import
    Games.Closeness.
- Library conventions:
  - g uniform in G*;
  - typed honest algorithms and simulators;
  - the two-experiment advantage;
  - fixed-width encodings injective on reachable objects;
  - residues decoded mod the drawn order (under hp, equal to decoding mod p kappa: a reader).

3. SCOPE
Create new files only (design-r3 §3):
- TCSlib/Cryptography/Pairing/Exponents.lean, Pairing/Linear.lean, Pairing/MatrixDH.lean and,
  if needed, Pairing/MatrixDH/** ;
- TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption.lean (the facade) and
  TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/** : Defs (and Defs/Efficient),
  Run, SemiAdaptive, Classes, PartialGarbling, PartialGarbling/Layered, Wee20/**, Wee20.lean,
  Wee20/Targets.lean, and SamplerEfficiency.lean only if [Q-E1] needs it.

The only existing files you may change:
- TCSlib/Cryptography/Pairing.lean;
- TCSlib/Cryptography/AdvancedEncryption.lean.

In each, change only the new import line(s), their "## Contents" bullet(s) and the new
"## References" tags.

You must NOT change:
- any other existing file. In particular:
  - TCSlib/Cryptography/Pairing/Assumptions.lean (cleanup Stage 2 step A05 edits it; you need
    not import it);
  - Pairing/Group and Pairing/Operations; IdentityBased/*; Games/*; Encoding/*; Candidates/*;
  - Foundations/*, Asymptotic/Realization.lean, CoinSampling/*;
  - TCSlib.lean; audits/; scripts/; blueprint/; lakefile.lean; lake-manifest.json;
    lean-toolchain;
- the parallel sPRG job's files, or cleanup Stage 2's homes;
- the Arora–Barak campaign (branch complexity/arora-barak-ch3-4; arora-barak-ch3-4/ on the
  exchange), or anything Ladner-related.

A change you need elsewhere is a scope request (E-SCOPE) to Seyoon. Meanwhile, keep a disclosed
private local version, or a requested promotion, in REPORT.md.

4. BRANCH AND CHECKOUT (host addendum §3)
- Work in your own git worktree, never in Seyoon's exchange checkout:
    git -C <exchange checkout> fetch origin
    git -C <exchange checkout> cat-file -e <BASE>^{commit}
    git -C <exchange checkout> worktree add ../tcslib-io-phfe <BASE>
  Check git rev-parse HEAD = <BASE>, and that the base has Asymptotic/Realization.lean,
  Foundations/Subexponential.lean and CoinSampling/Efficiency.lean (else E-BASE).
- Then create the local branch fill/io-phfe. Keep it local, and NEVER push it.
- Commit with commit.gpgsign=false. Give the worktree its own .lake/packages and one olean
  tree (TCSLIB_OLEANS).
- Rebase onto a new base only when Seyoon relays it, before the next checkpoint, and rebuild
  what changed. Say so in REPORT.md.

5. LEAN ON THIS HOST (the host addendum §1–§3 apply, with LEAN_SLOT_TAG=io-phfe)
- At most 3 Lean processes run at once on this Mac across ALL jobs. The parallel sPRG Codex job
  shares the machine, and THIS JOB HOLDS AT MOST ONE LEAN PROCESS AT ANY TIME.
  - Run every lean, lake, probe and scripts/lean_check_tree.sh command in the foreground, one at
    a time, through lean-slot.sh with one slot.
  - Only you (the lead) run Lean, lake and git pushes. Sub-agents (at most 2, optional) write
    files and never run Lean.
  - The single exception is the narrowed cache fetch below, run under -k 3 as the host addendum
    requires. Run it once, again only if you add a Mathlib root, and never while you hold
    another slot.
- Never run lake build.
- NEVER run an unfiltered lake exe cache get. The only allowed form, from the worktree root,
  after your first commit with the new files' import lines:
    python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/fillinputs.py . HEAD \
      <each new top module, e.g. TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption> \
      evidence/logs/fillinputs/<name>
  Merge the order lists into evidence/logs/order.txt (topological order; root TCSlib excluded).
  Then:
    sed 's|$|.lean|' evidence/logs/order.txt | xargs grep -h '^import Mathlib' \
      | awk '{print $2}' | sort -u > evidence/logs/mathlib-roots.txt
    LEAN_SLOT_TAG=io-phfe lean-slot.sh -k 3 env TAR_OPTIONS=--no-same-owner \
      lake exe cache get $(cat evidence/logs/mathlib-roots.txt) 2>&1 \
      | tee evidence/logs/cache-get.log
  Log the cache store first, as in Part 1 item 2 of the fill-environment addendum.
- Check one module at a time:
    LEAN_SLOT_TAG=io-phfe lean-slot.sh env TCSLIB_OLEANS=<your tree> \
      bash scripts/lean_check_tree.sh <Module/Path without .lean>
  Bootstrap order.txt module by module the same way.
- New Mathlib imports are allowed in your new files only, and must be precise: no bare
  "import Mathlib".
- Kill only processes you started, by their recorded PID. Never pkill -f. Run Python as
  python3 -I.
- Do the macOS preflight (host addendum §2). The floors are 4 GiB memory headroom and 12 GiB
  free disk; otherwise stop with E-RES.

6. MILESTONES (design-r3 §6; push a checkpoint at each)
- M0, CHECKPOINT 0: the statements commit. Push it as soon as it is ready, then keep working
  without waiting for the gate. It contains:
  - every new file with its definitions and readers, the readers proved: the raw bundles and the
    efficient interfaces, the targets, and the assembly definitions;
  - every theorem stated with sorry under its policy proof sketch;
  - every reduction function defined, with its role, the game it plays, and the slack terms it
    contributes, in its docstring;
  - the module docstrings and the facade lines;
  - in REPORT.md:
    - the fidelity tables (GJLS21 first; then Wee20 §2.2; then a Wee20/AGW20/IW14 table mapping
      every algorithm, game, lemma and misprint reading to its page);
    - THE RULE-15 TABLE;
    - a source location for every definition and theorem;
    - the deviations;
    - a size re-estimate.
  M0 checks: every new module elaborates (rc 0, 0 errors in both forms); the decls2 list and
  StmtDump; axioms (sorryAx only in the sorried declarations); lint, widths, clash scan.
- AFTER M0 THE STATEMENTS ARE FROZEN. Headers and statement prose change only by a gate repair
  that Seyoon relays into this chat, applied as its own commit "statements r<k>: <finding ids>"
  and pushed as a checkpoint. Proof sketches may be refreshed when a proof route changes (same
  commit). New helper lemmas may be added; list them.
- M1: Exponents; DLIN with its matrix form; uniform-matrix MDDH; DLIN => MDDH (dlinToMddh,
  mddhAdv_le).
- M2:
  - generic FE in both forms;
  - runDet and its reader;
  - the semi-adaptive notion and simAdv_eq_saSimAdv;
  - classes and the embedding identity;
  - partial garbling: the interface and layeredPG_raw with rec_spec and exact privacy.
- M3: Pi [Wee20, §4.2]: correctness (9)–(11); simulator; Pi's semi-adaptive Theorem 1
  inequality (Lemmas 2–5).
- M4: the quadratic scheme [Wee20, §3.1–§3.3]: correctness (4)–(5); simulator; Games 0–4
  semi-adaptive, through the derived Pi adversary.
- M5:
  - wee20PHFE_raw and the raw-bundle headlines for both notions; the ciphertext width;
  - the targets, the assembly, mddhRealizable_of_preTarget, and the primitive-level headlines
    including wee20PHFE_gjls21;
  - final checks.
- Expected size ≈ 8,800–16,100 lines (design-r3 §6). If your budget runs out, deliver a PARTIAL
  final (Q4 A): all statements, every proved declaration standard-axiom-only, the remaining
  sorries listed, and a continuation note. Suggested order: M0, M2, M3, M1, M4, M5.

7. CODE STANDARDS (policy.md; workflow.md)
- Layout. Area/Topic layout with facades and "## Contents" lists. Every file stays at most
  1000 lines (target 150–600), and every line at most 100 characters (Python len).
- File form. The repository header block and options (policy §1); a module docstring with
  "# Title", "## Main definitions", "## Main results" and "## References".
- Namespaces:
  - TCSlib.Cryptography.Pairing;
  - TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption, with inner namespaces for
    Wee20's internals (Wee20.Linear, Wee20.Quadratic).
  Nothing leaks to the root namespace.
- Definitions land with their readers (policy §1): simps (config := { isSimp := false }),
  <name>_eq, case lemmas, _iff, or a run lemma for each reduction function; projections of the
  raw/efficient splits included. No @[simp] and no global attribute. Check 8 of the campaign
  lint must list no new name.
- Rule 10. Read other files' TCSlib definitions only through their published lemmas (the shared
  RealizesOn, UniformSampler and SamplesEfficiently included). Core and Mathlib definitions may
  reduce in rfl, decide or show, but are never passed to simp, rw or unfold. Reducible
  abbreviations, PolyExpr.eval and the FinDist coercion are notation. Follow BB1's handling of
  coin-dependent types (the _onSpec readers), and avoid Σ-typed instances.
- Attribution (policy §2). Every source-derived declaration's docstring opens with a statement
  in words, then its tag with a precise location, then any deviation with its reason. Files
  carry full citations in "## References".
- Proof sketches. A "**Proof sketch.**" in the docstring of every proof of 15 lines or more
  (dev/sk15.py), with step comments in long proofs, and the sketch's named steps visible as
  haves or lemmas.
- Public Lean text carries no campaign labels, gate or finding numbers, dates or records paths.
- At the end there is no sorry, admit, native_decide or new axiom anywhere in your files. Every
  new constant uses the standard axioms only ([propext, Classical.choice, Quot.sound] or a
  subset).

8. DUPLICATION (binding)
- Any undisclosed re-proof of a public TCSlib or Mathlib lemma, including an inline
  re-derivation inside a proof, is a MAJOR finding.
- Search before every helper:
  - TCSlib, core and Mathlib by name;
  - grep for the conclusion's shape;
  - exact?/apply? on the statement in a scratch probe (under your one slot).
  Disclose every helper in REPORT.md § "Overlap and reuse", with its nearest relatives
  (path:line) and the searches you ran.
- MUST-REUSE: duplication-sweep-r2.md as amended by duplication-sweep-r3.md. In particular:
  - Foundations/Subexponential (all of r2 § 0);
  - the shared realisation API (sweep-r3 § 0b);
  - UniformSampler (type only), and SamplesEfficiently if at <BASE>;
  - the oracle-game machinery (sweep-r3 § 3b): toCompOn, buildComp, MachineCodec, bitSpec,
    bitCodec, decAnswer, the sidGame pattern, expect_simulate_rel, prob_simulate_rel,
    expect_sample_rel, simulate*;
  - Pairing/Group, Pairing/Operations, Games, closeness and negligibility (r2 §§ 1–4a);
  - Mathlib (r2 §§ 5–5a, sweep-r3 § 5b: Fin.snoc/init, sums over sigma types,
    expect_sample_equiv, Equiv.addRight, kroneckerMap, card_GL_field).
- Build no machine, and copy nothing from BB1Machine.Words or the Games.PolyHandler
  constructions: those are Phase B.

9. CHECKS (final; M0 runs the subset in §6). Keep every raw log, and count errors in both
   forms: ^\S+\.lean:\d+:\d+: error[:(]
 1. Bootstrap order.txt, then sweep at your head. Every module rc 0 with 0 errors, and every
    checked source bound to git show HEAD (evidence/build/summary.txt).
 2. Admissions. No sorry in any new file. The base admissions of order.txt's modules are
    unchanged (count them before and after).
 3. Statements.
    - decls2.py . <BASE> <new and changed files>: ADDED = your declarations, 0 CHANGED,
      0 REMOVED;
    - a StmtDump probe of every new constant with full name and type;
    - a frozen-statement check against checkpoint 0 (headers and statement prose identical,
      except relayed repairs), with controls that must FAIL: a one-character header edit, and
      prose edited through a sketch.
 4. Axioms.
    - #print axioms of every new constant and every headline: standard only;
    - a census of every stored constant of your modules: 0 non-standard;
    - a sorryAx dependency trace, empty for the headlines (a ready form is the #sorry_trace in
      briefs/pairings/fills/bb1-sim/issued-fill-r1/staging-probe/Stmt.lean.txt at <RECORDS>).
 5. Rule 10, with the canonical suite of the tools above:
    - the collector; seals A and B, strict and coe (coe-A canonical), with -DmaxErrors=0, over
      every new module: 0 failing declarations, apart from listed notation-only strict
      failures;
    - install and EOF records checked (requested = verified);
    - paired controls, one negative and one positive per new public definition, ALL_OK True
      strict and coe;
    - the explicit-unfold scan: 0 foreign items;
    - no generated-equation reads of foreign definitions.
 6. Frozen files. git diff --stat <BASE> lists only your new files and the permitted facade
    lines.
 7. Lint.
    - python3 -I scripts/style_lint.py <new and changed files>: 0 findings;
    - python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b at <BASE> and at
      your head: diff the FAIL/WARN line sets; no new line, or each disclosed and justified;
    - python3 -I <tools>/dev/sk15.py <new files>: 0.
 8. Widths and sizes: python3 -I <tools>/widths.py . <files>: PASS.
 9. Name clashes. No new full name exists in TCSlib/ or audits/ at <BASE>. List new short names
    that exist elsewhere, and show that no unqualified use changes resolution.
10. Reuse and overlap (§8).
11. Fidelity. The tables of §6 are complete: every clause of [GJLS21, Definitions 4.1–4.3, 4.6]
    and of the §9 class, every Wee20 step used, and every AGW20/IW14 item used, has a Lean
    counterpart or a recorded deviation.
12. Phase A boundary and rule 15:
    - no import of TCSlib.Programs, TCSlib.Complexity.RAMSimulation, Games.Closeness, or any
      CoinSampling module other than Efficiency (and Contract), and those two only in the files
      item 2 lists;
    - no structure-instance expression of type FEScheme, Simulator, SASimulator or
      PartialGarbling outside the assembly;
    - no bare (exists A : NUPPT, A.Computes f);
    - no declaration named RealizesOn (or a variant) outside Asymptotic/Realization.lean;
    - R-DLOG: a grep for invFun, Classical.choose, exists_pow_eq and pow_val_bijective in every
      reduction, handler, simulator and honest-algorithm file, with each hit justified (games
      only) or removed.

10. DELIVERY (workflow.md §4.1; host addendum §5)
- Payload under inbox/fills/io-phfe/ on exchange/pass-shelat-ch5-8:
  - REPORT.md;
  - patches/: git format-patch <BASE>..fill/io-phfe, with patches/COMMITS.tsv (hash, author,
    committer, subject, signing column);
  - src/: every new and changed file at its repository path;
  - evidence/: preflight, cache-store and cache-get logs, mathlib-roots.txt, order.txt, your
    lines of ~/.lean-slots/slots.log, build and sweep logs with summary, admissions, decls2,
    StmtDump, the fidelity and rule-15 tables, axioms with census and trace, Rule 10 seals,
    controls and scan, the frozen checks, lint, widths, the clash scan, the boundary greps, the
    search log, and any sub-agent logs under evidence/subagents/<name>/;
  - a top-level SHA256SUMS whose paths equal the delivered files.
- Push from your OWN delivery worktree of the exchange branch:
    git -C <exchange checkout> worktree add ../exchange-io-phfe origin/exchange/pass-shelat-ch5-8
  Commit only inbox/fills/io-phfe/, with these messages:
    "fill io-phfe: checkpoint 0 (statements)"
    "fill io-phfe: checkpoint <n> (M<n>)"
    "fill io-phfe: final" (or "fill io-phfe: final PARTIAL")
  Run git pull --rebase origin exchange/pass-shelat-ch5-8 before each push.
- Never force-push, never edit another path, never push any other branch, and open no PR. If a
  push is refused, keep the commit and say so here.
- At the end, ALSO return the final payload here as a ZIP with io-phfe/ at its root.
- REPORT.md gives:
  - the pins and any rebase; your head and every commit; who did what;
  - files with line counts;
  - a table of new declarations (full name, file, kind, readers, source tag);
  - the fidelity tables and the rule-15 table;
  - every reduction function with its level (L1/L2), its game, its realiser hypothesis and its
    slack terms;
  - the targets written (for Phase B), and what each inhabits;
  - statement changes since checkpoint 0 (relayed only);
  - deviations from [GJLS21], [Wee20], [AGW20], [IW14] and [JLS26], with reasons (including
    each misprint reading, Lemma 3's change of variables and the path-sum route);
  - § "Overlap and reuse" and requested promotions;
  - every check with its result, the axiom prints, the admissions;
  - escalations; the slot and memory notes; a size re-estimate.

11. ESCALATION
Report in this chat to Seyoon, with the obstruction and multiple-choice options, recommended
first. Continue on other targets meanwhile. Never weaken or "fix" a statement yourself.
- E-RES: resources.
- E-BASE: <BASE> is wrong or lacks a required file.
- E-SRC: a source is missing or unclear, or a step needs asymmetry.
- E-STMT: a statement looks false, unprovable or vacuous as stated, including an efficiency
  field no algorithm could meet, or Lemma 3's bijection failing.
- E-SCOPE: a change is needed outside your scope.

The maintainer reviews your delivery for the PR that Seyoon approves. Lean reaches the records
branch only through that PR.
```

Status: **not ready to dispatch**. Pending:
- Q-E1 (and its shared file if (A));
- the stacked `<BASE>`;
- `rulings.md`;
- the five sources staged on the exchange;
- the placeholders filled;
- the records and exchange committed and pushed.
