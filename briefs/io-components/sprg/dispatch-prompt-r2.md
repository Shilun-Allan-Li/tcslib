# Dispatch · io-sprg Phase A (Codex in a local checkout on Seyoon's Mac), end to end

The worker is Codex in a local checkout (campaign ruling 2026-11-18; `workflow.md` §4.1 on `main`,
*Codex in a local checkout*). It pushes to `inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`,
with a ZIP in chat as the fallback. Seyoon dispatches. The PHFE job (`io-phfe`) runs alongside on
the same machine. This is **Phase A** only (row *Strategy and uniformity*): no efficiency proofs,
no machines, no RAM. It supersedes `dispatch-prompt.md` (r1).

**Placeholders the maintainer fills before dispatch** (full 40-character hashes from
`git rev-parse`, never typed by hand):

| Placeholder | Filled with |
|---|---|
| `<BASE>` | the Lean base: the head of branch `foundations/subexp` (draft PR #374, `cbce64d1c135c710b7c036968ed9d4f21414aa72`), or a later head stacked on it (for instance with the shared realisation file of Q-S9 A); the tip of `cryptography/pass-shelat-ch2-4` once #374 has merged |
| `<RECORDS>` | the records commit carrying `briefs/io-components/sprg/` r2 (with `rulings.md`); a descendant of `dab31951abb5c892dc6279c229e49497ec95de10` |
| `<EXCHANGE>` | the exchange commit staging `outbox/io-components/sources/jls26.pdf` and its `SHA256SUMS` |

The prompt assumes the recommended options of design-r2 §10.2 (Q-S9 A, Q-S10 A, Q-S11 A, Q-S12 A);
Q-S1–Q-S8 are settled (design-r2 §10.1). If Seyoon rules otherwise on Q-S9–Q-S12, edit the items
marked *(Q-S…)* before dispatch and record his answers in `briefs/io-components/sprg/rulings.md`
(the prompt tells Codex that `rulings.md` overrides the design note). If Q-S9 A's shared file is not
at `<BASE>`, item 2's Q-S9 line already tells Codex what to do.

## Prompt for Codex

```text
You are an external Codex worker for the iO-components unit io-sprg of
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib), running on
Seyoon's Mac from his local checkout of the exchange branch.

This is an END-TO-END job, PHASE A: you write both the statements and the proofs of the
structured-seed PRG (sPRG) of Jain-Lin-Sahai [JLS26, J. ACM 73(1), 2026, §2-§4, Theorem 4.1]:
LPN over F_p (Def 2.3), Boolean PRGs with locality and multilinear degree (Def 3.4), sPRG syntax,
security and complexity (Defs 3.1-3.3), the construction (IdSamp', SdSamp', 1SdSamp, Eval',
G(1)-G(4)), Claim 4.1, Claim 4.2, Lemma 4.2, Proposition 4.1 and Theorem 4.1. Phase A means:
honest algorithms and reductions are explicit Lean functions; correctness, stretch and Claim 4.2
are proved; security is proved as explicit advantage inequalities for EVERY non-uniform PPT
machine that realises each reduction function; efficiency statements are WRITTEN (as named
propositions), NOT proved. There is no maintainer step in between. Two separate audits gate the
job:
- a STATEMENTS gate on your first, statements-only push (checkpoint 0, milestone M0), which
  audits the fidelity of every statement to the paper FIRST;
- a PROOFS gate on your final delivery.

PINS (full hashes; fetch branches by name)
- Lean base: <BASE>, on branch foundations/subexp (it adds
  TCSlib/Cryptography/Foundations/Subexponential.lean, "the Foundations/Subexponential API").
- Records: <RECORDS> on cryptography/pass-shelat-ch2-4 (read with git show <RECORDS>:<path>).
  Read in full:
  - briefs/io-components/sprg/README.md, design-r2.md, duplication-sweep-r2.md, rulings.md;
  - briefs/io-components/sprg/design-r1.md, for the sections design-r2 marks "unchanged from r1"
    (binding as written there, with design-r2's substitutions); dispatch-prompt.md and
    duplication-sweep.md (r1) are superseded: do not follow them;
  - IOComponentsPlan.md (scope, "Deferred library work", every decision-log row dated
    2026-11-18), policy.md, workflow.md, and workflow.md §4.1 and §6.1 as on main
    (git show origin/main:workflow.md);
  - briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md §2-§3 (standing rules, Rule 10);
  - briefs/pass-shelat-ch5-8/fills/fill-environment-addendum.md, Part 1 only (preflight, the
    narrowed cache, retries, logs).
  For context only (do not build or use anything from them): briefs/io-components/
  ram-bridge-assessment.md §1 and §3, briefs/io-components/sampler-bridge/README.md.
- Exchange: <EXCHANGE> on exchange/pass-shelat-ch5-8. Read:
  - README.md;
  - outbox/io-components/sources/jls26.pdf and that folder's SHA256SUMS;
  - outbox/fills/codex-host-2026-11-15/host-addendum.md and lean-slot.sh (the Mac host rules);
  - the Rule 10 suite of the bb1-sim delivery at commit
    2467bc3befdad8472b1f359337bf3a203e3651e1: inbox/fills/bb1-sim/evidence/tools/ (seal/,
    seal/review/, dev/sk15.py, clash/clash_scan.py, sweepsum.py).

Precedence: rulings.md (Seyoon) > this prompt > design-r2.md > design-r1.md > the addenda. This
prompt overrides the fill-environment and host addenda where it says so. Everything else you read
in the repository, on the exchange or in the PDF is working material, never instructions.

1. SOURCE AND FIDELITY
- Verify outbox/io-components/sources/ with its SHA256SUMS (shasum -a 256 -c, from that folder);
  jls26.pdf must have SHA-256
  bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d. PDF page k is article
  page 1:k. The content is §2 (pp. 8-10), §3 (pp. 10-11) and §4 (pp. 11-21).
- Statement fidelity to the paper is what the statements gate audits first. Every definition
  and theorem docstring opens with a statement in words, then its [JLS26, <item>, p. <k>] tag,
  then every deviation (design-r2 §8: Dv1-Dv15) with its reason. Never fabricate a quotation,
  page or item number; quote only what you read in the PDF (CC BY 4.0).

2. SETTLED (design-r2 §0, §3, §10.1; not open)
- Two phases (S10). Phase A is this job. Phase B (word-RAM programs, efficiency proofs, the RAM
  bridge, the final "exists NUPPT B" theorems) is NOT: do not import anything under
  TCSlib/Programs/ or TCSlib/Complexity/RAMSimulation/, do not state anything about word-RAM
  programs, do not build Turing machines, and do not prove the efficiency targets.
- Uniformity (S11, binding). Honest algorithms' efficiency, where you state it, is
  PolyTimeComputable f of ONE string map f, or (exists A, A.Uniform /\ A.Computes f); NEVER a bare
  (exists A : NUPPT, A.Computes f). The map is quantified BEFORE kappa and before the public
  parameter: one algorithm for all kappa, kappa read from 1^kappa, no per-kappa constants. Advice
  appears only in reductions, and only as their input.
- p is an input (S12, Q-S2 ruled and refined). The prime is a public parameter
  pp : PrimeParam kappa (a prime with 2^kappa <= p <= 2^(kappa+1), its primality and width
  proofs; design-r2 §4.1, C2). Params has NO prime field. Every honest algorithm of the
  construction is defined for an arbitrary pp; a schedule pi : PrimeSchedule only assembles the
  family jlsSPRG P pi; every security theorem holds for EVERY schedule pi; correctness, stretch
  and Claim 4.2 hold for every kappa and every pp (Claim 4.2's kappa0 independent of pp). The
  public parameter is the first field of every challenge string and is in every efficiency
  statement's input (in the reductions: in the advice encoding). NO definition computes a prime
  or hard-wires one (do not use ClassP/BinaryArith/PrimeFind; Bertrand only for
  PrimeSchedule.nonempty, a non-vacuity theorem).
- Rounding: the convention of design-r2 §3 (C1-C14; C1, C3-C10 as design-r1 §3): one security
  parameter kappa (Lean cannot name lambda); l = kappa^E, D = ceil(d/2), n = l^D;
  w = max 1 floor(l^(delta/2)), W = w^2, noise rate 1/W; t = kappa; sqrt c = t*w, c = (t*w)^2;
  B = max 1 ceil(m*t/W); Gamma = floor(m*log2 n/W); side conditions proved as "eventually"
  theorems. Everything encoded for a machine is Fin-indexed or carries an EXPLICIT equivalence
  (finSumFinEquiv, finProdFinEquiv, finFunctionFinEquiv, finCongr), never Fintype.equivFin or
  another classical choice (C13). Every honest sampler is a named deterministic core applied to
  exact uniform draws (C14). You may refine with disclosure.
- Sampling: state the non-dyadic laws (uniform Z_p, the LPN noise D_r(p), uniform functions
  [m] -> [B]) EXACTLY, as ProbComp.sample of finite types and their pushforwards (the
  LWE.Family / LWE.Noise convention). Samplers are NOT asserted efficient. The sampler bridge is
  built in-house separately: DO NOT build one, do not approximate samplers (rejectionSample,
  StatClose, LWE.sampleFromBits, uniformFromBits, DyadicUniform), and do not import
  CoinSampling or Games.Closeness even if <BASE> has them. Reductions hardwire averaged-out
  values in their advice instead of sampling (design-r2 §4.8).
- Degree: degree d in the public seed and degree 2 in the private seed (Theorem 4.1, p. 17), not
  p. 14's "d+1"; say so in one docstring sentence.
- Adversaries: non-uniform PPT throughout (Complexity.NUPPT); assumptions and security are
  "every NUPPT has negligible (or SubexpHard) advantage". Subexponential-TIME adversaries are out
  of scope.
- Reductions (design-r2 §4.8, binding shape). Each reduction X (LPN hop, PRG hop) is an explicit
  Lean function of its input x (the assumption's typed challenge), its advice omega (a finite
  type INHABITED at every parameter, with an explicit encoding that starts with the prime and has
  an explicit PolyExpr length bound) and its coins r:
    XRed A m omega x r = A.runAtL (phiX m) (XPre m omega x) (r.take (A.coinLen (phiX m)))
  with phiX m <= m (kappaOf, kappaOfN) and XPre a deterministic Lean function producing the sPRG
  challenge string of the hop's hybrid. Security is stated for every NUPPT B with
  B.RealizesOn encX (A.coins.subst .var) (fun m x r => XRed A m (omega m) x r).
- Realisation predicate (Q-S9 A). If <BASE> has TCSlib/Cryptography/Asymptotic/Realization.lean
  (Complexity.NUPPT.RealizesOn), reuse it. Otherwise write exactly design-r2 §4.8's declarations
  in StructuredSeed/Realization.lean, inside your namespace, with a docstring note that it is to
  be moved to Asymptotic/ later.
- The core theorem (S8, design-r2 §4.9): prop41, for every schedule pi and adversary A there is
  advice omegaL, omegaG such that for EVERY realisers BL, BG and EVERY kappa
    adv_sPRG A kappa <= 2*kappa*adv_LPN BL (l kappa) + adv_PRG BG (n kappa)
                        + 2*errProb kappa (pi kappa)
  with the LPN advantage in LPN's own dimension l = kappa^E, the PRG's in its seed length n, and
  errProb the explicit probability of err = 1 (Claim 4.2 bounds it by 2^(-kappa) eventually,
  uniformly in pp). Derive from it: the negligible corollary (jls_secure, theorem41), the
  explicit-exponent subexponential lemma jls_subexpSmall (exponent min(E cL, E D cG, 1)/2) and
  jls_subexpSecure/theorem41_subexp, and exists_sprg(_subexp); the assumption-level corollaries
  take the realisability propositions P.Realizable pi (the Phase B obligation) as hypotheses.
  The random-hybrid-index trick is allowed with disclosure (advice-chosen index recommended).
- Subexponential API (S7): use ONLY TCSlib/Cryptography/Foundations/Subexponential.lean at
  <BASE> (namespace TCSlib.Cryptography): SubexpSmall, subexpSmall_iff(_eventually), SubexpHard
  (any adversary type; instantiate alpha := NUPPT), subexpHard_iff, .negligible, .mono,
  .mono_exponent, .add/.const_mul/.mul_pow (each to any c' < c, needs 0 < c),
  .comp_of_rpow_le, SubexpHard.comp_of_rpow_le, eventually_const_mul_rpow_mul_two_rpow_neg_le,
  subexpSmall_two_pow_neg, subexpSmall_zero. Do NOT define a subexponential notion of your own (a
  named wrapper only as a one-line definition whose body is SubexpHard of your advantage
  function, with its _iff reader).
- Efficiency statements (Q-S10 A, design-r2 §4.10). Write, in Targets.lean, the named
  propositions evalTarget (Eval'), qGenTarget (Q_I generation, through PolyTerms), coreTarget
  (the samplers' deterministic cores on the encodings of their exact-law draws), lpnPreTarget,
  prgPreTarget (the reductions' pre-processing; one map for every schedule, length and
  adversary, the prime from the advice), and the generic SPRG.EvalEfficient and
  SPRG.HasComplexityEff in Defs.lean, plus BoolPRG.EvalEfficient and
  MultilinearRep.TermsEfficient (Phase B hypotheses). Each is a definition with its _iff reader
  and the docstring "Phase B obligation; not proved in this development". NO sorry for them. Do
  not try to prove them.
- (Q-S11 A) Prove the link, sorry-free: realizable_of_targets (P.ReductionTargets -> forall pi,
  P.Realizable pi) through Complexity.NUPPT.exists_reparam_pre_post with post := id, the
  targets used only as hypotheses; then theorem41_of_targets and exists_sprg_of_targets; and
  evalEfficient_of_target, hasComplexityEff_of_target.
- (Q-S12 A) The generic SPRG keeps a modulus schedule, publishes it in challengeStr (encPP) and
  reads it from the input in EvalEfficient; seeds are Fin-indexed Z_p vectors (C13).
- Settled by Seyoon (design-r2 §10.1): Q-S1 LPN for the construction's own l-indexed family,
  defined through an LPN-shaped LWE.Family (design-r1 §4.1, C11 with pi); the literal Def 2.3
  bridge is NOT in this job. Q-S4 Def 3.3 only for degree-d public / degree-2 private, one
  polynomial over both seed parts. Q-S5 the new area below. Q-S8 gate repairs relayed mid-run
  (item 6). Q-S3 and Q-S6 are superseded by the two-phase ruling.

3. SCOPE
- NEW FILES ONLY, all under TCSlib/Cryptography/Obfuscation/: the job's modules in
  Obfuscation/StructuredSeed/ (design-r2 §2.2), the facade Obfuscation/StructuredSeed.lean and
  the area facade Obfuscation.lean (each with a ## Contents list).
- The ONE permitted change to an existing file: the single line
    import TCSlib.Cryptography.Obfuscation
  in TCSlib.lean, right after "import TCSlib.Cryptography.AdvancedEncryption".
- FORBIDDEN: editing any other existing file (a missing reader or lemma in another file is an
  E-SCOPE question, never an edit); touching blueprint/, audits/, scripts/ or running
  scripts/sources.py; touching other campaigns' paths (complexity/arora-barak-ch3-4 and
  arora-barak-ch3-4/ on the exchange, lwe-sis-constructions/, the io-phfe unit's files and
  inbox path, Ladner material, the sampler-bridge and RAM work); pushing anything except
  inbox/fills/io-sprg/ on the exchange; pushing any campaign branch or your fill branch; new
  axioms; importing modules that cleanup Stage 2 restates (Asymptotic.Ensembles,
  EnsemblesLemmas, OneWay, Collections, HardCore.*, Games.Tapes,
  Pseudorandom.Generators.Asymptotic.Defs; design-r1 §2.3-§2.4); importing TCSlib/Programs/*,
  TCSlib/Complexity/RAMSimulation/*, CoinSampling, Games.Closeness, or the Phase B modules of
  the sweep's appendix (DyadicLinearAlgebra, DyadicArithmetic, Encoding.BinaryArith,
  Complexity.ClassP.BinaryArith.*).

4. BRANCH AND CHECKOUT (host addendum §3)
- In a git worktree of your own, never in Seyoon's exchange checkout:
    git -C <exchange checkout> fetch origin cryptography/pass-shelat-ch2-4 foundations/subexp
    git -C <exchange checkout> worktree add ../tcslib-io-sprg <BASE>
  Check git rev-parse HEAD = <BASE>. Create the local branch fill/io-sprg there. Keep it local.
- Commit with git -c commit.gpgsign=false. One .lake/packages and one olean tree
  (TCSLIB_OLEANS) for this job. Keep evidence/ untracked in the worktree (never committed on
  fill/io-sprg); it is copied into the delivery.
- Stay on <BASE> for the whole job. Do not rebase unless Seyoon asks in this chat (for example
  if the foundations/subexp PR changes its API after a gate repair, or the shared realisation
  file lands); then rebase, rebuild what changed, and record both bases in REPORT.md. The
  maintainer replays on the current tip at landing.

5. LEAN ON THIS HOST (host addendum §1-§3, LEAN_SLOT_TAG=io-sprg)
- At most 3 Lean processes run at once on this Mac across ALL jobs; the io-phfe Codex job
  shares it. THIS JOB HOLDS AT MOST ONE LEAN PROCESS AT ANY TIME:
  - run every lean, lake, probe, seal and scripts/lean_check_tree.sh command in the foreground,
    one at a time, through lean-slot.sh with one slot;
  - only you (the lead) run Lean, lake and git pushes; sub-agents, if you use any (at most 2),
    write files and never run Lean;
  - the one exception is the narrowed cache fetch, under -k 3 as the host addendum requires;
    run it once, again only when you add a Mathlib root, never while holding another slot.
  The seal runner of the bb1-sim tools calls "flock $LEAN_LOCK nice -n 10 lean ..."; replace
  that by "lean-slot.sh nice -n 10 lean ..." (record the change in the tool's header).
- NEVER run lake build. NEVER run an unfiltered lake exe cache get. The only allowed form, from
  the worktree root, after your first commit containing the new files' import lines:
    python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/fillinputs.py . HEAD \
      TCSlib/Cryptography/Obfuscation evidence/logs/fillinputs
    cp evidence/logs/fillinputs/order.txt evidence/logs/order.txt
    sed 's|$|.lean|' evidence/logs/order.txt | xargs grep -h '^import Mathlib' \
      | awk '{print $2}' | sort -u > evidence/logs/mathlib-roots.txt
    LEAN_SLOT_TAG=io-sprg lean-slot.sh -k 3 env TAR_OPTIONS=--no-same-owner \
      lake exe cache get $(cat evidence/logs/mathlib-roots.txt) 2>&1 \
      | tee evidence/logs/cache-get.log
  (order.txt excludes the root TCSlib; recompute both files whenever an import changes.) Log the
  cache store first and run the package check, as in Part 1 item 2 of the addendum.
- Check one module at a time, bootstrapping order.txt the same way:
    LEAN_SLOT_TAG=io-sprg lean-slot.sh env TCSLIB_OLEANS=<your tree> \
      bash scripts/lean_check_tree.sh <Module/Path without .lean>
- Kill only processes you started, by recorded PID; never pkill -f. Run Python as python3 -I.
- macOS preflight (host addendum §2): 4 GiB memory headroom, 12 GiB free disk, else E-RES.

6. MILESTONES (design-r2 §5; push a checkpoint at EACH, so a stalled run leaves a reviewable
   prefix)
- M0 = CHECKPOINT 0, the statements commit "io-sprg: M0 statements (all proofs sorry)". Push it
  as soon as it is ready, then keep working WITHOUT waiting for the gate. It contains:
  - every file of design-r2 §2.2 with its module docstring (# Title, ## Main definitions,
    ## Main results, ## References with the full [JLS26] citation and [PS10] for NUPPT);
  - EVERY DEFINITION FINAL (LPN family and noise, BoolPRG and its predicates, pubDegree and
    privDegree, PolyTerms, PrimeParam and PrimeSchedule, SPRG and its predicates, Params and
    derived quantities, buckets, sparse factorization, G(1)-G(4), the samplers and their cores,
    the encodings with explicit equivalences, jlsSPRG, errProb, the hybrids, the advice types
    and their encodings, lpnPre/prgPre, lpnRed/prgRed, RealizesOn if local, the realisability
    propositions, the efficiency targets), each with its readers proved (rfl, or
    simps (config := { isSimp := false })): policy §1 "Definitions land with their lemmas";
    PrimeSchedule.nonempty proved;
  - EVERY THEOREM stated with sorry under its **Proof sketch.** (the sketch is the plan; each
    sorry is a named step);
  - in REPORT.md: the fidelity table (paper item, page, Lean name, file:line, deviations), the
    helper plan, a non-vacuity table (every advice type and PrimeSchedule inhabited, every
    realisation hypothesis constrains only encoded challenges), and a size re-estimate.
  M0 checks: every new module elaborates (rc 0, 0 errors in both forms) with sorry warnings
  only on the listed theorems; decls2 and StmtDump; axioms (sorryAx only in the sorried
  declarations); coe-A seals and paired controls on the definitions; lint; widths; clash scan.
- AFTER M0 THE STATEMENTS ARE FROZEN. A header or statement-prose change happens only (a) by a
  statements-gate repair that Seyoon pastes into this chat (Q-S8: you continue after checkpoint
  0; the gate's majors arrive here and you apply them), or (b) when a statement is false or
  unprovable as written (E-ROUTE, item 12). Either way: its own commit
  "io-sprg: statement change <id>: <reason>", listed in REPORT.md § Statement changes, pushed as
  a checkpoint. Never rewrite the M0 commit. New helper lemmas may be added (listed, disclosed).
- M1 algebraic correctness (G(1)-G(4) through the renaming, sparse factor, buckets, degree
  lemmas, G4_eval_eq, jls_hasComplexity, lpnNoise_law); M2 stretch (Claim 4.1); M3 Claim 4.2
  (uniform in pp); M4 hybrids, the hop lemmas for every realiser, and prop41 (the core
  inequality); M5 Theorem 4.1 (jls_secure, jls_subexpSmall, jls_subexpSecure, theorem41,
  theorem41_subexp, exists_sprg, exists_sprg_subexp); M6 the targets link (advice length bounds,
  realizable_of_targets, theorem41_of_targets, exists_sprg_of_targets, evalEfficient_of_target,
  hasComplexityEff_of_target). M1-M3 may be reordered; M4 needs M1; M5 needs M2-M4; M6 needs
  M4. Each milestone: one or more commits "io-sprg: M<k> <title>", then a checkpoint push.
- Expected size about 4,600-7,900 lines (design-r2 §2.2, §5). If you finish early, do not add
  scope (in particular, do not start Phase B); if you run out of budget, push what passes and say
  exactly where you stopped.

7. CODE STANDARDS (policy.md; workflow.md)
- Layout, facades, precise imports (no bare "import Mathlib"), the file header (copyright, the
  three set_options), area-local namespace TCSlib.Cryptography.Obfuscation.StructuredSeed,
  helpers private or in an inner namespace, nothing in the root namespace.
- Files at most 1000 lines (target 150-600); every line at most 100 characters (Python len);
  check both with a python3 -I script before each push and keep its output.
- Attribution: [JLS26, ...] tags at theorem and section level as in item 1; glue lemmas say
  "glue" in one line. Every public declaration's docstring opens with a statement in words and
  its formula. Every proof of 15 lines or more, and every sorry at M0, has a
  **Proof sketch.** naming its steps (visible as haves or lemmas); long proofs carry step
  comments. A sketch changes in the same commit as its proof route.
- No @[simp] and no global attribute. At the end: no sorry, admit, native_decide or new axiom
  anywhere in the job; #print axioms of every public theorem gives only propext,
  Classical.choice and Quot.sound (or a subset).

8. DUPLICATION (binding)
- Any undisclosed re-proof of a public TCSlib or Mathlib lemma, INCLUDING AN INLINE
  RE-DERIVATION inside a proof, is a major.
- Search before every helper: name search in TCSlib and in .lake/packages/mathlib, exact? and
  apply? on the statement in a scratch probe, and grep for the conclusion's shape. Disclose every
  helper with its searches in REPORT.md § Overlap and reuse.
- duplication-sweep-r2.md is the MUST-REUSE list (rows marked MR) and the do-not-use list (X);
  its Phase B appendix (B) is not for this job. For each MR row the route needs, use it; if you
  do not use one the design names, say why. The Foundations/Subexponential API is MR for every
  subexponential step; NUPPT.exists_reparam_pre_post is MR for the targets link.

9. RULE 10 (policy §1; MAINTAINER-HANDOFF §3): readers only
- No statement or proof reads another file's TCSlib definition except through lemmas published
  beside it (equations, _eq/_iff readers, simps projections, run and contract lemmas). Each of
  your files is foreign to the others, so every definition another of your files uses lands
  with its reader in its own file at M0 (this includes the reduction functions, the advice
  encodings, the realisation predicate and the targets). Core and Mathlib definitions may reduce
  in rfl, decide or show, but are never passed to simp, rw or unfold (use their equation lemmas).
- Notation, never sealed: reducible abbreviations (ProbComp, QueryImpl, NUPPT.Coins,
  PrimeSchedule, and your own abbrevs, which still need _eq/_iff readers), PolyExpr.eval,
  projection coercions and the FinDist coercion.
- What you run and deliver, for EVERY new module (owner), at M0 (definitions) and at the final:
  a) Canonical seals: a probe copy of the owner with `attribute [local irreducible]` on every
     ordinary TCSlib definition of its full import closure that is defined in another module
     (term-collected with the suite's collector, matchers included), compiled with
     lean -DmaxErrors=0 (no -o). Four variants: A (PolyExpr.eval excluded as notation), B
     (PolyExpr.eval sealed too), each strict (everything sealed) and coe (the FinDist coercion
     instance excluded as notation). COE-A IS CANONICAL. Count errors in both forms
     ^\S+\.lean:\d+:\d+: error[:(]. Required: 0 failing declarations in coe-A and in coe-B;
     every strict-only failure attributed (the FinDist coercion) and listed. Report each
     seal's request count. Use SEAL_CHUNK if a harness overflows.
  b) Paired controls: for every new public definition that a later module of yours uses, a
     negative (the unfolding its reader replaces, by rfl/unfold/show, in a consumer-context
     probe) and a positive (through the reader). Pretest unsealed: all pass. Sealed: each
     negative fails exactly once, each positive passes, no stray error; strict and coe both
     ALL_OK True.
  c) The explicit-unfold scan of every new file: 0 foreign TCSlib definitions passed to simp,
     rw or unfold or read by .eq_N/.eq_def/.eq_unfold.
  Adapt the bb1-sim suite (review/mkcollect.py with NmCollect.template.lean,
  review/mkseals_ab.py, review/mkseals_coe.py, runner_full.py, review/sealsum.py,
  review/ctlcheck2.py, scan2.py and review/archived-gate10-tools/); copy what you use under
  evidence/tools/ and record every host-path change in each tool's header.

10. CHECKS AND EVIDENCE (final; M0 runs the subset of item 6)
- Build: bootstrap order.txt, then check every new module in order, each rc 0 and 0 errors in
  both forms; evidence/build/summary.txt binds each checked source to git show HEAD (module,
  rc, errors in both forms, sorry warnings, source SHA-256). The root TCSlib is not built.
- Statements: python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . <BASE>
  <every new file and TCSlib.lean>: ADDED only, 0 CHANGED, 0 REMOVED. A StmtDump probe prints
  every new public constant with its full name and type.
- Frozen files: git diff --stat <BASE> lists only the new files and TCSlib.lean (+1 line);
  git diff <BASE> -- TCSlib.lean is exactly the one import line.
- Axioms: #print axioms of every public theorem; a census of every stored constant of the new
  modules (0 non-standard); a sorryAx dependency trace (empty at the final; at M0 exactly the
  sorried theorems).
- Phase A boundary: a grep showing no import of TCSlib.Programs, TCSlib.Complexity.RAMSimulation,
  CoinSampling, Games.Closeness or the sweep's appendix modules; no use of PrimeFind,
  Fintype.equivFin or Classical.choose inside an encoding, pre-processing map or target.
- Rule 10: item 9 a)-c).
- Lint: python3 -I scripts/style_lint.py <every new file>: no finding.
  python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b at <BASE> and at your
  head; diff the line sets: no new FAIL or WARN line (check 8/8b: no definition without its
  lemmas). Run dev/sk15.py on the new code.
- Sizes and widths of every new file; name-clash and shadow scans (no new full name already in
  TCSlib/ or audits/ at <BASE>; list new short names that exist elsewhere).
- Reuse: item 8.

11. DELIVERY (workflow.md §4.1 on main; host addendum §5)
- From your own delivery worktree of the exchange:
    git -C <exchange checkout> worktree add ../exchange-io-sprg origin/exchange/pass-shelat-ch5-8
  write ONLY inbox/fills/io-sprg/. Before each push: git pull --rebase origin
  exchange/pass-shelat-ch5-8; never force-push; commit with commit.gpgsign=false. Commit
  messages: "fill io-sprg: checkpoint 0 (M0 statements)", "fill io-sprg: checkpoint <k> (M<k>)",
  "fill io-sprg: final", or "... (blocked: <code>)". If a push is refused, keep the commit and
  say so here; Seyoon pushes it.
- Payload (each checkpoint and the final; a checkpoint may carry partial evidence, named as
  such):
  - REPORT.md: bases and heads (fill/io-sprg head, every commit); milestones table (status,
    commit, lines); the fidelity table; the non-vacuity table; § Statement changes (none, or
    each with its reason and the gate finding); § Deviations from the design note; § Overlap and
    reuse (every helper, its searches, the MR rows used); the checks of item 10 with counts; the
    headline axiom prints (prop41, claim42, G4_eval_eq, jls_hasComplexity, jls_hasPolyStretch,
    lpnNoise_law, jls_secure, jls_subexpSmall, jls_subexpSecure, theorem41, theorem41_subexp,
    exists_sprg, exists_sprg_subexp, PrimeSchedule.nonempty, realizable_of_targets,
    theorem41_of_targets, exists_sprg_of_targets); the list of Phase B targets with their
    statements; host notes (preflight numbers, the slot cap quoted, waits); questions SP-W1,
    SP-W2, ... with the recommended option first;
  - patches/: git format-patch <BASE>..fill/io-sprg, with COMMITS.tsv (hash; author name,
    email, date; committer name, email, date; signing). git am at <BASE> must reproduce every
    hash: check it in a scratch clone before each push and say so;
  - bundle/io-sprg.bundle: git bundle create of <BASE>..fill/io-sprg (git bundle verify output
    in evidence/);
  - src/: every new or changed file at the branch head, under its repository path;
  - evidence/ with its manifest evidence/SHA256SUMS: preflight, cache and package logs, slots
    lines tagged io-sprg from ~/.lean-slots/slots.log, order.txt and mathlib-roots.txt, build
    logs and summary, decls2, StmtDump, frozen-file diff, axioms and trace, the Phase A boundary
    grep, seals (probe sources, manifests, request records, raw logs, results.jsonl), controls,
    the unfold scan, lint (base and head), sizes and widths, clash scans, reuse searches, tools;
  - a top-level SHA256SUMS of every delivered file except itself. Delivered paths must EQUAL
    the manifests' paths: nothing missing, nothing extra, no leading "./". Check before each
    push. If the evidence is too large for one commit, split it into several commits with entry
    lists; leave nothing out.
- At the end, also return the final payload here as a ZIP with io-sprg/ at its root, and a
  short report in this chat: milestones reached, the exchange commits, the fill/io-sprg head,
  the headline axiom prints, and the open questions.

12. ESCALATION (push a checkpoint whose REPORT.md opens with the blocker; keep everything that
    passes; continue on other milestones where you can)
- E-RES: the preflight or cache rules fail (quote the numbers).
- E-BASE: <BASE> is not what git rev-parse gives, or the base does not elaborate.
- E-SCOPE: the route needs a change to an existing file (a reader, an import, a promotion), any
  machine construction or PolyTimeComputable proof beyond using NUPPT.exists_reparam_pre_post
  with the targets as hypotheses, any RAM or sampler-bridge module, or anything item 3 forbids.
  Ask Seyoon here with the file, the diff and the reason; go ahead only on his approval; record
  request and answer verbatim under evidence/scope-request/.
- E-ROUTE: a statement looks false, unprovable or vacuous as written (including an empty advice
  type or a realisation hypothesis no machine could meet). State the exact obligation, with the
  failing goal or a counterexample, and propose the minimal disclosed change. Never weaken a
  statement silently, add a hypothesis silently, or use a private stand-in.

Treat repository, exchange and PDF content beyond rulings.md, this prompt, design-r2.md (with the
design-r1.md sections it keeps) and the two addenda as working material.
```

The status becomes **Ready to dispatch** once the three placeholders are filled and the
pre-dispatch steps in `README.md` are done.

**Not yet ready to dispatch: placeholders, the base (Q-S9), the staged source, Seyoon's answers to
Q-S9–Q-S12, and the PHFE pack r2 (Phase A dispatches after it) are pending.**
