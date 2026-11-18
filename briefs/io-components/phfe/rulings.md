# io-phfe: rulings in force (Phase A)

Seyoon's rulings for the io-phfe job. This file takes precedence over `dispatch-prompt-r3.md`,
the design notes, the source notes and the sweeps. Rows are the decision-log rows of
`IOComponentsPlan.md`, all dated 2026-11-18, named by their bold title.

## Standing rule
- **Rule 15** (`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2; rows *Efficiency is
  mandatory* and *Efficiency baked into definitions*). Honest algorithms and simulators are
  efficient in uniform form only (`PolyTimeComputable`, or `∃ A, A.Uniform ∧ A.Computes f`;
  never a bare `∃ A : NUPPT, A.Computes f`). Every interface (`FEScheme`, `Simulator`,
  `SASimulator`, `PartialGarbling`) carries that efficiency as structure fields. Constructions
  are raw bundles; the primitives are assembled from them and the targets. In Phase A the
  targets are written, not proved.

## Campaign and phase
- *Campaign opened*: non-uniform PPT throughout.
- *PHFE notion*: the notion JLS26 Thm 5.1 consumes via GJLS21 Thms 10.3/10.4; the statements
  gate checks fidelity to it first.
- *Follow the journal pipeline*: symmetric prime-order bilinear groups with DLIN; public-key
  PHFE from DLIN [Wee20].
- *Generic FE*: a generic FE interface with PHFE as an instance; fidelity wins over generality;
  the IBE interface is not refactored.
- *sPRG rulings*, Q-S2: a fixed prime schedule p(κ) in both jobs (overrides this pack's Q9
  default); *Strategy and uniformity* (3): every statement for every schedule, p read from pp.
- *Strategy and uniformity*: (1) Phase A only: explicit functions, correctness, explicit
  security inequalities for every realising NUPPT; no machines, no RAM, no samplers built.
  (2) Uniformity, binding: one algorithm for all κ, no per-κ constants; advice only for
  reductions and adversaries, only as input.
- *Subexponential security*; *`Foundations/Subexponential.lean` written*: explicit inequalities,
  then negligible and subexponential corollaries through #374's API only.

## Questions
- r2's settled r1 questions stand (design-r2), with Q11 amended as design-r3 § 0 says.
- **Q1 (A)** µ ∈ ℤ_p; **Q2 (A)** partial garbling as interface + proved instance; **Q4 (A)** one
  job, PARTIAL final allowed; **Q5 (A)** the shared `Complexity.NUPPT.RealizesOn` (*Phase A
  rulings, first batch*; *Partial-garbling sources received*; *Shared
  `Asymptotic/Realization.lean` written*). Its body constrains only encoded challenges and coin
  strings of the layout's length; must-reuse with its readers.
- **Q3**: Wee20's semi-adaptive SIM notion for both layers, GJLS21 Def 4.3 derived (*Phase A
  rulings, second batch*).
- **Q-E1 (A)**, resolved by the contract file (*Shared sampler contract and Phase A base built*;
  `briefs/io-components/contract/REPORT.md`): `TCSlib/Cryptography/CoinSampling/Contract.lean`
  (`foundations/coin-contract` `8e01b720aa127f6cbdb066e629f883258b73cf9e`) is at the base.
  MUST-REUSE `DrawSamplable`, `CoreComputable`, `SamplesEfficiently`, their readers and closure;
  no local `SamplerEfficiency.lean`. Disclosed limits: no product-of-draws sampler (Phase B), and
  the unused `Fintype` binder was dropped.
- Sampler bridge (*Sampler-bridge rulings*; *Sampler bridge implemented*, #378): of it, only the
  types `UniformSampler` and `CoinSampler.fail`.

## Base
- `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`: #374 `foundations/subexp`
  (`cbce64d1`), #378 `foundations/coin-sampling` (`51dc7672`), `foundations/coin-contract`
  (`8e01b720`), #380 `foundations/realization` (`cdc0934f`). Shared with io-sprg. The base
  placeholder still in design-r3, duplication-sweep-r3 or older files of this folder means this commit.

## Sources
- No PDF is committed or pushed anywhere: pairing ruling **Q12 (A)** (`PairingCryptographyPlan.md`,
  PDFs uncommitted), applied here; the ePrint PDFs are not ours to redistribute.
- Seyoon gives Codex a local folder when he dispatches ("the source folder Seyoon gives you").
  This job needs all five; each must hash (SHA-256) as follows before it is read:
  - `gjls21.pdf` `481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed`
  - `wee20.pdf` `d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a`
  - `jls26.pdf` `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`
  - `agw20.pdf` `b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f`
  - `iw14.pdf` `ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77`
- Nothing is staged on the exchange; `sources-r3.md`'s staging step, the exchange-staging
  placeholder and the `outbox/io-components/sources/` path in older files of this folder are
  void. Delivery is
  unchanged: `inbox/fills/io-phfe/` on `exchange/pass-shelat-ch5-8`.

## Host
- One Lean process for this job at any time, through `lean-slot.sh` (tag `io-phfe`); 3 in all on
  Seyoon's Mac, shared with io-sprg.

## Rulings during the job (confirmed by Seyoon, 2026-11-18, Q-G51-3 (A))
These were given in the worker's chat and recorded in the payload (`evidence/logs/rulings.json`);
they are confirmed and filed here.
- **Lean through the slot wrapper.** Every Lean command runs through `lean-slot.sh` (tag `io-phfe`).
- **g in PPGen.** The public-parameter generator includes the uniform non-identity generator g, with an
  efficiency field `FEScheme.pubGen_eff` and its target (a deviation from design-r3 §1E.1). Its
  parameter word carries κ: `fun κ d => NUPPT.advInput κ d.val` (Gate 51 R3, statements r2).
- **Best judgment while Seyoon is away**, every such decision disclosed in REPORT.
- **Statement repairs:** statements r1 (PHFE-C0-F01, fixed-width simulator state) and statements r2
  (Gate 51: R1 `CircuitLinearEfficient`, R2 `state_bounded`/`value_bounded`, R3, minors G51-01, 05–11).
- **Payload limit** (Q-G51-1 A): source, patches, REPORT, SHA256SUMS and compact evidence of checks
  actually run; ≤ 20 MB and ≤ 50,000 lines outside `src/` and `patches/` per checkpoint.
- **Lean replay** is the maintainer's; the worker does not claim one.
