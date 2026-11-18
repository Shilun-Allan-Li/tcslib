# io-sprg: rulings in force (Phase A)

Seyoon's rulings for the io-sprg job. This file takes precedence over `dispatch-prompt-r3.md`,
the design notes and the sweeps. Rows are the decision-log rows of `IOComponentsPlan.md`, all
dated 2026-11-18, named by their bold title.

## Standing rule
- **Rule 15** (`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2; rows *Efficiency is
  mandatory* and *Efficiency baked into definitions*). Honest algorithms are efficient in uniform
  form only (`PolyTimeComputable`, or `∃ A, A.Uniform ∧ A.Computes f`; never a bare
  `∃ A : NUPPT, A.Computes f`). Every primitive (`SPRG`, `BoolPRG`, `LPNFamily`) carries that
  efficiency as structure fields. The construction is a raw bundle; the primitive is assembled
  from it and the efficiency targets. In Phase A the targets are written, not proved.

## Campaign and phase
- *Campaign opened*: non-uniform PPT throughout; statements use degree d (JLS26 Thm 4.1, p. 17),
  not p. 14's "d+1".
- *sPRG design inputs*: rounding left to the maintainer; exact finite laws with samplers as
  separate contracts.
- *Strategy and uniformity*: (1) Phase A only: explicit functions, correctness, explicit
  security inequalities for every realising NUPPT; no machines, no RAM, no samplers built.
  (2) Uniformity, binding: one algorithm for all κ, no per-κ constants; advice only for
  reductions and adversaries, only as input. (3) p is an input; every statement holds for every
  prime schedule.
- *Subexponential security*; *`Foundations/Subexponential.lean` written*: explicit inequalities,
  then negligible and subexponential corollaries through #374's API only.

## Questions
- **Q-S1 (A)**, **Q-S4 (A)** (*sPRG rulings*); **Q-S2 (A), refined** (*sPRG rulings*; *Strategy
  and uniformity* (3)).
- **Q-S5 (A)**, **Q-S8 (A)** (*Efficiency rulings* (4) and its last clause).
- **Q-S3**, **Q-S6**: superseded by *Strategy and uniformity* (1). **Q-S7**: withdrawn in r1.
- **Q-S9 (A)**: the shared `Complexity.NUPPT.RealizesOn` (*Phase A rulings, first batch*;
  *Shared `Asymptotic/Realization.lean` written*). Its body constrains only encoded challenges
  and coin strings of the layout's length; must-reuse with its readers.
- **Q-S10 (A)**, **Q-S11 (A)**, **Q-S12 (A)** (*Phase A rulings, second batch*). Q-S11's link
  is the shared `exists_realizesOn_of_preTarget` of the realisation file.
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
  (`8e01b720`), #380 `foundations/realization` (`cdc0934f`). Shared with io-phfe. The base
  placeholder still in design-r3, duplication-sweep-r3 or older files of this folder means this commit.

## Sources
- No PDF is committed or pushed anywhere: pairing ruling **Q12 (A)** (`PairingCryptographyPlan.md`,
  PDFs uncommitted), applied here; the ePrint PDFs are not ours to redistribute.
- Seyoon gives Codex a local folder when he dispatches ("the source folder Seyoon gives you").
  This job needs only `jls26.pdf`, which must hash (SHA-256) to
  `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` before it is read.
- Nothing is staged on the exchange; the exchange-staging placeholder and the
  `outbox/io-components/sources/` path in older files of this folder are void. Delivery is
  unchanged: `inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

## Host
- One Lean process for this job at any time, through `lean-slot.sh` (tag `io-sprg`); 3 in all on
  Seyoon's Mac, shared with io-phfe.
