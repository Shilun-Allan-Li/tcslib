# Sampler bridge: exact non-dyadic laws from fair coins, perfect correctness kept

In-house library work (Seyoon, 2026-11-18; `IOComponentsPlan.md` § *Deferred library work*),
reusable across campaigns; it closes the sampler gap of the sPRG and PHFE jobs. Static design,
no Lean run. Bound by the TM-model and uniformity rulings relayed on 2026-11-18 (design §0).

| File | What it is |
|---|---|
| `design-r1.md` | problem (§1), what exists with file:line (§2), consumer gains (§3), the proposal (§4), options (§5), duplication sweep (§6), layout and size (§7), risks (§8), **questions (§9)** |
| `Skeleton.lean` | the proposed declarations, full statements, `sorry` proofs, policy docstrings (936 lines, 114 declarations; a draft, not checked) |

**Recommended formulation.**
- *Per sampler*: `CoinSampler Ω s`: a decoder `(Fin s → Bool) → Option Ω` (`none` = give up),
  exact on success (the library's existing `*_uniform_of_some` shape); `fail` derived; the mixture
  identity `𝔼 F(dec) = fail·F(none) + (1−fail)·𝔼_a F(some a)`. Seyoon's sketch is `bucket N s`:
  one `uniformFromBits` trial at `⌊2^s/N⌋·N`, then `x mod N`; `fail = (2^s mod N)/2^s < N/2^s`.
  Rational laws: `RatSeed w = Σ a, Fin (w a)` + `weighted`.
- *Per experiment*: `ProbComp.Close ε` (`[0,1]`-tests), closed under `bind` and `simulate`
  (`m` queries ⇒ `m·ε`); atoms `close_draw_bind`, `close_drawD_bind`, `close_simulate_draw`;
  `advantage_le_of_close`.
- *Correctness*: `OracleComp.OutputsSubset` + `outputsSubset_drawD`: with a default fallback every
  `AllOutputs` property (IBE/FE `Correct`, `encPP_inj`, sPRG `HasComplexity`) transfers exactly;
  custom fallbacks (send in the clear) via `allOutputs_draw_bind`.
- *Asymptotics*: `drawSlack q t = q(κ)·2^{-t(κ)}`; `t ≥ κ` ⇒ `Negligible`, `SubexpSmall c` ∀ `c < 1`.
- *Efficiency (TM model, uniform)*: `UniformSampler`: one `PolyTimeComputable` raw map on the NUPPT
  layout, modulus read from the input; machine `NUPPT.ofPolyTimeUniform` (empty advice).
  `bucketRaw` from proved `BinArith` `mod`/`sub`/`lt` + `toLE`/`fromLEPoly`; no host, no κ-indexed
  programs, no hard-wired `p(κ)`.
- *Instances*: `zmod q`, LWE noise seeds, `lweSeeds` + LWE challenge transfer (any `q`, not only `2^w`).

**Reuse.** `statClose_getD_of_uniform_of_some` (applied), `uniformFromBits`, `rejectionSample`
(instance), `StatClose` API, `OneWay.statClose_pi`, `Games` `expect`/`AllOutputs`/`simulate`,
`Negligible`/`SubexpSmall`, `NUPPT.ofPolyTimeUniform`, `BinArith`, Mathlib `finProdFinEquiv`,
`finSigmaFinEquiv`, `ZMod.finEquiv`. One disclosed overlap (mixture identity vs the fibre step of
`statClose_getD_of_uniform_of_some`): Q8.

**Questions** (design §9; recommended first; ★ shapes the API): ★Q1 per sampler / per experiment
(contract + `ProbComp.Close`) · ★Q2 fallback (default value; branch form available) · ★Q3 give-up
type (`Option`) · Q4 bucket map (`x mod N`) · Q5 slack bits (`t` parameter, default κ) · ★Q6 target
law (uniform + pushforwards) · ★Q7 home (`Cryptography/CoinSampling/` + `Games/Closeness.lean`) ·
Q8 overlap dedup (prove beside the old lemma) · Q9 no retrofit of `BB1Machine.draw` · ★Q10 how the
modulus reaches sPRG/PHFE machines (input numeral) · Q11 first-PR scope (all eight modules).

**Size.** ≈ 1,800–3,000 Lean lines (central 2,300) in 8 new files plus 2 facade lines; can split
into two PRs (`Asymptotic` waits for `foundations/subexp`, PR #374). Stage 2 crossings: additive or
proof-level only. Gate item: `#print axioms` on the efficiency theorems (the TM tooling's import
closure has 17 `sorry`s in 7 modules; reach unchecked).

**Status:** draft for Seyoon's review; nothing in `TCSlib/` touched.
