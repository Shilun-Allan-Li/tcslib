# Ch2 fill campaign — Epoch 3, Batch D: `TAUTOLOGY ∈ coNP`

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e3-D`). The
  required base is `b55180a8bb38b94427e75e63630aa6eab5fd6e95`; record it in
  `REPORT.md` and never rebase onto anything else.
- **Delivery is by zip, not PR or push**: `fill-ch2-e3-D.zip`, **flat**
  (`SHA256SUMS` at the root), with `REPORT.md`, the full modified source,
  the `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

Epochs 1 and 2 are complete and audited (38/59 proved;
`audits/ch2-epoch2-resolutions.md`). Your batch is one target —
**`TAUTOLOGY ∈ coNP`** [AB09, §2.6.1], the complement-certificate
membership over the DNF fragment. The formula layer is proved (E1 1D:
`evalDNF_dual`, `dnfTautology_dual_iff`, `eval_congr_of_lt_numVars`,
`numVars_decode_le`, `decode_serialize`), the `coNP` vocabulary is proved
(E1 1C: `mem_coNP_iff_forall` et al.), and the verifier-machine
obligations mirror the `SAT_mem_NP` set being filled concurrently (3B) —
but **your batch must not depend on 3B's results**: build your own
verifier through the audited library
(`Build/{Convention,Wrappers,Loop,Primitives}`) and the proved epoch-2
precedents (`NP.lean`'s odd-split recovery, `TMSAT.lean`'s parsing
machines).

## Owned file and target

- `TCSlib/Complexity/ClassNP/Tautology.lean` — target:
  `TAUTOLOGY_mem_coNP` (6 pts). Per the binding docstring sketch: exhibit
  `TAUTOLOGYᶜ ∈ NP` with parameters `(1, 1)`; the verifier runs the
  odd-length split with explicit even rejection, the shared parsing
  machine pattern, the assignment walk, and the **dual** evaluation loop —
  accept iff **every** term contains an unsatisfied literal, i.e. evaluate
  `evalDNF` and answer its negation (an empty term forces rejection, the
  empty formula forces acceptance — the phase-4 round-1 finding-2
  correction, already embedded in the docstring); buffered verdict.
  Malformed strings: the fallback is not a DNF tautology, so they lie in
  `TAUTOLOGYᶜ` and the verifier accepts them with any certificate.

  **`TAUTOLOGY_coNPComplete` in the same file is NOT yours** (E4, batch
  4B). Leave its admission untouched.

## Environment and verification

- Pinned toolchain (Lean 4.25.0, `cdd38ac5115b`; mathlib `029db123ddaa`).
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap the **57-module** order
  (`scripts/ab_ch1_module_order.txt` via `scripts/lean_check_tree.sh`);
  iterate the owned module plus later modules; final full fresh sweep,
  zero `error:` lines.
- **Axiom prints**: the target at most
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` — **zero
  sanctioned admitted dependencies**. Kernel-traversal template:
  `audits/programs/ch2-e2-ClosureAxioms.lean`.

## Ground rules (binding)

1. **File ownership.** Only `Tautology.lean`; only the one target plus
   `private` helpers; list every new declaration.
2. **Statement freeze** absolute; escalation over alteration, always.
3. Docstrings stay (append-only, flagged). Precise imports; keep
   `set_option` headers.
4. **Budget** (6 points): if exhausted, deliver a partial flat zip per the
   standing partial-delivery protocol.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/ch2-phase4-findings.md` (finding 6 and the membership
derivation, via the phase-4 resolutions):

> The named DNF evaluation-congruence obligation is elementary and
> sufficient at statement phase. **A private evaluation-congruence lemma
> is appropriate during the fill.**

> For membership in `coNP`, fix a formula string `x` of length `n`. The
> complement condition is an assignment making `evalDNF (decode x)` false.
> Since `(decode x).numVars ≤ n`, a certificate of exactly `n+1` bits
> suffices: restrict a falsifying total assignment to those bits;
> conversely extend a certificate by `false` beyond its length. Agreement
> on mentioned variables preserves each literal, each conjunction, and
> their disjunction. This proves the named DNF congruence bridge without a
> new conceptual assumption. Alternatively, involutivity of `dual` and
> preservation of `numVars` reduce it to the trusted CNF congruence
> theorem and the new De Morgan identity.

Either congruence route is acceptable; state the bridge as a `private`
lemma and name it in `REPORT.md`. The parsing-then-evaluation order of the
phase-3 SAT contract is binding here too: a complete syntax pass precedes
any semantic verdict.

## Out-of-scope sorries you will see (leave untouched)

`TAUTOLOGY_coNPComplete` (your own file — E4); the padding cluster and
`EXP_subset_NEXP` (3A, concurrent); `SAT.lean` (3B, concurrent);
`CookLevin/Snapshot.lean` (3C, concurrent); `CookLevin/Hardness.lean`
(E4).

## REPORT.md checklist

- [ ] Target filled; the dual-evaluation discipline, the private
      congruence bridge, and the malformed-string equivalence called out
      explicitly and mapped to discharging lemmas.
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom print (standard triple at most, roots empty); final sweep log
      tail; diff touches only `Tautology.lean`; archive flat.
- [ ] Requested shared lemmas / escalations — or "none".

## Known pitfalls at this pin (hard-won)

- The complement changes every polarity: the verifier accepts on a
  **falsifying** assignment; the `coNP` wrapper then flips once more via
  the `mem_coNP` route — keep the two negations separate and let the
  frozen statement dictate the direction.
- The fallback convention is the mirror of `SAT`'s: `evalDNF [] = false`
  (empty DNF is not a tautology), so parse failure keeps the string in
  `TAUTOLOGYᶜ` and the verifier **accepts** it — consistent on both sides
  of the equivalence, for every certificate.
- The E2 pitfall lists carry over (`briefs/ch2-epoch2-batch{C,D}.md`):
  `Function.update_of_ne`; `dsimp only` after `cases hs : cfg.state`;
  buffered output — the real output stays empty until the single verdict;
  odd-split recovery is a proved precedent in `NP.lean` and `TMSAT.lean`.
- `evalDNF_dual` and `dnfTautology_dual_iff` are proved — if you take the
  dual route, consume them rather than re-deriving De Morgan reasoning.
