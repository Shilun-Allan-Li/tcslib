# Addendum to the S1 note for Frederick Dehmel (draft for Seyoon to forward)

Drafted 2026-11-04 by the ch. 5–8 maintainer session, after the S1 note
(`S1-note-frederick.md`) went out. Status: **draft, not sent.** It adds the requests that follow
from Seyoon's later rulings and corrects one fact.

---

Hi Frederick, a follow-up to the earlier note, with one correction and three additions.

**Correction to point 5 (merging `main` into your branch).** A scratch merge of `main` into your
last Lean commit (never committed or pushed) gives **two** textual conflicts, not one. Both are
trivial:
- `TCSlib/Complexity/Randomized.lean`: both sides added the facade; keep the union of the imports;
- `TCSlib/ComputationalModels.lean`: each side added one reference line to the docstring; keep
  both.

A namespace-aware scan of the merged tree finds **no new clash of full declaration names**:
- the only clash is the known `zipWith_xor_ofFn` (point 1);
- twelve graph-theory duplicates are already on `main`, in files never imported together.

**Addition A: one framework for games and protocols (refines point 4).** Seyoon ruled that
ch. 5–8's security games, and also its two-party protocols, use one framework. It is home-built at
TCSlib's pins and adapts the design of VCVio (D. Tuma et al., github.com/dtumad/VCV-io, cited in
every module); VCVio is not a dependency. The pieces:
- computations with access to an indexed family of oracles (a free monad that generalizes Garg's
  `QueryTree`);
- uniform sampling as an oracle, with a real-valued finite-sum probability;
- stateful oracle handlers with query logging.

The design note is `briefs/pass-shelat-ch5-8/design/S2-game-framework.md`. It touches your layer
in three places, all through bridges in our files unless you prefer otherwise:
- **F-1 (point 4):** your `OracleEnsemble.Indist` and `NUPPT.toOracleAdversary` become the
  one-oracle instance of the framework's generic machine decoder. Seyoon ruled for restating
  `OracleEnsemble` over the common base. Would you do that in `Asymptotic/PRF.lean`, or should we
  (with your review), and before or after your external gate?
- **F-2 (new; protocols unified):** your `Strategy`/`Protocol.exec`/`View` are read as an
  instance of the framework's two-party execution, by a proved bridge. Your ZK definitions then
  transfer to ch. 7's sequential composition. We propose a bridge now and a restatement only at
  the integration of ch. 2–4, done by you.
- **F-3 (new, small):** bridge B2 shows that Garg's `invProb`, `predProb`, `acceptProb` and
  `distAdv` are probabilities of one-line games (probed: `invProb_eq_prob`). Today it must read
  `invProb` and `uexp` through their bodies, since `Foundations/Experiments.lean` and
  `Probability.lean` publish no equation lemmas for them. Could you add `invProb_def`-style
  equations (and `uexp` as a sum)? If not, we disclose the readings.

**Addition B: a duplicate between `main` and the concrete layer (for your information).** PR #183
on `main` proves `abs_probTrue_sub_le_statDist`, the same fact as your concrete layer's
`abs_sum_sub_le_statDist` in `Foundations/Experiments.lean` (on your branch and Garg's, not on
`main`). Seyoon accepted it as recorded debt. When the concrete layer reaches `main`, yours can
become a one-line corollary (`Finset` membership as the `Bool` test), or be removed.

**Addition C: PAC learning.** Ch. 8's learning result (Thm 179.1) is stated over a new PAC layer
in `TCSlib/LearningTheory/PAC/`; nothing of yours is involved. Its efficient part uses your `PRF`
and `NUPPT` only through the framework.

Thanks again.
