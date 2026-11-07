# Maintainer tools and templates

`tools/` holds the scripts the maintainer used, copied from its session scratch on 2026-11-07. Run them
with `python3 -I`; see `../MAINTAINER-HANDOFF.md` §5 for what each does. Related tools kept with
their evidence:
- **Gate 04's rule-10 seal package** (classifier `declx.py`, collector, `seal.py`, `exclude.py`,
  scanner `scan.py`, `unsealable.py`): `../gates/04-s2b/evidence-r5/tools/`.
- **#210's whole-file proof seal** (`proofseal.py`, the touched-classification scripts):
  `../gates/07-eqlemmas/evidence-r2/r6c/` and `r6c/proofseal-tools/`.
- **The explicit-unfold scanner, as #210 used it:** `../gates/07-eqlemmas/evidence-r2/r6b/tools/`.

`templates/` holds:
- the internal fill environment note (for fills run by maintainer sub-agents);
- the fill-brief review instructions;
- the equation-lemma brief common text.

The external dispatch templates (audit and fill prompts) are in `../EXCHANGE.md`.
