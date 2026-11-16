# GSW phase 5 · rulings Q1–Q16 (Seyoon, 2026-11-16)

Seyoon accepted all sixteen recommendations in [questions.md](questions.md), with one change to **Q9**.

- **Q9 (changed): the module location is a new top-level folder.** The modules live at
  `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/{Gadget,Noise,Scheme,Eval,Security,Symmetric}.lean`.
  - The namespace is `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`.
  - The facades are `AdvancedEncryption.lean`, `AdvancedEncryption/Homomorphic.lean` and `…/Homomorphic/GSW.lean`.
  - Seyoon's reason: homomorphic encryption is a very different beast from SKE and PKE, so it does not belong under
    `Encryption/`.
  - The column leftover-hash lemma stays at `Hashing/SIS/Columns.lean`, as Q9-A proposed.
- **Accepted as recommended:**
  - Q1 (A): the `DAGCircuit` via `runWith`.
  - Q2 (A): the small owner-side PR to `DAGCircuit.lean` (depth readers and `runWith_rel`).
  - Q3 (A): regime-agnostic, concrete statements.
  - Q4 (A): a public-key headline, plus the optional secret-key unit F7.
  - Q5 (A): worst-case, every-coin correctness.
  - Q6 (A): decryption through the `C·G⁻¹(⌊q/2⌋·e_{n+1})` column with `Regev.decrypt`.
  - Q7 (A): the product-chain lemma is in phase 5.
  - Q8 (A): concrete hybrids now; the `NUPPT` bridge later.
  - Q10 (A): reuse `Lossy.gadget` in place.
  - Q11 (A): a GSW-local `columnHashParameters`, disclosed.
  - Q12 (A): BV14 for phase 7.
  - Q13 (A): Barrington as its own complexity unit.
  - Q14 (A): ingest GSW13 in the statement PR.
  - Q15 (A): weak circular security as an explicit hypothesis.
  - Q16 (A): the LWE gap as a ratio predicate.

**Next:**
1. Move the drafts to the ruled paths and namespace.
2. Compile them in Lean, one module at a time, when an olean tree is free.
3. Open two PRs: the `DAGCircuit.lean` owner PR (Q2) and the GSW statement PR (phase 5).
4. Stage a Codex statement gate for each.

The PDFs still needed for later phases are Barrington (JCSS 1989) and BV11 (FOCS 2011 / ePrint 2011/344), and ACPS09
only if small-secret LWE is to be proved rather than assumed.

## Addendum (Seyoon, 2026-11-16)
- **Sources received; the PDFs are not committed.**
  - Barrington, "Bounded-Width Polynomial-Size Branching Programs Recognize Exactly Those Languages in NC¹",
    JCSS 38(1):150–164, 1989. It is a 15-page scan with no text layer, so read it as page images.
    SHA-256 `06fd3eeccecf8e3e42c0e33f50356588ea9377b2f7d2642b4d3e0370f4ca7831`.
  - Brakerski–Vaikuntanathan, "Efficient Fully Homomorphic Encryption from (Standard) LWE", FOCS 2011, 39 pages.
    SHA-256 `d3e95f9b9e017ea1133064bed227981ec21e38ee6fc6163eb08585dd238b0c00`.
- **ACPS09 is not needed now.** Seyoon is happy to **assume small-secret LWE** for now, and to prove the equivalences
  with standard LWE later. Phase plans state small-secret (normal-form) LWE as an explicit assumption (A3) wherever
  it is used.
