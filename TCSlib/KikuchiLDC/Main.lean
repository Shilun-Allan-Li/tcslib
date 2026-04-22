/-
  Main.lean
  Entry point for the formalization of:
    "A Near-Cubic Lower Bound for 3-Query Locally Decodable Codes
     from Semirandom CSP Refutation"
  Following Alrabiah–Guruswami–Kothari–Manohar (STOC 2023)

  Blueprint: kikuchi_ldc_blueprint.tex

  Structure:
    §2–3  LDC/Defs.lean           — Core definitions (Hypergraphs, LDCs, XOR instances)
    §4    LDC/BackgroundFacts.lean — Matrix Khintchine, binomial ratio bound
    §5    LDC/HighValue.lean       — High-value observation (Lemma 5.1)
    §6    LDC/Decomposition.lean   — Hypergraph decomposition (Lemma 6.1)
    §7    LDC/TwoXOR.lean         — 2-XOR refutation (Lemma 7.1)
    §8    LDC/ThreeXOR.lean       — 3-XOR refutation (Lemma 8.1) and sub-lemmas
    §9–10 LDC/MainTheorem.lean    — Main theorem (Theorem 9.1) and even-q bound (Theorem 10.1)
-/

import RequestProject.LDC.Defs
import RequestProject.LDC.BackgroundFacts
import RequestProject.LDC.HighValue
import RequestProject.LDC.Decomposition
import RequestProject.LDC.TwoXOR
import RequestProject.LDC.ThreeXOR
import RequestProject.LDC.MainTheorem
