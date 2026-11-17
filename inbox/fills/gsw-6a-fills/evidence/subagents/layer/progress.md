# layer (U7, NANDLayering N7-N13) progress

## Plan (written before the seed, from the module docstring's column invariant)
No private def. N = n + n, D = C.depth, F v = (List.range v).foldl C.layerColumn ([], []).

Structural part (no C.layerNAND; N12/N13 must not reach N1):
- chain lemmas on `layerChain` by induction on the link count: `.1 = gs ++ ext` with every ext gate
  `⟨.not, [w]⟩` and `|ext| = 2s`; `|.2| = s`; acyclicity (GatesAcyclic via gatesAcyclic_iff,
  GatesAcyclic.snoc) and `.2` entries below the vertex count.
- `layerAt_lt`: every recorded copy (or default 0) is below a bound that bounds all columns.
- step lemma `layerColumn_struct` (one case split over layerColumn_eq): shape `(s.1 ++ ext, s.2 ++ [col])`,
  acyclic, column entries in range, hC -> new gates IsNAND, |ext| <= 2D+1.
- fold lemma `layerFold_struct` by induction on v (List.range_succ, List.foldl_append).
- N12 = gatesAcyclic_iff.mp at v = n + |gates|; N13 = layerAt_lt.
Semantic part (on C' = C.layerNAND, gates through layerNAND_gates; F v's gates a prefix of C'.gates):
- readers at a gate of a prefix: C'.depthAt (N + |gs|) = 1 + foldr max (via depthAt_gate, depth_eq,
  depthAt_eq) and, under hC, value = NAND (values_getD_gate, eval_of_isNAND N1).
- generic chain lemma for a vertex predicate P w k; P_u w k := C'.depthAt w = k ∧ (hC -> ∀ x, value of w
  on litInput x = value of u on x).
- step + fold lemma: every live processed u, every level d u ≤ k ≤ D: P_u (layerAt cols u k) k; every
  gate has all its args at one depth (gives IsLayered with List.max_le_of_forall_le / le_max_of_le).
- N7, N10 at the output; N8 from the uniform-args part; N9 from the structural IsNAND part; N11 from
  the length part and size_eq.
2026-11-17T11:35:41Z N12, N13 proved (structural helpers, no layerNAND use); file compiles rc 0 (NL-005), 5 sorry targets left
2026-11-17T11:41:36Z all 7 targets proved (NL-011 rc 0, 0 sorry); file too long, compacting next
2026-11-17T11:54:04Z FINAL: all 7 targets proved; NL-019 rc 0, 0 warnings; 944 lines (base 388), width<=100; seal probe SealNL-002 ok, control fails once; axioms AxNL-002 (sorryAx only via N1 in N7/N8/N10; layerNAND/_gates/_output clean)
