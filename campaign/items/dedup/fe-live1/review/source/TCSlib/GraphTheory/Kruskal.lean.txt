/-
Copyright (c) 2026 Harsha Polavaram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harsha Polavaram
-/

import TCSlib.GraphTheory.Kruskal.Basic
import TCSlib.GraphTheory.Kruskal.Reach
import TCSlib.GraphTheory.Kruskal.UnionFind
import TCSlib.GraphTheory.Kruskal.Exchange
import TCSlib.GraphTheory.Kruskal.Optimality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Formalizing the Optimality of Kruskal's Algorithm

## Main results

- `Kruskal.kruskal_spans`: the edge set returned by Kruskal's algorithm spans the same graph as the input edge list
- `Kruskal.kruskal_optimal`: the edge set returned by Kruskal's algorithm has minimum total weight among all spanning subgraphs of the input edge list

## References

- Original formalization by Harsha Polavaram
-/
