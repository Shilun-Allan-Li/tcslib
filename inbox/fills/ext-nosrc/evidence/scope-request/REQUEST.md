# Scope request: direct helper imports in frozen facade

The issued brief permits helper modules under Extraction/ and forbids editing every other
file. Its required whole-Cryptography lint recursively checks Randomness.lean and reports
that it does not directly import Extraction.Rejection and Extraction.Sampler, although it
imports Extraction, which precisely imports both helpers. Existing check_facade computes
a grandchild facade at child.parent/(child.parent.name + ".lean"), so it does not recognize
the repository-standard sibling Extraction.lean as covering those helpers.

The attached two-line patch adds the two direct imports to Randomness.lean. It is a concrete
proposal only; the frozen file in the proof checkout is unchanged. The proposed import graph
has the same transitive contents. A source-only lint overlay validates it independently.
Approval is requested either to include these two imports in the fill scope or to waive these
two false-positive lint findings; no statement weakening or global simp change is involved.
