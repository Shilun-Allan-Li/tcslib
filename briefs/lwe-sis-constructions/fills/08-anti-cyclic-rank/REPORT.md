# Anti-cyclic rank proof checkpoint

The two rank obligations are filled at `75a4214dc098cd6c363d00c34f569bac23eb4555` on draft #250. The baseline
is the passed Gate 12 intake `ce421a2f5e4abf50b776c190a95788ce926494f0`. Both frozen signatures
are preserved. The sole changed Lean file is `AllButOne/AntiCyclic.lean`.

The proof identifies the power-of-two cyclotomic polynomial and uses the
existing Mathlib quotient field and power basis. Reindexing the coefficients
by a row shift gives the power of the adjoined root for that row. A wrapped
index gives the minus sign because the width-th power is minus one. The
matrix transpose acts on the integer coefficient vector as multiplication
by the field element that defines the matrix. Cancellation in the field proves
injectivity. A zero difference of branch bits would make the branches equal.

This is the integer transpose of the row action in PW10 §6.4, printed page 38.
The proof also includes width one. The author PDF and the consumed page
reproduce the existing source fingerprints. [PW10 §6.4](https://sites.cc.gatech.edu/fac/cpeikert/pubs/lossy_tdf.pdf#page=38) ·
[Source manifest](../07-sis-trapdoor/pw10-primary-source.json)

| Check | Result |
|---|---|
| Freeze | Two proof bodies filled and two precise Mathlib imports added. All six declaration signatures and 152 other frozen paths match. |
| Affected scope | All four affected modules passed serially in 14.513 seconds. Two pre-existing admissions remain in `AllButOne.Basic`. |
| Type checks | 216 exact representations match Gate 12. Four representations use the imported normed integer ring projection. The kernel accepts reflexivity certificates for all four old and new types. |
| Axiom probe | Both fills and eight backing contracts use only standard axioms. Two compiler auxiliaries from the rank proof are inventoried. |
| Style | 0 failures and 0 warnings over 7 files in the trapdoor scope. |
| Cache | 178 missing archives restored for the cyclotomic import, totaling 7,636,276 bytes. The existing package sources and pins are preserved. |
| Merge preview | Tree `24893d9e331156531305009e37ab2b41ecd46603` at target `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` preserves the checked library and pins. |

The affected checks use a separate object tree with prerequisites from this
worktree's Gate 12 build. The full fresh sweep and independent review belong
to the next combined proof batch. The temporary development assumption was
replaced by Mathlib's rational cyclotomic irreducibility theorem. The final
probe uses the corrected theorem namespace. The proof reuses Mathlib's basis
and adds only the two filled bodies and precise imports.

The nine counted-loop consumers and seven gadget and inversion obligations
remain. The exact `Randomized.blockVal_eq` proposal still applies to the
shared owner and awaits approval. [Reader proposal](../../gates/08-construction-statements/proposed-random-bits-reader.patch)

**Not yet clear to merge.** Sixteen admissions, the next proof audit, scoped
source matching, and landing checks remain open.
