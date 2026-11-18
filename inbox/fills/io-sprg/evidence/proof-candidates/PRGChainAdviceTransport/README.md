# Advice-law transport repair — UNRUN

Complete replacement body: `prg_chain_accept_average.proof`.

The repair3 log fails when `rw [P.kappaOfN_n] at havg` abstracts the displayed inverse parameter while `ω : PRGAdvice π (n κ)` still supplies fields at the hidden inverse parameter. The record parameter itself is `n κ`, so the rewrite cannot change its projected field types.

This candidate first transports the actual advice expectation through the existing `PRGAdvice.prodEquiv.symm` using `ProbComp.expect_sample_equiv`. The public `prodEquiv_eq` and `data_eq` readers then expose a bucket/matrix/uniform-vector product. Rewriting the inverse parameter now changes the explicit product and every dependent field together. The goal expectation is transported through the same equivalence; `prgPre_eq` consumes the reconstructed record before the inverse rewrite.

There is no new helper, sampler, algorithm, or frozen statement change. The record law remains the actual PRGAdvice law, transported by its already-published equivalence. The candidate keeps the existing comparison-vector equivalence and nuisance averaging argument.

Static checks only: one outer tactic block, no `sorry`/`admit`, maximum width 100. No Lean, source edits, Git, cache, or spawned agents. The conv/simp normalization and final equality are untested; root must validate the complete body. The diff is bound to the recorded live repair3 source snapshot and must not overwrite later root repairs.
