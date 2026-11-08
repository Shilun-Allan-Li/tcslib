# Gate06D round1: independent intake review

**Recommendation: accept the reported0-blocker/0-major D closure at the issued frozen source, with all4 minors tracked. No hidden blocker or major found.** The reviewed correction patch resolves the D findings in prose; it remains unapplied while B/C are active. This is not overall PR or proof-completion clearance.

Report:34,608bytes, SHA-256 `a13979aa9fafcad2ab77a5b33d59fdd034c5a7969fd346f44e3a70385297bcfc`. Source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, records `c81baa7712ab1b43357276ef5df138d02616c9d0`, exchange `5928e06c02b382b63b9b384db89d0458b520f351`. I read the full report as data, the actual issued pack at the records pin (not its older source-head draft), all4 frozen Randomness files/facade and the relevant model/security/PAC interfaces. The report covers the issued8 definitions/18 theorems and more than3 adversarial instances. Its unavailable-context source comparisons are disclosed rather than passed.

## Mathematical assessment

**D01 is a real sketch defect with a statement-preserving repair.** An arbitrary positive real epsilon need not supply a computable exact real-power schedule. A fixed integer `d≥2` with `1/d<min(epsilon,1)` exists, and the algorithm hardcodes this integer; no algorithm computing epsilon is required. The least integer `ell(n)` with `n≤ell(n)^d` is computable in polynomial time in unary n (even scanning0..n works for positive n). It satisfies `n≤ell(n)^d` and `ell(n)≤n^(1/d)+1`.

The proposed `P(s)=a(s^d+1)^k+s+1` is a natural-coefficient syntactic polynomial, expands even at s=0 and dominates the verifier's `a(n+1)^k` whenever s=ell(n). The published `PRG.Secure.truncate` plus `prg_expand` permit this output envelope. For each bad seed length select one bad input, defaulting to the empty word otherwise: its advice length is at most s^d. Apply the bridge to the efficient verifier `Mhat(x,y)=M(x,take_(a(|x|+1)^k)y)`. Nonuniform advice is permitted by PRG security; it need not be computable. A bounded set of seed lengths bounds all corresponding n by s^d, so infinitely many bad n give infinitely many bad seed lengths. The distinguisher need not generate G on its challenge.

**The1/12 replacement is sound.** Eventual acceptance gap at most1/12 gives success at least `2/3−1/12=7/12>1/2` for both yes and no inputs. Enumerating all seeds therefore has a strict correct majority. The report's alternative1/6 argument is also mathematically valid: a dyadic success probability cannot equal2/3; however1/12 avoids that extra endpoint lemma. The runtime is `2^ell(n) poly(n)`; since1/d<epsilon its logarithm is eventually at most n^epsilon. A fixed finite table handles the finitely many remaining input words. DTIME permits one global multiplicative constant, and `subexpBound>0` at every length lets that constant absorb their costs. None of this constructs the still-admitted enumeration/counting machine.

**D02 correctly identifies a confidence qualification, not a false theorem.** The formal (c) assumes fixed `delta<gamma≤1/2`. Weak-learning success yields prediction advantage at least gamma−delta; the displayed Lean proof eventually bounds it by half this positive gap. Negative failure parameters are impossible on the nonempty class, so their admitted syntax causes no counterexample. The report's holdout amplification calculation is sound with independent training and a fresh holdout: repeated-success and validation union bounds give the stated changed learner/edge/confidence and polynomial resource envelopes. For inverse-polynomial edges the contradiction uses (b), not merely (c)'s fixed real parameters. A literal arbitrary-real amplification schedule should be replaced by computable polynomial envelopes when constructing a machine. No such construction or fresh KV94-page comparison is claimed; the proposed module summary retains that limit.

**Extraction has no new defect under its explicitly pointwise reading.** The10-trial/fallback law has true-output probability `1−(1−q)^11`; at q=1/4 its distance from uniform is `1920005/4194304>1/4`. Both mixture components satisfy the n−2 atom bound, and n≤2 admits point-source witnesses. The n-indexed existential sampler does not establish one uniformly quantified sampler family defeating Ext infinitely often. N1's fixed-length hardcoded-table argument is valid; a literal NUPPT implementation can use a global polynomial coin budget and ignore surplus bits, rather than require a piecewise exact n−1 coin schedule. This observation is a retained semantic limit, not an additional formalized result or a reason to delete the efficient-Ext hypothesis from the frozen statement.

## D findings and proposed patch

Reviewed root proposal: `.lake/ps-maintainer/gate06-audit-intake-r1/corrections/minor-prose-corrections.patch`, SHA-256 `157964e06e8cd6da8f48ca0be44a47f5eeceebfaa412dad2b4a7ef453653bf0d`.

| Finding | Disposition of proposed D hunks |
|---|---|
| D01 | Accept: replaces the real-power module hint and complete theorem sketch with the integer-root/polynomial advice/reindexing/1/12 majority/finite-table route above. |
| D02 | Accept: states fixed failure delta<gamma and expressly leaves KV94 amplification/resource transport as additional work. |
| D03 | Accept: facade now describes extractor impossibility, PRF prediction hardness and BPP deterministic-time inclusion. |
| D04 | Accept the chosen **docstring-only** resolution: output for every tape is the exported contract; the proof's zero coin schedule is an implementation fact. No theorem strengthening is needed. |

The exact D04 text is appropriate: “The conclusion exposes coin-independent behavior; the proof chooses a witness with zero coin schedule.” The proof visibly chooses `NUPPT.ofPolyTime ... (.const0) ...`, while its public existential asserts advice and every-tape output only. Coin independence suffices for the bridge probability argument.

I independently reconstructed every hunk against exact3f Git blobs entirely in memory. All6 files have byte-identical noncomment code before/after nested block/line comment removal; the4 D paths have no proof/header/definition/admission change. `patch-check.json` records the source/proposed/code hashes. This also checks code preservation for the2 A paths; it is not an independent mathematical review of the A findings. No patch was applied and no Git index/source was written.

## Evidence and closure limits

The issued final index hash matches the report. The pinned completed seal summary records valid rc0/zero-error results for all4 primary Randomness modules. The exact all-stored axiom records retain3 direct admissions—prediction hardness, derandomization and extractor impossibility—and the derived (c) dependency:4 admitted-dependent Randomness identities, not proof completion. I inspected these records; I did not rerun their native checks or replay the auditor's finite Python suite. Its finite278-table and other calculations remain reported corroboration, never kernel evidence. I did not reverify the entire455MB common archive or independently reopen the unavailable contextual books.

This meets the issued0-blocker/0-major closure threshold for D. Root may record D closed with the4 minor resolutions/proposed patch and preserved source/access/build limits. Hold the frozen audited source while B/C are active; apply any combined correction only in the coordinated follow-up with exact source/code identity and the required source-matched checks. No library, main-record, exchange, Git, native/cache or app mutation occurred in this review; only ignored review notes are saved.

**Not yet clear to merge — the remaining Gate06 audit resolutions and unapplied corrections remain.**
