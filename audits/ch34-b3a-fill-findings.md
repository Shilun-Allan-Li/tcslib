Input SHA-256: `7770623f02b3312899f936634f0164e8ab355b0e7a32d51f5aec7122e55170e2` — independently recomputed and equal to the expected digest. Exactly **49 sections**, counted by the prescribed headers.

**B3a fill-gate verdict: 0 blockers, 0 majors, 3 minors. The stated closing criterion is met.** Both realizations satisfy the frozen statements and the sanctioned routes. This is not a blanket verification of the delivery’s execution history: the missing evidence and limits of reproduction are identified below.

Paths in the findings table are relative to `TCSlib/Complexity/` unless they begin with `audits/`, `briefs/`, or `backlog.md`. Source line numbers refer to the extracted file, excluding the bundle’s Markdown fences. I did not modify the input or repository, and did not rerun Lean; the commissioned kernel-check premise and supplied replay/axiom evidence are used as such.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `audits/ch34-b3a-fill-pack.md` · bundle completeness and screen reproduction | The bundle does not contain every screen-population file, and its attached source population is not the historical B3a screen snapshot. | All 24 B3a population files are present, but **42 of the 66 union-population files are absent**, including `Build/Convention.lean` and `SpaceComplexity/ConfigGraph.lean`. Parsing the supplied 24 files with the supplied screen gives **1,245** qualifying declarations; substituting the attached `Constructible` base gives **1,230**, versus the historical **1,243 / 1,228**. Thus the original full screens cannot be independently reproduced from these source snapshots. `Cfg.ofWords` itself is absent, so its exact comparison is unavailable. | Record a pack erratum; supply the historical 24-file snapshot or its non-owned-file deltas, the other 42 union files, and the exact pinned `Convention.lean`. Distinguish reproduced results from historical logs. |
| 2 | minor | `audits/ch34-b3a-fill-pack.md`; delivery report · execution evidence | The claimed evidence completeness exceeds what this audit packet supplies. This does not show the original ZIP was incomplete or the executions failed. | `delivery-SHA256SUMS.txt` has 27 entries, but only **five payloads** can be matched directly in this packet: the report, owned source, population list, and two screen logs; all five hashes match. The reported `evidence/Sanity.lean`, `logs/sanity.log`, pre-ship probe/log, 113-module sweep logs, git bundle, and original format-patch are absent. A checksum manifest does not establish the contents or execution of missing files. | Attach the sanity source/log and original verification records, or explicitly restrict the packet’s completeness claim. Preserve the independent 41-module replay and gate axiom logs already attached. |
| 3 | minor | `backlog.md` F6-1(b); `audits/fills-6-integration.md` · proposed retirement of `b3a_seam_space` | Simply substituting the existing additive Seam lemma is not a valid resolution at the final emitting call. The delivery report correctly identifies the missing generality. | `Seam.lean:423` and `:447` require a second-phase run ending at **live** `Cfg.ofWords q₂ w₂`. `Constructible.lean:179` has no such endpoint hypothesis and is used at a genuine halt, whose state is `none` and output is nonempty. The public **general** visited-set theorem at `Seam.lean:583` does apply, and the helper cites it before elementary cardinality and sum bounds. | Correct F6-1(b): promote the general-configuration additive corollary and derive the canonical corollaries from it, then replace the private helper. This can wait for the shared-file window; it is not an undisclosed reimplementation of the seam controller or its trajectory proof. |
| 4 | note | `Constructible.lean` · freeze, scope, imports | **No findings.** | Applying the attached cumulative patch to the attached base reproduces the 538-line head byte-for-byte. Git blob hashes match the patch (`22972eb0…` → `579cf63c…`). `SpaceConstructible` is byte-identical; both theorem signatures and all original declaration prose are unchanged. Exactly 15 privates were added; the same three publics remain. The four added imports, two flagged appendices, and status-heading change are sanctioned. `Machines.Bin` imports only Mathlib. | None. The earlier P4.1-to-base equality, ancestry, authorship, and complete import-closure history remain maintainer attestations; their repository objects are not supplied. |
| 5 | note | `Constructible.lean:517` · `spaceConstructible_linear` | **No findings.** The main realization satisfies P4.1 minor 2. | Catalog prepending followed by `bufferedCompTM_computesInTime` runs the length counter on `true :: x`, hence emits `Nat.bits (n + 1)`. Dominance includes `n = 0`. The exact time inequality and positive multiplier are verified below; `spaceUsed_le_mul_succ` counts initial, intermediate, boundary, and final head positions. | None. |
| 6 | note | `Constructible.lean:66–82,202–458,485` · logarithmic realization | **No findings.** The main realization satisfies P4.1 minor 1. | The positive-only binary-width identity is not applied at zero. R8.5c starts at native input position 1 and its actual entry state; its framing and first-exit cut are retained. The four-step writer yields `true :: (Nat.bits n).tail`. The virtual handover is explicitly identified with `vhostCfg (initCfg y) true 1 []`; its fresh bank is disjoint from the native scratch bank. Both nested seams use their first-exit cuts. The final forwarded output is `Nat.bits (logSpace n)` at a genuine halt, including any halting emission. | None. |
| 7 | note | `Constructible.lean:156–197,224–246,275–282,412–458` · space ledgers | **No findings.** | The native radius becomes an inclusive interval cardinality; the writer is bounded by two cells; Z1 includes both buffer clamps and the source bank; relocation includes every unused tape’s initial cell. Summing the phase bounds gives the stated `A * (logSpace n + 1)` allowance, then `2 * A * logSpace n`. See the calculation below. | None. |
| 8 | note | `Constructible.lean:113–121,179–197` · duplication ruling | **No failure-mode-5 major established for either named item.** | `b3a_seam_space` is a disclosed general-configuration corollary of the already-public trajectory theorem, with a genuinely weaker endpoint requirement than the existing additive corollaries. Its remaining proof is finite-set cardinality and finite-sum algebra. `b3a_cfg` is a four-line specialized configuration constructor and `b3a_cfg_map` is `rfl`; this is not wholesale duplication of a proved machine routine. The exact claimed equality with `Cfg.ofWords` is **not certified**, because its defining file is missing (finding 1). | Generalize/promote the seam corollary as in finding 3. Consider defining the small configuration wrapper through `Cfg.ofWords` once the missing comparison is supplied. Neither requires immediate factoring to establish these two results. If later evidence establishes substantive duplicated proved material, the template’s human-acknowledgment rule applies; a backlog entry alone would not waive it. |
| 9 | note | `audits/logs/ch34-b3a-1-screen-{before,after}.txt`; combined screen | **No findings in the recorded pair lists or independently checked B3a comparisons.** | The historical pair lists are byte-identical: 1,520 rows totaling 597,328 reproduced characters, with declaration counts 1,228 → 1,243. Both complete lists embedded in the report match their separate logs. The union log has 2,464 rows totaling 783,700 characters and no pair involving `Constructible.lean`. Independently applying the supplied extraction/tiling functions to every eligible pair involving `Constructible` in the attached 24-file population finds **zero pairs**. The snapshot and coverage limitations are finding 1. | None beyond finding 1. A negative text screen is not a semantic-duplication certificate. |
| 10 | note | `audits/logs/fills-6-replay.log`; gate axiom probe/log; downstream walks | **No findings in the supplied kernel and downstream evidence.** | The replay lists 41 modules, all `exit=0 errors=0`; `Constructible` has `sorry=0`. The gate probe enumerates 23 public axiom prints and 23 matching walks. Both targets have exactly `[propext, Classical.choice, Quot.sound]` and empty walks. Private censuses report 47 `Constructible` and 57 `ConfigGraph` constants, with no direct `sorryAx` users. Both S1b corollaries’ walks contain only `NSPACE_subset_exp_dtime`; the four `Hierarchy` rows contain themselves. The broader integration log agrees. | None. These are checked log/probe correspondences, not independently rerun kernel results. The missing `ConfigGraph` source limits independent validation of the “every public” census. |
| 11 | note | `Constructible.lean` · documentation; style and delivery records | **No findings in the delivered documentation or reproducible integrity checks.** | All 15 new privates have docstrings; the substantial glue proofs have sketches matching their roles. Both appendices describe the actual sanctioned refinements; the original sketches are preserved. The constant-slack discussion does not revive an exact-space refutation. The style log reports `0 FAIL, 4 WARN over 45 files`, with existing size warnings in other files. The owned-source hash matches the delivery manifest, and the patch adds no execution hooks or references to the environment shim. | None. “The shim was never compiled or run” is accepted only as a maintainer-replay attestation: the delivery report explicitly says the agent used it. Full delivery integrity and the 113-module execution history are subject to finding 2. |

The duplication ruling does **not** treat rewording a copied proof as a defense. It rests on the actual contract difference and the fact that B3a consumes the public general trajectory theorem rather than reproving it. The old additive corollary’s final-state requirement cannot be discharged by rewriting a halted configuration: its state would have to be both `none` and `some q₂`.

Reading the definitions directly gives the following restatements:

| Definition | Mathematical meaning |
|---|---|
| `SpaceConstructible S` | `S` dominates `logSpace` pointwise. There is one positive natural constant and one fixed finite Boolean-tape machine such that, on every input, it halts with the little-endian binary representation of `S` of the input length, and the total number of visited work-tape cells up to that halt is at most the constant times that value of `S`. Input and append-only output storage are excluded. The machine and constant precede the universal input quantifier. |
| `b3a_word n` | Replace the first binary digit of `n` by `true`, or create the singleton `[true]` when its digit list is empty. |
| `b3a_cfg s x w` | A live configuration in state `s`, with native input `x` at position 1, word `w` buffered from cell 0 on work tape 0, all other work cells blank, every work head at 0, and empty output. |
| `b3a_virtualSelect K m` | An injection from the virtual host’s buffer-plus-`m` tapes into `K + 1 + m` tapes: index 0 maps to 0; every positive index maps to `K` plus that index. Thus its source bank occupies the tapes after the native counter bank. |

These meanings agree with the delivered prose and the frozen P4.1 interpretation. No definition has been weakened during the fill. This audit does not reopen the already-closed textbook-fidelity gate.

For the linear ledger, using the report’s notation,

\[
\begin{aligned}
t+1
 &=a(n+1)+(n+1)+3+b(n+2)\\
 &=(a+b+1)n+a+2b+4,\\
(a+2b+4)(n+1)-(t+1)&=(b+3)n\ge0.
\end{aligned}
\]

Consequently,

\[
\begin{aligned}
\operatorname{spaceUsed}(M,x,t)
&\le M.k\,(t+1)\\
&\le M.k\,(a+2b+4)(n+1)\\
&\le\bigl(M.k\,(a+2b+4)+1\bigr)(n+1).
\end{aligned}
\]

The final coefficient is positive even without separately requiring positive Catalog constants. Dominance is
\(\operatorname{logSpace}(n)=\operatorname{Nat.log}(2,n)+1\le n+1\), giving exactly \(1\le1\) at zero.

For the logarithmic ledger, retain the report’s constants
\(B=(K+1)(2C+1)\), \(k=K+1+L.k\), and \(A=k(B+b+8)+1\).
The native counter’s per-tape inclusive interval has
\(2C(\operatorname{length}(\operatorname{Nat.bits}(n))+1)+1\) cells; summing gives at most \(B(\operatorname{length}(\operatorname{Nat.bits}(n))+1)\).
After relocation, the three phase bounds sum to

\[
\begin{aligned}
&k\bigl(B(\operatorname{logSpace}(n)+1)+1\bigr)+3k
 +k\bigl(b(\operatorname{logSpace}(n)+1)+\operatorname{logSpace}(n)+3\bigr)\\
&\quad=k\bigl((B+b)(\operatorname{logSpace}(n)+1)+\operatorname{logSpace}(n)+7\bigr)\\
&\quad\le\bigl(k(B+b+8)+1\bigr)(\operatorname{logSpace}(n)+1)\\
&\quad=A(\operatorname{logSpace}(n)+1)
 \le2A\operatorname{logSpace}(n).
\end{aligned}
\]

The penultimate inequality has nonnegative slack
\(k(7\operatorname{logSpace}(n)+1)+\operatorname{logSpace}(n)+1\).
The last uses \(\operatorname{logSpace}(n)\ge1\).
The emitter bound uses the public Z1 allowance
\(b(\operatorname{Nat.size}(\operatorname{length}(y))+1)+\operatorname{length}(y)+2\),
then \(\operatorname{Nat.size}(\operatorname{length}(y))\le\operatorname{length}(y)=\operatorname{logSpace}(n)\),
and the embedding’s extra unit allowance. No input-head movement is charged as work space; all work-head boundary cells are included.

Adversarial cases checked from the definitions and supplied contracts:

| Case | Result |
|---|---|
| Empty input | `Nat.bits 0 = []`; overwriting produces `[true]`, whose length is `logSpace 0 = 1`. Both constructed functions output `Nat.bits 1 = [true]`. |
| Input length 1 | The logarithmic function outputs `[true]`. The linear construction counts a virtual input of length 2 and outputs `[false, true]`. |
| Width change, `j ≥ 1` | `logSpace (2^j - 1) = j` and `logSpace (2^j) = j + 1`. The corresponding linear values are `2^j` and `2^j + 1`; the first requires the new digit. Neither route assumes a nonoverflowing fixed-width counter. |
| Halt during emission | The forwarded run preserves the entire source output when the state becomes `none`; no output-free live-seam assumption is imposed on the final endpoint. |
| No virtual source work tapes | The selection still maps the one buffer tape correctly when `m = 0`; unused relocated tapes contribute one initial cell each. No hidden positivity requirement on the source bank is used. |

These are independent mathematical checks, not claims to have executed the missing sanity probe. The generic space ledgers and source contracts establish the cases without introducing new axioms or changing either target.

**Notation glossary.** `x` is the native Boolean input and `n` its length; `S` is a proposed space bound. `M` is the linear composite machine; `a,b` are the Catalog time constants, with `b` also bounding the length counter’s space, and `t` is the linear time budget. `L` is the Catalog length-counter machine. `K + 1` is the native counter’s tape count and `C` its radius constant; `B,k,A` are the displayed logarithmic-ledger constants. `y = b3a_word n`; `s` is a live control state, `w` a buffered word, and `m` a virtual source-bank size. `j` indexes a power of two; `q₂,w₂` denote the canonical additive Seam lemma’s final live state and word assignment. `spaceUsed(M,x,t)` abbreviates the source expression `M.tm.spaceUsed (M.tm.initCfg x) t`. Existing Lean identifiers retain their source meanings.
