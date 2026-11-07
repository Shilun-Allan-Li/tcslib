# S2 final internal workflow/evidence review

Status: **0 blockers, 0 majors, 3 minor documentation findings.** The pinned workflow evidence is internally consistent. This is a static evidence review, not acceptance or a native replay.

Reviewed exchange payload: `7a2e14829e0f2c43aae20b249f90e838822a7dc1`.
Frozen ancestor: `31348fcf7dee32f84db1fc8f929d80653137995e`.
Delivered source head: `125a29633892daebde9fbad46a131d5b66febbb7`.
REPORT SHA-256: `0ba3e76869da060f190a48de04ce3efbd34c44a58909ef08e0b5ea3bbec32f47`.
Archive SHA-256: `f0cd4239b8ac1fac0f1f0d74fe9d7566217692f58fc5f8df84466a5888813109`.

The campaign archive is `briefs/pass-shelat-ch5-8/fills/shared-lemmas/s2/final/payload.tar.gz`. All 101 archived files equal the pinned exchange Git blobs. All 101 manifest size/SHA-256/Git-blob entries match. Own in-memory application of all four format patches from the issue ancestor reproduces all five delivered sources. The fourth patch changes only the private `rsa_unitAcc_poly` sketch; the other four files are byte-identical to checkpoint 4.

## Minor findings

1. **MINOR-1 — stale module inventory:** `src/TCSlib/Cryptography/Candidates/Concrete.lean:85` still says “host H15; statement only, its proof is an open fill.” Replace with “host H15; proved via the repetition host.”
2. **MINOR-2 — sampler sketch typo (also present at checkpoint 4):** `src/TCSlib/Cryptography/Candidates/DiscreteLog.lean:678` says “The output is the last `|t|` bits of”. Replace `|t|` with `|p|`: the proof drops `|t|` from the padded word of length `|p|+|t|`, leaving `|p|` bits.
3. **MINOR-3 — exact source identity in REPORT:** `REPORT.md:17–21` uses abbreviated source heads although the brief asks for exact ancestor/head. Replace final `125a2963` with `125a29633892daebde9fbad46a131d5b66febbb7`; preferably expand the milestone/series hashes too. Full patch headers and `seal-summary.json` already supply the missing exact values, so this is presentation, not lost provenance.

## Replay, counts and axioms

Own parsing finds successful `rc=0` plus `fresh-nonempty=True` records covering **94/94** candidate modules and **422/422** Checks prerequisites. The 328 extra prerequisites appear exactly once in their issued order; the 422-module order has no direct TCSlib prerequisite violation. Their source imports and transitive closure contain no owned module.

The two final prerequisite logs contain **337** completed checks: 328 additional prerequisites, eight owned/downstream modules, then Checks. All have rc 0 and fresh-object confirmation; summed wall time is **4036.9 s**, maximum RSS **3599 MiB**. Checks is **137.2 s**, rc 0, fresh, with no error diagnostics. The initial bootstrap has 94 starts/93 completions; the missing facade completion is disclosed and its later successful check is present. No unsupported clean-bootstrap claim was found.

Own lexical census over the ancestor's **1069** TCSlib Lean files with the five-file overlay yields `sorry 511→510`, `admit 0→0`, `axiom 0→0`, `sorryAx 1→1`; owned `sorry 1→0` and all four final owned counts zero.

The **57** touched/generated axiom rows equal the collector log and contain only standard axioms: 20 all three, 20 `propext/Quot.sound`, three `propext`, 14 none. The checkpoint-4 module walk contains **1280** unique module/name rows, all standard-only. This remains relevant at final because patch 4 is comment-only.

Independent parsing of the actual Gate08 round-2 base Checks log and the delivered final Checks log reproduces the **equal 367-record multisets**, each over 364 names; 364 dependency-bearing records over 361 names and four unchanged sorryAx records. Base log SHA-256 is `467c442e866d2c5c7846dc49eb6689f908c939bb807d84178c90c6136e155fc8`. No base Checks rerun on the worker host is claimed.

The prerequisite drivers pipe `chkS.py` through `grep ... || true`; their shell completion alone is not a pass certificate. The positive conclusion above uses the individual end/status/fresh records. A robust native driver should preserve subprocess failures.

## Collector and whole-file seal coverage

Read `S2Collect.lean:16–103` as source only. It selects touched private/generated descendants via user names, and separately roots every constant using `["*"]`. Types and root values are inspected; traversal follows dependency types and own definition values. No touched-not-found warning occurs. Touched roots total 57; whole-module constants are 125/145/220/314/488.

Own recomputation of source import closures matches the recorded 61/80/88/69/71 modules. The conservative ordinary-definition lists contain **830/1236/1335/984/1060 = 5445 pairs**. All stored foreign ordinary reads are covered except the explicitly documented `PolyExpr.eval` exclusion. Instances, reducible non-matchers and `glNeed` retain the issued methodology's exclusions.

**Critical placement check:** there is no proof or anonymous command before any real seal. In all five files, the prefix consists only of imports, three options, module prose, the initial outer namespace and its open command. Seal start/end lines in probe copies:

| file | seal start | seal end | active | already irreducible |
|---|---:|---:|---:|---:|
| Concrete | 101 | 126 | 830 | 0 |
| DiscreteLog | 114 | 139 | 1218 | 18 |
| ElGamal | 107 | 132 | 1317 | 18 |
| RSA | 85 | 110 | 984 | 0 |
| Rabin | 77 | 102 | 1060 | 0 |

Each outer namespace stays open through the last source command; nested sections/namespaces do not close that outer scope. No later source attribute changes or anonymous commands were found. The ten head/ancestor probe sources equal their corresponding originals modulo exactly the seal insertion and one blank line.

All ten installed spelling arrays equal their collector sets, with no duplicates. The harness resolves unique actual Names from the environment, verifies post-install irreducibility, counts already-irreducible names separately, and contains no unsafe override. Delivered logs contain the expected single status marker each; every source error is strictly after the seal command, so no attribute/name-resolution diagnostic was counted as a proof failure.

Head and ancestor have the same **1/3/0/1/2** diagnostics and the same five failing declarations: `primesPairEquiv_apply_val`, `ExpGroupGen.FullLength.exists_fullLengthExcept`, `rsaTrapdoor_oneWay`, `rabinCollection_index`, `rabinBlumTrapdoor_index`. No head-only or touched failure is reported. Their classification remains source-identical inherited debt from the issue ancestor; no whole-file exemption is inferred.

The report openly limits ancestor probes to ancestor source copies against current imported owned-module objects. They are not a rebuilt full ancestor environment. Public source bodies are frozen, and the only final-vs-checkpoint change is a comment, but maintainer native checking must retain that distinction.

## Controls and explicit lists

The anonymous narrow control succeeds unsealed and fails sealed at `rfl` **3:135**. The full-RSA-list control succeeds unsealed and fails at **28:135**, with `primeStr` confirmed in that list. The repetition-matcher control succeeds unsealed and fails at **7:52**, with the actual matcher present in Concrete's list. These are proof-site errors; none is an attribute error. The delivered matcher sources match the staged control form.

The recorded explicit-list scan covers exactly the **37** touched names, with **92** tactic occurrences and **121** distinct identifiers, including multiline lists. Inspection of the actual proof snippets found no config/parenthesized argument form bypassing that scanner. Resolved non-theorems are all same-file definitions. Unresolved names are own private declarations, locals and `show` terms; no obvious explicit foreign ordinary/Core/Mathlib definition item was found. This is static review plus delivered name-resolution evidence, not independent Lean syntax analysis.

Style logs correctly retain rc 1 and four inherited size findings on both sides. Campaign/plain and check8b each report 0 FAIL/12 WARN. The four oversized files shrink; Concrete remains below 1000 lines. No clean-style-exit claim is made.

## Native confirmation and limits

Root should retain its serial native replay and confirm the reconstructed exact source, all owned/downstream modules and Checks; regenerate collector/axiom/census/header evidence; and re-elaborate head/ancestor seals and the controls with status and source hashes. Acceptance must distinguish inherited failure classification from a clean whole-file seal pass.

No delivered tool was executed. This review used own read-only Git/archive/hash/parse analysis; no Lean, cache, apps, Git mutations, source edits or worker contact occurred. One session/no subagents, prior cache provenance and absence of unrelated concurrent Lean processes remain worker attestations. The prior checkpoint-4 mathematics/header/scope review is retained; this invocation does not claim a new native or full mathematical review.

**Not yet clear to merge — maintainer native confirmation and delivery acceptance remain pending.**
