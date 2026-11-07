**Verdict: issue after edits.** No blocker; one major and two minor findings.

Reviewed SHA-256: `b10bce43d3e151550fe8d2ac20238b81eaa905f9d0a7ae8739ed07eb135d5b36`.

1. **Major — final `Checks` prerequisites exceed supplied inputs.** In [brief-draft.md](/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/fills/shared-lemmas/s2/brief-draft.md:176), the final aggregate check imports four facades absent from the supplied order. At the frozen ancestor, its closure contains **422 library prerequisites and 144 direct Mathlib roots**. The supplied 94-module/75-root lists omit **328 modules and 69 roots**.

   Stage separate `inputs/checks-order.txt` and `inputs/checks-roots.txt`, generated at the frozen ancestor. Replace milestone 1’s second sentence with:

   > Use `inputs/order.txt` (94 modules) for the candidate bootstrap. Fetch the narrowed cache for `inputs/checks-roots.txt` (144 named Mathlib roots), which covers final verification; `inputs/roots.txt` records the 75-root candidate subset.

   Replace the first final-check bullet with:

   > Recheck the owned modules and their downstream modules in `inputs/order.txt`. Before checking `audits/pass-shelat/Checks`, build any remaining prerequisites in `inputs/checks-order.txt` (422 library modules), in its recorded order. Then check `audits/pass-shelat/Checks`. Use one `scripts/lean_check_tree.sh` invocation per module; log start/end time, return code and peak RSS, and require a fresh nonempty object.

2. **Minor — explicitly carry forward the external-fill “no sub-agents” ruling.** Handoff §2.12 records this user instruction, but the brief omits it. After the opening job description, insert:

   > Run this external fill in one Claude session, without sub-agents.

3. **Minor — make attachment-path resolution explicit.** The maintainer confirmed that issue staging will flatten the recorded unit inputs. Add after the source/delivery section:

   > All attachment paths in this brief are relative to `outbox/fills/reject-blocks-s2/` on the exchange. Its `inputs/` directly contains the files recorded under `s2/inputs/reject-blocks-s2/`, with the additional Checks order/roots lists described below. `environment-addendum.md` is the staged copy of the campaign’s external `fills/fill-environment-addendum.md`. Use absolute attachment paths when running commands from the frozen source checkout.

Ownership, public-surface freeze, five-file scope, six sketch refreshes, authorized harvest, Claude-only inbox delivery, checkpoint protocol, and escalation routes agree with the existing rulings.

Evidence limits: read-only review; no edits, dispatch, commits, pushes, Lean runs, or test reruns. All five baseline fingerprints/line counts match the ancestor; the 94-module order is topological. Audited S1-to-ancestor library/toolchain/manifest diff is empty. Recorded Names/Routes/MatcherUnsealed checks exit 0; MatcherSealed fails at the intended proof site. Routes still inherit H15’s authorized `sorryAx`; these probes establish interface usability, not completion of H15.
