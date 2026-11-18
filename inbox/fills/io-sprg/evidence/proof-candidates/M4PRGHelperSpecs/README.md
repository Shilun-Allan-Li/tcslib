# Root-compatible M4 PRG helper specifications — UNRUN

M4-PRG-helper-specs.json is a plain four-row list in the existing install_helper.py
schema. It supplies name, file, candidate, marker, probe and doc; the extra fields
capture exact full-name/header/doc/body/source hashes, variant choice, dependency
order and overlap scope. The installer currently consumes only its six ordinary
fields:the extra bindings are provenance, not a claim that it enforces those hashes.
No installer, proof_step, Lean, Git, cache, source edit or agent was executed.
The pure producer only did static schema/parser/format/byte checks and an in-memory
stub insertion to verify the resulting exact full names.

| Install name argument | Owner and scope | Selected candidate |
| --- | --- | --- |
| sdCore_publicSeed | Hybrids, already INSIDE Params, before original H0-H3 doc | candidates/01-sdCore_publicSeed.in-Params.proposed.lean |
| Params.prg_verdict_prob | Reductions/PRG/Hop, BEFORE original namespace Params | preferred-MRr3 helper04 |
| Params.prg_nuisance_average | Same Hop marker, area-level qualified header | preferred typed helper05 |
| Params.prg_chain_accept_average | Same Hop marker, after helper05 | prepared helper06 |

Only helper01 was copied/adapted:the declaration token
Params.sdCore_publicSeed becomes the bare leaf sdCore_publicSeed. The body and
literal binder/result type stay unchanged, giving the SAME full name
TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.sdCore_publicSeed when placed
inside the current Params namespace. No Params.Params name is produced. The other
three headers remain qualified Params.* before the owner's existing namespace
Params command. Both source markers are unique and all four resulting FQNs were
verified by the reviewed pure declaration parser in memory.

Every doc field comes verbatim from its corresponding original declaration
comment in PRGModularity/Hop.lean.template, without paraphrasing. install_helper.py
rewraps paragraphs at width92 by design; original raw comment, inner text and
rendered comment have separate hashes so line wrapping is not misrepresented as
byte-identical. Literal candidate headers match those original template headers;
only helper01's necessary namespace token differs. The exact body hash uses the
installer's own extraction convention:outer by + newline + stripped tail + newline.

Before installation root must run/archive BOTH exact/apply probes for the required
names (all four records were absent at preparation):

- M4PRG_sdCore_publicSeed_core
- M4PRG_prg_verdict_prob_core
- M4PRG_prg_nuisance_average_core
- M4PRG_prg_chain_output_reindex_core

These are the existing isolated component-core mappings, not claims of complete
source-goal search. The chain helper's mapped probe is the explicit output
coordinate core; full image/chain/preprocessing normalization and the actual
nuisance averaging remain in its source proof. Helper04 uses the binding MRr3
bit-vector activation reader, not the previous rederived generic reader sequence.
Helper05 retains the actual G.idCore pushforward and imposes no uniform G.Idx law.

Dependency order:helper01 before the two Hybrids statistical hops; helper04 is
independent of nuisance averaging; helper05 is independent of helpers01/04;
helper06 depends on helper05. The final prg_hop consumes helpers04 and06. Only
helpers04/05/06 belong in PRG/Hop, so no backwards Hybrids→PRG/Hop cycle is added.

Use the JSON row's exact name as install_helper.py's name argument. Root's normal
reuse records and serial one-helper proof ladder remain required. The original
helper bodies/other proof files are untouched. This packet is not proof validation.
