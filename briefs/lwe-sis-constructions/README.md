# LWE/SIS construction campaign: working records

Read `../../LatticeCryptographyPlan.md` for approved scope, architecture, source locations,
parameter obligations, ownership and phase gates.

## Current checkpoint

The first source drafts introduce finite-seed scalar noise, explicit LWE/SIS numeric
parameters, the common-secret LWE sample map, the integer SIS solution relation and
concrete decision/success experiments. Every public definition has an owner-side
reading lemma. There are no new axioms, nontrivial proof fills or admissions in these
drafts. This is a source observation, not an elaborated axiom attestation.

The source drafts have not yet been checked with Lean. They are not an issued statement
gate and are not evidence that an asymptotic assumption, sampler, encryption scheme,
hash family, PRG, trapdoor function or CCA2 theorem has been completed. Canonical
encodings, polynomial schedules, machine interfaces and the asymptotic assumptions
remain phase-0 work.

`check_finite_models.py` independently checks small-instance conventions: one common
secret, strict decoding boundaries, correctness with bounded errors, integer SIS
nonzeroness, collision differences, and universality of binary-subset linear hashing
including a composite modulus. It is not an interpreter for the Lean definitions and
does not prove security or replace native elaboration.

No existing shared API, root export or existing facade has been changed. New LWE/SIS
facades exist as drafts; the two proposed root imports are recorded in the plan for a
separate export commit. No external worker, audit or fill has been dispatched. The
shared exchange checkout has not been used.

## Environment

The installed Lean executable reports version 4.25.0. Shell DNS blocks source/cache
retrieval from GitHub and the official Regev host. Process inventory through `ps` is
denied by the execution sandbox; the state of other native/cache jobs is unknown.
Heavy verification remains deferred. Only source and lightweight finite-model/static
checks have been run. No other checkout's packages or scratch oleans have been changed
or used as this branch's build objects.

## Worktree isolation

The current branch is `cryptography/lwe-sis-constructions` in
`tcslib-crypto-parallel-kickoff/`. The maintainer's `tcslib-pass-shelat-ch2-4/` remains on
`cryptography/pass-shelat-ch2-4`; the frozen integration and S2 worktrees retain their
original branches. The branch rename and fast-forward were performed in this worktree
only, and `git worktree list --porcelain` confirmed the separation afterward.

**Not yet clear to merge — drafts need isolated native verification and the remaining
phase-0 surface before an external statement gate.**
