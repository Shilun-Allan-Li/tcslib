# Scope request SR-02: typed views of the two bundled constructors

Status: proposed, NOT applied. Automatic approval review rejected application.

The new generic-fuel harvest elaborates and has only the standard axioms, but
the full closure seals add nine diagnostics in its new proof. Eight arise from
the hidden tape/state fields of `ModuleHost.hostTM` and `IterateFind.copyTM`;
one needs an explicit local-budget simplification. The untouched original
`polyTimeComputable_find` independently has eleven baseline diagnostics. No
existing proof or definition is changed to hide any of those findings.

Prototype 3 validates the solution with both constructors still sealed. Prototypes
1 and 2 demonstrate why whole-machine equalities and raw run equalities alone
do not repair the dependent carrier types. Every source and raw log is retained.

## Exact proposed addition

`typed-views.patch` adds 84 lines to
`TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (672 → 756):

* `Turing.ModuleHost.hostTMView`, a reducible abbreviation whose explicit fields
  are `k := K`, `State := State C M`, and the original host's underlying machine;
* `hostTMView_eq` and `hostTMView_q₀`;
* `hostTMView_step_inl`, `host_call_view`, and `host_clean_view`, proved directly
  from the existing public contracts in the same file.

It adds 22 lines to
`TCSlib/Complexity/Randomized/Build/IterateFindHost.lean` (362 → 384):

* `Complexity.IterateFind.copyTMView`, with explicit one-tape, `Fin 2` fields;
* `copyTMView_eq` and `copy_clean_view`, reusing the existing copier contract.

Every existing declaration, definition, proof, and attribute remains byte-for-byte
unchanged. There is no transition-table copy, time-bound change, new admission,
or `simp` attribute. Both proposed files remain below 1000 lines and width 100.
The risk is expansion of the frozen shared-provider/rebuild scope; the purpose
is to remove implicit type-field reads in E1 while preserving all operational
seals. Header, clash, full-source seal, axiom, lint, and replay evidence would
cover both providers if approved.

## Authorization and automatic review

Seyoon delegated judgment over exceptions while away (see
`standing-discretion.txt`). The worker interpreted this as allowing these narrowly
necessary reader additions and attempted to apply/check them. Automatic approval
review rejected the action because it requires a specific scope approval for
these two provider files. No provider mutation occurred. The exact rejection is
in `automatic-review-rejection.txt`. Specific SR-02 approval is now requested;
independent final-consumer work continues in the meantime.

Answer: PENDING.
