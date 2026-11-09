# Pseudorandomness construction map

Seyoon merged the [ElGamal relocation #262](https://github.com/Shilun-Allan-Li/tcslib/pull/262)
at `7abb6357ec92044f84c4f0735cd5f269f6054dda`. Its Lean and checker inputs match the checked ElGamal head
`85feea8b82fdef6117a6819900ec66f09e7e93bd`.

[PR #263](https://github.com/Shilun-Allan-Li/tcslib/pull/263) at `bd2b7717dea1f24b64ef50140002aed0472d6835` expands the existing pseudorandomness entry point.
It distinguishes the finite advantage bounds from the asymptotic next-bit, stretch,
and GGM results and points to the evaluator and reduction-machine contracts.
It links both private-key encryption applications. The diff changes one module
docstring. The import graph and Lean commands match the base.

- The isolated tree verifies 1,083 retained local and
  3,810 external objects. Three rebuilt modules
  reproduce their accepted object bytes. The facade, library root, and campaign Checks pass.
- The finite and asymptotic probes resolve all 21 fully qualified declaration
  names in the map. The twelve printed headline axiom sets contain no `sorryAx`.
- The plain style check has zero findings. Five identical campaign-linter findings
  on both sides refer to grandchildren reached through the imported Functions facade.
- The first runner stopped when the timing wrapper's system statistics call
  failed under sandbox restrictions. The second runner uses wall-clock timing
  and a separate tree. The first attempt is retained in the archive.

[The approved layout](../../CLEANUP-PLAN.md#pseudorandomness-and-private-key-encryption)
records the rest of the two waves. After this merge, the next slice moves the
asymptotic PRG contract into its generator module and retains the old import for
next-bit, symmetric encryption, and derandomization callers.

`facade-checks.zip` has SHA-256 `7e42eb250763cae8a700287d5c5c72cf70a41ce03de61cee7872fda0132f93f6`.

Seyoon merged the verified source at `6877e6de392894df102643d1c30e601e562d2b6f`.

**Ready to run — the next slice moves the asymptotic PRG contract.**
