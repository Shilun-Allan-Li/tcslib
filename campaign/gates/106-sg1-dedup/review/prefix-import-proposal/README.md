# One proposed Hardness import — ruling pending

An exact sealed hypothetical consumer of the existing
`polyTimeComputable_dropPrefixByLength` passes, with standard axioms.
It pairs `u x` first and `s x` second, composes the public prefix remover,
and rewrites only `Function.comp_apply`, the existing
`PrefixByLength.drop.eq_1` and public pair projection equations.
No private iteration or new reader is needed. Six ordinary definitions are
opaque before the complete header; the three default model simp unfoldings
are removed. The current toolchain/context is wt-camp at merged#230/mac4.

The proposed source change is one import of ClassNP.PolyTimePrefix in
CookLevin/Hardness, plus the existing private clA5Drop_native proof/doc repoint.
Its public/private signature, machines and all other source stay unchanged.
This is a new import in a frozen file, so START-HERE§2 requires Seyoon's ruling.
The question is pending; no actual source/import edit is made by this probe.

Drop-v1.lean.txt/.out and its exact command/hash/exit receipt are retained.
The run exited0 with0errors; the consumer uses only propext/Classical.choice/
Quot.sound. This is not a whole-Hardness compile, full seal/control pack, replay
or gate clearance. Any approved actual source change still requires those checks.
