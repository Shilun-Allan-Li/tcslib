# Initial in-process metadata lookup failure

Hardness-native fully elaborated the actual source and printed standard AX for all8 changed
proof roots. The appended inventory then selected the generated private clNative_map.match_1.eq_1
from env.constants but failed env.find? on that name. This is retained as a failed complete
command, not a native PASS receipt.

Lean4.25 Environment.lean:734 defines env.constants through env.toKernelEnv.constants, while
find? at838 uses the asynchronous elaborator lookup path. Metadata now consistently looks up
constant info in the same kernel environment that supplied the enumeration, using the public
env.toKernelEnv.find?. collectAxioms already uses env.checked.get's kernel environment
(Util/CollectAxioms.lean:24–46). No constant is inserted, materialized, dropped or filtered out;
the full generated descendant set is retained. No production source/header/proof changes were
made for this instrumentation fix. All original inputs and the failed raw log remain intact.
