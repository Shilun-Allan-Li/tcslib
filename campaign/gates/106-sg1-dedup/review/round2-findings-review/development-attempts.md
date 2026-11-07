# Retained bounded-probe development

Generated-readerv1: the bare simp only eq_def attempt failed at function eta; all other direct
consumer headers/bodies in that input elaborated. v2 and expanded v3 use the already existing
eq_1 in an explicit funext equality; both pass, v3 prints all9 selected roots with standardAX.

Controlv1: generic reflection against pairDecode's whole List.brecOn body did not reduce on an
arbitrary list, even unsealed. Its two positive failures are not valid pass/fail controls.
Controlv2: local quoted type-ascription syntax failed before controls ran. Controlv3: the quoted
control goal types still had assigned metavariables when sent to kernel declaration creation.
Controlv4 fixes only that instrumentation by instantiateMVars on the goal type. It passes8
kernel-checked positive controls and fails exactly8 sealed controls. For pairDecode, point is
decode []=none, and abstract is the function on arbitrary separator suffixes, not the generic
List.brecOn defining-function equation. Other3 definitions retain complete point/abstract body
controls. Every Lean input/request/run/output is preserved; failed checker versions remain.
No unsafe reducibility override was used.

Source-review parser initially omitted two inline @[simp] source theorems (24 vs26); corrected
attribute-prefix parsing reproduces26. The failed parser/error are retained. Expanding the
matching-family review added clA5 const/cond/and after the first source catalogue. Neither the
initial six audit sites nor the later thirteen candidates are an exhaustive global debt census.
