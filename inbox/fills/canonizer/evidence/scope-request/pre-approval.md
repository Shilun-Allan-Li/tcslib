# Scope pre-approval for the fill `canonizer` (recorded verbatim from the dispatch prompt)

The dispatch prompt of this fill (session of 2026-11-15) contains, verbatim:

> SCOPE PRE-APPROVAL (Seyoon, 2026-11-14): exactly the two rfl readers
> named in the brief's checkpoint 1 are approved, so no scope request is
> needed for them:
>   CodeFormat.lean: oneTapeFormat.serialize (oneTapeFormat.decode xs)
>     = (codeDecode xs).serialize
>   CodeSimulator.lean: oneTapeMachineFormat.serialize
>     (oneTapeMachineFormat.decode α)
>     = oneTapeFormat.serialize (oneTapeFormat.decode α)
> each by rfl beside its definitions, with a formula docstring and no
> attribute. Still include the seal probe showing each is needed. Any
> other frozen-file change still needs a scope request.

No other frozen-file change was made, so no scope request was sent.

The two readers as delivered (commit 1 of the series):

```lean
-- TCSlib/Complexity/TuringMachine/CodeFormat.lean, after `codeDecode_serialize_pad`
/-- The one-tape format's canonical serialization is that of the decoded machine:
`oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize`. -/
theorem oneTapeFormat_serialize_decode (xs : List Bool) :
    oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl

-- TCSlib/Complexity/TuringMachine/CodeSimulator.lean, after `oneTapeMachineFormat`
/-- The machine format's canonical serialization is the one-tape format's:
`oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
oneTapeFormat.serialize (oneTapeFormat.decode α)`. -/
theorem oneTapeMachineFormat_serialize_decode (α : List Bool) :
    oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
      oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl
```
