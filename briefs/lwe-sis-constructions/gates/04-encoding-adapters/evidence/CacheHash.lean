import Cache.Hashing

open Cache Cache.IO Cache.Hashing Lean System

-- Only the selected Mathlib root and its dependencies are hashed.
#eval CacheM.run do
  let name := `Mathlib.Computability.Language
  let path ← Lean.findLean (← read).srcSearchPath name
  let (_, memo) ← (getHash name path).run { rootHash := ← getRootHash }
  let entries := memo.hashMap.toArray.map fun (mod, hash) =>
    Json.mkObj [("module", Json.str mod.toString), ("archive", Json.str hash.asLTar)]
  IO.FS.writeFile "briefs/lwe-sis-constructions/gates/04-encoding-adapters/evidence/required-root-hashes.json"
    (Json.compress (Json.arr entries))
  IO.println s!"Hashed {entries.size} selected dependency modules"

