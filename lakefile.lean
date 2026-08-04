import Lake
open Lake DSL

package «tCSlib» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "029db123ddaa"

require PFR from git
  "https://github.com/teorth/pfr.git" @ "e1095d58"

@[default_target]
lean_lib «TCSlib» {
  -- add any library configuration options here
}


meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.25.0"
