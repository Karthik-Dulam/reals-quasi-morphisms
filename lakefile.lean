import Lake
open Lake DSL

package «reals-quasi-morphisms» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib RealsQuasiMorphisms

lean_lib Util
