import Mathlib.Tactic.Zify          -- for `zify` tactic
import Mathlib.Data.Int.Order.Basic -- for `Int.coe_natAbs` lemma

/-! # Basic notation/tactics specific to the integers. --/

namespace Int.natAbs            -- restrict them to a namespace

/- This conflicts with match-case notation. -/
-- 	local notation (priority := high) "|" x "|" => Int.natAbs x
/- This is copied with modifications from Mathlib.Algebra.Abs. -/
/-- Use absolute-value notation specifically for `Int.natAbs`.

This is the only absolute-value-like function used in this project, so
this is extremely convenient. -/
scoped macro:arg (name := «notation») (priority := default+1)
  atomic("|" noWs) x:term:min noWs "|" : term => `(Int.natAbs $x)

/- This should make the pretty printer use this notation.
Copied with modifications from https://github.com/leanprover/lean4/issues/2045#issuecomment-1396168913. -/
@[scoped app_unexpander Int.natAbs]
private def unexpander : Lean.PrettyPrinter.Unexpander
| `($_ $n:term) => `(|$n|)
| _ => throw ()

open Lean.Parser.Tactic (simpArgs location) in
/-- Custom `zify` tactic which does not convert `Int.natAbs` to `abs`. -/
scoped syntax (name := customZify_notation)
  "custom_zify " (simpArgs)? (ppSpace location)? : tactic

/-- Custom `zify` tactic which does not convert `Int.natAbs` to `Int.abs`. -/
macro_rules (kind := customZify_notation)
| `(tactic| custom_zify $[[$simpArgs,*]]? $[at $location]?) =>
  `(tactic| zify $[[$simpArgs,*]]? $[at $location]?;
            repeat rewrite [←Int.coe_natAbs] $[at $location]?)

end Int.natAbs
