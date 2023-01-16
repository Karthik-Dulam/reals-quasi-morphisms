import Mathlib.Init.Data.Int.Basic
import Mathlib.Algebra.Group.Defs

def is_bounded {G : Type u} (f : G → ℤ) := ∃n, ∀ x, f x ≤ n
structure quasiHomomorphism (G : Type u) [AddCommGroup G] where 
  f : G → ℤ
  almostAdditive : is_bounded (fun (x,y) => f (x+y) - f x - f y)
