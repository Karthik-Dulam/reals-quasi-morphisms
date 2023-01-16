import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Tactic.Linarith

variable {G : Type u} [AddCommGroup G]

variable (G) in structure quasiHomomorphism where 
  func : G → ℤ
  bound : ℕ 
  almostAdditive x y : (func (x+y) - func x - func y).natAbs ≤ bound

