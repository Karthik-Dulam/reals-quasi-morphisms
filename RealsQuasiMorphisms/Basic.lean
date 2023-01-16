import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Tactic.Linarith

-- For convenience. We can think about scoping this with sections later.
local notation (priority := high) "|" x "|" => Int.natAbs x

variable {G : Type u} [AddCommGroup G]

variable (G) in
structure QuasiMorphism where
  toFun : G → ℤ
  bound : ℕ 
  almostAdditive x y : |toFun (x + y) - toFun x - toFun y| ≤ bound

instance : CoeFun (QuasiMorphism G) fun _ => G → ℤ where
  coe := QuasiMorphism.toFun
