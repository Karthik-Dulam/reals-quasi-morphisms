import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.ToAdditive

namespace Equiv

def quotientEquivQuotient {α : Sort u} {s₁ s₂ : Setoid α}
    (h : ∀ a b : α, s₁.r a b ↔ s₂.r a b)
    : Quotient s₁ ≃ Quotient s₂ where
  toFun  := @Quotient.map α α s₁ s₂ id fun a b => h a b |>.mp
  invFun := @Quotient.map α α s₂ s₁ id fun a b => h a b |>.mpr
  left_inv  := Quotient.ind fun _ => rfl
  right_inv := Quotient.ind fun _ => rfl

@[to_additive]
def Group {α β} (f : α ≃ β) (inst : Group β) : Group α where
  /- The shows are only necessary because I can't figure out how to
  unfold the mul definition. -/
  mul a b := f.symm (f a * f b)
  mul_assoc a b c := by
    show f.symm (f (f.symm (f a * f b)) * f c) = f.symm (f a * f (f.symm (f b * f c)))
    simp only [f.apply_symm_apply, inst.mul_assoc]
  one := f.symm 1
  one_mul a := by
    show f.symm (f (f.symm 1) * f a) = a
    simp only [f.apply_symm_apply, f.symm_apply_apply, inst.one_mul]
  mul_one a := by
    show f.symm (f a * f (f.symm 1)) = a
    simp only [f.apply_symm_apply, f.symm_apply_apply, inst.mul_one]
  inv a := f.symm (f a)⁻¹
  mul_left_inv a := by
    show f.symm (f (f.symm (f a)⁻¹) * f a) = f.symm 1
    simp only [f.apply_symm_apply, f.symm_apply_apply, inst.mul_left_inv]

end Equiv
