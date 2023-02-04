import Mathlib.Algebra.Field.Basic
import RealsQuasiMorphisms.Basic

open scoped Int.natAbs

variable {G : Type _} [AddCommGroup G]

protected theorem AlmostAdditive.comp
    ⦃f₁ : ℤ → ℤ⦄ ⦃bound₁ : ℕ⦄ (h₁ : AlmostAdditive f₁ bound₁)
    ⦃f₂ : G → ℤ⦄ ⦃bound₂ : ℕ⦄ (h₂ : AlmostAdditive f₂ bound₂)
  : AlmostAdditive (f₁ ∘ f₂) <| (bound₁ + |f₁ 1|) * bound₂ + bound₁ * 3 := fun x y =>
  calc |f₁ (f₂ (x + y)) - f₁ (f₂ x) - f₁ (f₂ y)|
    ≤ |f₁ (f₂ (x + y)) - f₁ (f₂ (x + y) - f₂ x - f₂ y) - f₁ (f₂ x + f₂ y)|
      + |f₁ (f₂ (x + y) - f₂ x - f₂ y)|
      + |f₁ (f₂ x + f₂ y) - f₁ (f₂ x) - f₁ (f₂ y)|
        := by lax_exact Int.natAbs_add_le₃ (f₁ (f₂ (x + y)) - f₁ (f₂ (x + y) - f₂ x - f₂ y) - f₁ (f₂ x + f₂ y))
                                           (f₁ (f₂ (x + y) - f₂ x - f₂ y))
                                           (f₁ (f₂ x + f₂ y) - f₁ (f₂ x) - f₁ (f₂ y))
              linarith
  _ ≤ bound₁
      + ((bound₁ + |f₁ 1|) * |f₂ (x + y) - f₂ x - f₂ y| + bound₁)
      + bound₁
        := by conv in f₁ (f₂ (x + y)) =>
                /- Need `f₂ (x + y)` like this to use `h₁.almost_additive`. -/
                rw [show f₂ (x + y) = (f₂ (x + y) - f₂ x - f₂ y) + (f₂ x + f₂ y)
                    by linarith]
              refine Nat.add_le_add₃ ?_ ?using_lemma ?_;
              case using_lemma =>
                lax_exact h₁.linear_growth_upper_bound (f₂ (x + y) - f₂ x - f₂ y) 1
                rw [zsmul_int_one]
              all_goals apply h₁.almost_additive
  _ = (bound₁ + |f₁ 1|) * |f₂ (x + y) - f₂ x - f₂ y| + bound₁ * 3 := by linarith
  _ ≤ (bound₁ + |f₁ 1|) * bound₂ + bound₁ * 3
        := h₂.almost_additive .. |> Nat.mul_le_mul_left (k := _)
                                 |> Nat.add_le_add_right (k := _)

/-- Composition with a quasi-morphism on ℤ, returning another quasi-morphism. -/
protected def AlmostHom.comp  (f₁ : AlmostHom ℤ) (f₂ : AlmostHom G) : AlmostHom G where
  toFun := f₁ ∘ f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    -- bound is filled in based on the proof :)
    ⟨_, AlmostAdditive.comp h₁ h₂⟩


namespace QuasiHom

/-! One has to prove both that -/

/- protected def smul : QuasiHom ℤ → AlmostHom G → AlmostHom G := by -/ 
/-   intro f g -/
/-   refine QuotientGroup.lift {QuasiHom ℤ} -/



def compHom : AlmostHom ℤ →+ AlmostHom G → AlmostHom G where
  toFun := AlmostHom.comp 
  map_add' := sorry
  map_zero' := sorry
  
lemma compHom_ker_zero : 
    ∀ f, f ∈ boundedAlmostHoms ℤ → @compHom G _ f = 0 := 
  sorry



#check QuotientAddGroup.lift (boundedAlmostHoms ℤ) compHom compHom_ker_zero 
  

-- QuotientGroup.lift; Setoid Quotient
#print QuasiHom
#print QuotientGroup.lift

end QuasiHom

