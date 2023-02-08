import RealsQuasiMorphisms.Basic
import Mathlib.Algebra.Order.Field.Defs
import RealsQuasiMorphisms.Algebra

namespace AlmostHom

variable {G : Type} [OrderedAddCommGroup G]

def is_pos (f : AlmostHom G) : Prop := ∃ a : ℤ , ∀ x : G, x ≥ 0 → f x ≥ a

def is_neg (f : AlmostHom G) : Prop := ∃ b : ℤ , ∀ x : G, x ≥ 0 → f x ≥ b

def le (f g : AlmostHom G) : Prop := is_pos (g - f)

-- why exactly this is needed is well beyond me
private theorem add_reduces_to_fun (f g : AlmostHom G) : toFun (f + g) = toFun f + toFun g := by rfl
private theorem neg_reduces_to_fun (f : AlmostHom G) : toFun (-f) = - toFun f:= by rfl
private theorem sub_reduces_to_fun (f g : AlmostHom G) : toFun (f - g) = toFun f - toFun g := by rfl

instance : Preorder (AlmostHom G) where
  le := le
  le_refl f := by
                simp only [le, is_pos, sub_self]
                use -1; intro x _
                show -1 ≤ 0; simp only [Left.neg_nonpos_iff]
  le_trans p q r:= by
                    intro hpq hqr
                    simp only [le, is_pos] at hpq hqr ⊢
                    let ⟨a, hpq⟩ := hpq; let ⟨b, hqr⟩ := hqr
                    use a+b; intro x hx
                    simp [sub_reduces_to_fun] at hpq hqr ⊢ 
                    let h := add_le_add (hpq x hx) (hqr x hx)
                    simp only [sub_add_sub_cancel'] at h
                    apply h


-- instance : OrderedAddCommGroup (AlmostHom G) where
--   add_le_add_left := sorry

end AlmostHom

namespace QuasiHom


instance : LinearOrderedField (QuasiHom ℤ) where
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  add_le_add_left := sorry
  zero_le_one := sorry
  mul_pos := sorry
  le_total := sorry
  decidable_le := sorry
  mul_comm := sorry
  mul_inv_cancel := sorry
  inv_zero := sorry
  decidable_eq := sorry


  

end QuasiHom
