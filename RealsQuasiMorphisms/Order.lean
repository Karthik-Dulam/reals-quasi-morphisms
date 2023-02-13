import RealsQuasiMorphisms.Basic
import Mathlib.Algebra.Order.Field.Defs
import RealsQuasiMorphisms.Algebra

namespace AlmostHom

variable {G : Type} [OrderedAddCommGroup G]

def is_pos (f : AlmostHom G) : Prop := ∃ a : ℤ , ∀ x : G, x ≥ 0 → f x ≥ a
def is_neg (f : AlmostHom G) : Prop := ∃ b : ℤ , ∀ x : G, x ≥ 0 → f x ≤ b
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


theorem neg_minus_pos {f : AlmostHom G} (h : is_neg f) : is_pos (-f) := by
  simp only [is_neg, is_pos, neg_reduces_to_fun] at h ⊢
  let ⟨a, ha⟩ := h
  use -a; intro x hx
  show - f.toFun x ≥ -a
  simp only [neg_le_neg_iff]
  apply ha x hx

theorem pos_minus_neg {f : AlmostHom G} (h : is_pos f) : is_neg (-f) := by
  simp only [is_neg, is_pos, neg_reduces_to_fun] at h ⊢
  let ⟨a, ha⟩ := h
  use -a; intro x hx
  show - f.toFun x ≤ -a
  simp only [neg_le_neg_iff]
  apply ha x hx

theorem minus_neg_pos {f : AlmostHom G} (h : is_neg (-f)) : is_pos f := by
  simp only [is_neg, is_pos, neg_reduces_to_fun] at h ⊢
  let ⟨a, ha⟩ := h
  use -a; intro x hx
  show f.toFun x ≥ -a
  simp only [ge_iff_le]
  calc -a ≤ - - (toFun f x) :=
      by simp only [neg_le_neg_iff]; apply ha x hx
      _ = toFun f x := by simp only [neg_neg]

theorem minus_pos_neg {f : AlmostHom G} (h : is_pos (-f)) : is_neg f := by
  simp only [is_neg, is_pos, neg_reduces_to_fun] at h ⊢
  let ⟨a, ha⟩ := h
  use -a; intro x hx
  calc toFun f x = - - (toFun f x)  := by simp only [neg_neg]
      _ ≤ -a := by simp only [neg_le_neg_iff]; apply ha x hx

-- the meat lies here, the rest is nonsense because lean can't figure out anything
-- this depends on the bound though
theorem always_pos_or_neg (f : AlmostHom G) : is_pos f ∨ is_neg f := by sorry

-- WHY CAN'T LEAN FIGURE OUT MOST OF THIS PROOF?????
theorem le_total (f g : AlmostHom G) : f ≤ g ∨ g ≤ f := by
  show is_pos (g - f) ∨ is_pos (f - g)
  let h := always_pos_or_neg (g - f)
  apply Or.elim h
  · apply Or.inl
  · intro h
    apply Or.inr
    let h := neg_minus_pos h
    simp at h
    apply h

instance : IsTotalPreorder (AlmostHom G) (· ≤ ·) where
  total := le_total
  trans := by apply le_trans

theorem bounded_iff_pos_and_neg (f : AlmostHom G) : f ∈ boundedAlmostHoms G ↔ f.is_pos ∧ f.is_neg := by
  sorry

theorem sub_bounded_iff_le_and_ge (f g : AlmostHom G) : f - g ∈ boundedAlmostHoms G ↔ f ≤ g ∧ g ≤ f := by
  apply Iff.intro
  · intro h
    show is_pos (g - f) ∧ is_pos (f - g)
    simp only [bounded_iff_pos_and_neg] at h
    let ⟨h₁, h₂⟩ := h
    let h₂ := neg_minus_pos h₂
    simp at h₂
    simp [h₁, h₂]
  · intro h
    simp only [bounded_iff_pos_and_neg]
    let ⟨h₁, h₂⟩ := h
    apply And.intro
    · apply h₂ 
    · apply minus_pos_neg
      simp
      apply h₁

-- the fact that this is even needed anywhere is proof that lean is useless
theorem le_iff_le (f g : AlmostHom G) : f ≤ g ↔ AlmostHom.le f g := by
  apply Iff.intro
  · intro h
    simp only [le]
    apply h
  · intro h
    simp only [le] at h
    apply h

end AlmostHom

namespace QuasiHom

variable {G : Type} [OrderedAddCommGroup G]

instance : LinearOrder (QuasiHom G) where
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_total := sorry
  decidable_le := sorry -- how to even do this??
  decidable_eq := sorry -- again, HOW to do this??


instance : LinearOrderedField (QuasiHom ℤ) where
  add_le_add_left := sorry
  zero_le_one := sorry
  mul_pos := sorry
  mul_comm := sorry
  mul_inv_cancel := sorry
  inv_zero := sorry
  le_total := sorry -- this one is already proved in LinearOrder right??
  decidable_le := sorry -- this one is already proved in LinearOrder right??
  

end QuasiHom
