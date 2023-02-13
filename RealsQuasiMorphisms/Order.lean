import RealsQuasiMorphisms.Basic
import Mathlib.Algebra.Order.Field.Defs
import RealsQuasiMorphisms.Algebra
import Mathlib.Algebra.Order.Ring.Cone

namespace AlmostHom

variable {G : Type} [OrderedAddCommGroup G]

def nonneg (f : AlmostHom G) : Prop := ∃ a : ℤ , ∀ x : G, x ≥ 0 → f x ≥ a
def nonpos (f : AlmostHom G) : Prop := ∃ b : ℤ , ∀ x : G, x ≥ 0 → f x ≤ b
def le (f g : AlmostHom G) : Prop := nonneg (g - f)

-- why exactly this is needed is well beyond me
private theorem add_reduces_to_fun (f g : AlmostHom G) : toFun (f + g) = toFun f + toFun g := by rfl
private theorem neg_reduces_to_fun (f : AlmostHom G) : toFun (-f) = - toFun f:= by rfl
private theorem sub_reduces_to_fun (f g : AlmostHom G) : toFun (f - g) = toFun f - toFun g := by rfl

instance : Preorder (AlmostHom G) where
  le := le
  le_refl f := by
                simp only [le, nonneg, sub_self]
                use -1; intro x _
                show -1 ≤ 0; simp only [Left.neg_nonpos_iff]
  le_trans p q r:= by
                    intro hpq hqr
                    simp only [le, nonneg] at hpq hqr ⊢
                    let ⟨a, hpq⟩ := hpq; let ⟨b, hqr⟩ := hqr
                    use a+b; intro x hx
                    simp [sub_reduces_to_fun] at hpq hqr ⊢ 
                    let h := add_le_add (hpq x hx) (hqr x hx)
                    simp only [sub_add_sub_cancel'] at h
                    apply h

end AlmostHom

namespace QuasiHom

variable {G : Type} [OrderedAddCommGroup G]

theorem bounded_plus_nonneg_nonneg (f : boundedAlmostHoms G) (g : AlmostHom G) : g.nonneg → (f + g).nonneg := by sorry

-- ten thousand lines of nonsense
-- because lean
theorem nonneg_respects_equiv' (f g: AlmostHom G): (QuotientAddGroup.con (boundedAlmostHoms G)) f g → f.nonneg → g.nonneg := by
  intro h hf
  let a := AddAction.orbitRel (AddSubgroup.opposite (boundedAlmostHoms G)) (AlmostHom G)
  let b := a.r
  let H (x : AlmostHom G) := AddAction.orbit (AddSubgroup.opposite (boundedAlmostHoms G)) x
  let c (x y : AlmostHom G) := x ∈ H y
  have h' : b = c := by rfl
  have h : b f g := by apply h
  have h : c f g := by apply h
  have h : f ∈ H g := by apply h
  have h : f ∈ AddAction.orbit (AddSubgroup.opposite (boundedAlmostHoms G)) g := by apply h
  have h : f ∈ Set.range fun (x : boundedAlmostHoms G) => x + g := by
    sorry
  have h : ∃ (x : boundedAlmostHoms G), x + g = f := by
    simp only [Set.mem_range] at h
    exact h
  have h : ∃ (x : boundedAlmostHoms G), (-x) + x + g = (-x) + f := by
    let ⟨x, hx⟩ := h
    use x
    sorry -- pathetic
  have h : ∃ (x : boundedAlmostHoms G), g = x + f := by
    let ⟨x, hx⟩ := h
    use -x
    simp at hx
    exact hx
  -- there should be a way to do the above with very little code, but I don't know how
  let ⟨x, hx⟩ := h
  let h' := bounded_plus_nonneg_nonneg x f hf
  simp [hx]
  exact h'

theorem nonneg_respects_equiv (f g: AlmostHom G): (QuotientAddGroup.con (boundedAlmostHoms G)) f g → f.nonneg = g.nonneg := by
  intro h
  apply propext
  apply Iff.intro
  · intro hf
    apply nonneg_respects_equiv' f g h hf
  · intro hg
    apply nonneg_respects_equiv' g f ((QuotientAddGroup.con (boundedAlmostHoms G)).iseqv.symm h) hg

def nonneg (f : QuasiHom G) : Prop := Quotient.liftOn f AlmostHom.nonneg nonneg_respects_equiv

theorem zero_nonneg : nonneg (0 : QuasiHom G) := sorry
theorem add_nonneg {f g : QuasiHom G} : nonneg f → nonneg g → nonneg (f + g) := sorry


def GP : AddCommGroup.TotalPositiveCone (QuasiHom G) := {
  nonneg := nonneg,
  zero_nonneg := zero_nonneg,
  add_nonneg := add_nonneg,
  nonneg_antisymm := sorry,
  nonneg_total := sorry,
  nonnegDecidable := sorry --  no clue how decidable works
}

-- instance : LinearOrder (QuasiHom G) where
--   le := sorry
--   le_refl := sorry
--   le_trans := sorry
--   le_antisymm := sorry
--   le_total := sorry
--   decidable_le := sorry -- how to even do this??
--   decidable_eq := sorry -- again, HOW to do this??


-- instance : LinearOrderedField (QuasiHom ℤ) where
--   add_le_add_left := sorry
--   zero_le_one := sorry
--   mul_pos := sorry
--   mul_comm := sorry
--   mul_inv_cancel := sorry
--   inv_zero := sorry
--   le_total := sorry -- this one is already proved in LinearOrder right??
--   decidable_le := sorry -- this one is already proved in LinearOrder right??
  

end QuasiHom
