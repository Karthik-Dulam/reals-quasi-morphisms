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
private lemma add_reduces_to_fun (f g : AlmostHom G) : toFun (f + g) = toFun f + toFun g := by rfl
private lemma neg_reduces_to_fun (f : AlmostHom G) : toFun (-f) = - toFun f:= by rfl
private lemma sub_reduces_to_fun (f g : AlmostHom G) : toFun (f - g) = toFun f - toFun g := by rfl

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

private lemma bounded_plus_nonneg_nonneg' (f : AlmostHom G) ⦃g : AlmostHom G⦄ (h : ∃ bound : ℕ, Bounded g bound) : f.nonneg → (f + g).nonneg := by
  intro hf
  let ⟨bound, hb⟩ := h
  dsimp [Bounded] at hb
  simp only [AlmostHom.nonneg] at hf
  let ⟨a, ha⟩ := hf
  simp only [AlmostHom.nonneg]
  use a - bound
  intro x hx
  have ha := ha x hx
  have hb := hb x
  have hb : -bound ≤ g.toFun x := by
    simp only [←Int.ofNat_le, Int.coe_natAbs] at hb
    simp only [abs_le] at hb
    exact hb.left
  simp only [AlmostHom.add_reduces_to_fun]
  show (f.toFun x) + (g.toFun x) ≥ a - bound
  simp only [ge_iff_le] at ha ⊢
  apply add_le_add ha hb

protected theorem bounded_plus_nonneg_nonneg (f : AlmostHom G) (g : boundedAlmostHoms G) : f.nonneg → (f + g).nonneg := by
  exact AlmostHom.bounded_plus_nonneg_nonneg' f g.property

end AlmostHom

namespace QuasiHom

variable {G : Type} [OrderedAddCommGroup G]

#check (AddSubgroup.opposite (boundedAlmostHoms G))
#check (AlmostHom G)ᵃᵒᵖ
#check AddOpposite.op


-- ten thousand lines of nonsense
-- because lean
private lemma nonneg_respects_equiv' (f g: AlmostHom G): (QuotientAddGroup.con (boundedAlmostHoms G)) f g → f.nonneg → g.nonneg := by
  intro h hf
  have h : f ∈ AddAction.orbit (AddSubgroup.opposite (boundedAlmostHoms G)) g := by apply h
  dsimp [AddAction.orbit] at h
  -- TODO: stuck here
  have h : f ∈ Set.range fun (x : boundedAlmostHoms G) => x + g := by sorry
  have h : ∃ (x : boundedAlmostHoms G), x + g = f := by
    simp only [Set.mem_range] at h
    exact h
  have h : ∃ (x : boundedAlmostHoms G), g = x + f := by
    let ⟨x, hx⟩ := h
    use -x
    have hx' : -x + (x + g) = -x + f := by
      simp only [hx]
    simp only [neg_add_cancel_left] at hx'
    exact hx'
  -- there should be a way to do the above with very little code, but I don't know how
  let ⟨x, hx⟩ := h
  let h' := AlmostHom.bounded_plus_nonneg_nonneg f x hf
  simp only [hx, add_comm]
  exact h'

protected theorem nonneg_respects_equiv (f g: AlmostHom G): (QuotientAddGroup.con (boundedAlmostHoms G)) f g → f.nonneg = g.nonneg := by
  intro h
  apply propext
  apply Iff.intro
  · intro hf
    apply QuasiHom.nonneg_respects_equiv' f g h hf
  · intro hg
    apply QuasiHom.nonneg_respects_equiv' g f ((QuotientAddGroup.con (boundedAlmostHoms G)).iseqv.symm h) hg

def nonneg (f : QuasiHom G) : Prop := Quotient.liftOn f AlmostHom.nonneg QuasiHom.nonneg_respects_equiv

private lemma zero_nonneg : nonneg (0 : QuasiHom G) := sorry
private lemma add_nonneg {f g : QuasiHom G} : nonneg f → nonneg g → nonneg (f + g) := sorry


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
