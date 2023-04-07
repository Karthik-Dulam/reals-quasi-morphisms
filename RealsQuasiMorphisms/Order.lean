import Util.FunctionBounds
import RealsQuasiMorphisms.Basic
import Mathlib.Algebra.Order.Ring.Cone

import Mathlib.Tactic.Abel

import Util.Logic
import Util.Arithmetic
import Util.FunctionBounds

open scoped Int.natAbs

variable {G : Type _}

section PartialOrder variable [OrderedAddCommGroup G]

namespace AlmostHom

/-- `f` is non-negative if the image under it of `{g : G | g ≥ 0}` is bounded below. -/
protected def NonNeg (f : AlmostHom G) : Prop :=
  ∃ bound : ℤ , ∀ {g : G}, g ≥ 0 → f g ≥ bound

/- protected def NonPos (f : AlmostHom G) : Prop := (-f).NonNeg -/

variable {f : AlmostHom G}

section NonNegBasicLemmas

/-- A non-negative `AlmostHom` is bounded below on {g | g ≥ 0}. -/
lemma bddBelow_on_nonneg_of_nonneg
    : f.NonNeg → (⇑f).BddBelowOn (Set.Ici 0) :=
  id

/-- A non-negative `AlmostHom` is bounded above on {g | g ≤ 0}. -/
lemma bddAbove_on_nonpos_of_nonneg
    : f.NonNeg → (⇑f).BddAboveOn (Set.Iic 0) :=
  let ⟨bound', hₐ⟩ := f.almost_neg
  Exists.imp'' fun {bound} h {g} h_g =>
      show f g ≤ bound' - bound by
      have : f g - -f (-g) ≤ bound' := by
        -- add |·| to LHS and lift goal to ℕ
        apply Int.le_trans (Int.le_natAbs ..); apply Int.ofNat_le.mpr
        rewrite [show f g - -f (-g) = f (-g) - -f g by abel]; exact hₐ g
      linarith [this, h (neg_nonneg_of_nonpos h_g)]

/-- An `AlmostHom` whose negative is non-negative is bounded above on {g | g ≥ 0}. -/
lemma bddAbove_on_nonneg_of_nonpos
    : (-f).NonNeg → (⇑f).BddAboveOn (Set.Ici 0) :=
  Exists.imp'' (Int.le_neg_of_le_neg ∘ ·)

/-- An `AlmostHom` whose negative is non-negative is bounded below on {g | g ≤ 0}. -/
lemma bddBelow_on_nonpos_of_nonpos
    : (-f).NonNeg → (⇑f).BddBelowOn (Set.Iic 0) :=
  -- No idea why by exact is needed here; probably helps infer something.
  Exists.imp'' (by exact Int.neg_le_of_neg_le ∘ ·) ∘ bddAbove_on_nonpos_of_nonneg

end NonNegBasicLemmas

/-- The sum of non-negative `AlmostHom`s is non-negative. -/
protected lemma add_nonneg {f₁ f₂ : AlmostHom G}
    : f₁.NonNeg → f₂.NonNeg → (f₁ + f₂).NonNeg :=
  fun ⟨bound₁, h₁⟩ ⟨bound₂, h₂⟩ =>
    ⟨bound₁ + bound₂, fun h => Int.add_le_add (h₁ h) (h₂ h)⟩

/-- A bounded `AlmostHom` is non-negative. -/
lemma Bounded.nonneg : f.Bounded → f.NonNeg :=
  (·.bddBelow.imp <| fun _ => Set.ball_of_forall)

/-- The negative of a bounded `AlmostHom` is non-negative. -/
lemma Bounded.nonpos : f.Bounded → (-f).NonNeg :=
  Bounded.nonneg ∘ (boundedAlmostHoms G).neg_mem'

end AlmostHom
#exit
namespace QuasiHom

/-- A quasi-morphism `f` is non-negative if any representative almost-homomorphism is non-negative.

This is well-defined by `bounded_plus_nonneg_nonneg`. -/
protected def nonneg (f : QuasiHom G) : Prop := Quot.liftOn f AlmostHom.NonNeg (λ f g h ↦ by
  rw [QuotientAddGroup.leftRel_apply] at h
  let x : boundedAlmostHoms G := ⟨-f + g, h⟩
  have h₁ : g = f + x := by
    simp only [add_neg_cancel_left]
  have h₂ : f = g + -x := by
    simp only [neg_add_rev, neg_neg, add_neg_cancel_left]
  apply propext
  apply Iff.intro
  · intro hf
    rw [h₁]
    sorry -- apply AlmostHom.bounded_plus_nonneg_nonneg x hf
  · intro hg
    rw [h₂]
    sorry -- apply AlmostHom.bounded_plus_nonneg_nonneg (-x) hg
  )

end QuasiHom

end PartialOrder
section LinearOrder
variable [LinearOrderedAddCommGroup G] {f f₁ f₂ : AlmostHom G}

namespace AlmostHom

lemma bounded_of_nonneg_of_nonpos (h₁ : f.NonNeg) (h₂ : (-f).NonNeg)
    : f.Bounded :=
  let ⟨bound₁, h₁'⟩ := bddAbove_on_nonneg_of_nonpos h₂
  let ⟨bound₂, h₂'⟩ := bddAbove_on_nonneg_of_nonpos <| (neg_neg f).symm ▸ h₁
  let ⟨bound₃, h₃'⟩ := bddAbove_on_nonpos_of_nonneg h₁
  let ⟨bound₄, h₄'⟩ := bddAbove_on_nonpos_of_nonneg h₂
  ⟨max (max bound₁ bound₂) (max bound₃ bound₄) |>.toNat, fun g => by
     custom_zify
     refine Int.le_trans ?_ (Int.self_le_toNat ..) -- remove `toNat`from RHS
     cases le_total 0 g
     case' inl h_ge =>
       specialize h₁' h_ge; specialize h₂' h_ge
       refine Int.le_trans ?_ (Int.le_max_left ..)
     case' inr h_le =>
       specialize h₃' h_le; specialize h₄' h_le
       refine Int.le_trans ?_ (Int.le_max_right ..)
     all_goals apply Int.natAbs_le' <;>
       (apply Int.le_trans (by assumption)
        solve| apply Int.le_max_left | apply Int.le_max_right)⟩

/-- For an `AlmostHom` f, both f and -f are `NonNeg` iff f is bounded.  -/
lemma nonneg_and_nonpos_iff_bounded (f : AlmostHom G)
    : f.NonNeg ∧ (-f).NonNeg ↔ f.Bounded :=
  ⟨And.elim bounded_of_nonneg_of_nonpos,
   fun h => ⟨h.nonneg, h.nonpos⟩⟩

/- This is a somewhat non-trivial result and not proven yet. -/
/-- If `f` is an almost-homomorphism, then at least one of `f` and `-f` must be non-negative. -/
protected lemma nonneg_total (f : AlmostHom G) : f.NonNeg ∨ (-f).NonNeg := by
  sorry

end AlmostHom

namespace QuasiHom

/-- If `f` and `-f` are both non-negative quasi-morphisms, then `f` must be `0`. -/
protected lemma nonneg_antisymm {f : QuasiHom G} : f.nonneg → (-f).nonneg → f = 0 := by
  apply QuotientAddGroup.induction_on f
  intro f hf hf'
  rw [QuotientAddGroup.eq_zero_iff]
  exact AlmostHom.bounded_of_nonneg_of_nonpos hf hf'

/- This depends on the corresponding result for almost-homomorphisms, which is not yet proved. -/
/-- If `f` is a quasi-morphism, then at least one of `f` and `-f` must be non-negative. -/
protected lemma nonneg_total (f : QuasiHom G) : f.nonneg ∨ (-f).nonneg := by
  apply QuotientAddGroup.induction_on f
  intro f
  exact AlmostHom.nonneg_total f


/- The lemma used for `nonneg_total` is not yet proved. -/
/-- The set of non-negative quasi-morphisms, as a 'total positive cone' (the
convenient way to construct ordered additive groups). -/
noncomputable def GP : AddCommGroup.TotalPositiveCone (QuasiHom G) where
  nonneg := QuasiHom.nonneg
  zero_nonneg := QuasiHom.zero_nonneg
  add_nonneg := QuasiHom.add_nonneg
  nonneg_antisymm := QuasiHom.nonneg_antisymm
  nonneg_total := by simp only [QuasiHom.nonneg_total, forall_const]
  nonnegDecidable := (Classical.dec ·.nonneg)

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

end LinearOrder
