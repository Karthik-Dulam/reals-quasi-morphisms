import RealsQuasiMorphisms.Basic
import Mathlib.Algebra.Order.Ring.Cone

import Util.Logic
import Util.Arithmetic
import Util.FunctionBounds

import Mathlib.Tactic.Abel

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
lemma NonNeg.bddBelow_on_nonneg
    : f.NonNeg → (⇑f).BddBelowOn (Set.Ici 0) :=
  id

/-- An `AlmostHom` is non-negative if bounded below on {g | g ≥ 0}. -/
lemma nonneg_of_bddBelow_on_nonneg
    : (⇑f).BddBelowOn (Set.Ici 0) → f.NonNeg :=
  id

variable (f) in
/-- An `AlmostHom` is non-negative iff it is bounded below on {g | g ≥ 0}. -/
lemma bddBelow_on_nonneg_iff_nonneg
    : f.NonNeg ↔ (⇑f).BddBelowOn (Set.Ici 0) :=
  ⟨NonNeg.bddBelow_on_nonneg, nonneg_of_bddBelow_on_nonneg⟩

/-- A non-negative `AlmostHom` is bounded above on {g | g ≤ 0}. -/
lemma NonNeg.bddAbove_on_nonpos
    : f.NonNeg → (⇑f).BddAboveOn (Set.Iic 0) :=
  let ⟨bound', hₐ⟩ := f.almost_neg
  Exists.imp'' fun {bound} h {g} h_g =>
    show f g ≤ bound' - bound by
    have : f g - -f (-g) ≤ bound' := by
      -- add |·| to LHS and lift goal to ℕ
      apply Int.le_trans (Int.le_natAbs ..); apply Int.ofNat_le.mpr
      rewrite [show f g - -f (-g) = f (-g) - -f g by abel]; exact hₐ g
    linarith [this, h (neg_nonneg_of_nonpos h_g)]

/-- An `AlmostHom` is non-negative if bounded above on {g | g ≤ 0}. -/
lemma nonneg_of_bddAbove_on_nonpos
    : (⇑f).BddAboveOn (Set.Iic 0) → f.NonNeg :=
  let ⟨bound', hₐ⟩ := f.almost_neg
  Exists.imp'' fun {bound} h {g} h_g =>
    show f g ≥ -bound - bound' by
    have : f (-g) - -f g ≥ -bound' := by
      apply Int.neg_le_of_neg_le
      -- add |·| to LHS and lift goal to ℕ
      apply Int.le_trans (Int.neg_le_natAbs ..); apply Int.ofNat_le.mpr
      exact hₐ g
    linarith [this, h (neg_nonpos_of_nonneg h_g)]

variable (f) in
/-- An `AlmostHom` is non-negative iff it is bounded above on {g | g ≤ 0}. -/
lemma bddAbove_on_nonpos_iff_nonneg
    : f.NonNeg ↔ (⇑f).BddAboveOn (Set.Iic 0) :=
  ⟨NonNeg.bddAbove_on_nonpos, nonneg_of_bddAbove_on_nonpos⟩

/-- An `AlmostHom` whose negative is non-negative is bounded above on {g | g ≥ 0}. -/
lemma bddAbove_on_nonneg_of_nonpos
    : (-f).NonNeg → (⇑f).BddAboveOn (Set.Ici 0) :=
  Exists.imp'' (Int.le_neg_of_le_neg ∘ ·)

/-- If an `AlmostHom` is bounded above on {g | g ≥ 0}, its negative is non-negative. -/
lemma nonpos_of_bddAbove_on_nonneg
    : (⇑f).BddAboveOn (Set.Ici 0) → (-f).NonNeg :=
  Exists.imp'' (Int.neg_le_neg ∘ ·)

variable (f) in
/-- The negative of an `AlmostHom` f is non-negative iff f is bounded above on {g | g ≥ 0}. -/
lemma bddAbove_on_nonneg_iff_nonpos
    : (-f).NonNeg ↔ (⇑f).BddAboveOn (Set.Ici 0) :=
  ⟨bddAbove_on_nonneg_of_nonpos, nonpos_of_bddAbove_on_nonneg⟩

/-- An `AlmostHom` whose negative is non-negative is bounded below on {g | g ≤ 0}. -/
lemma bddBelow_on_nonpos_of_nonpos
    : (-f).NonNeg → (⇑f).BddBelowOn (Set.Iic 0) :=
  -- No idea why by exact is needed here; probably helps infer something.
  Exists.imp'' (by exact Int.neg_le_of_neg_le ∘ ·) ∘ NonNeg.bddAbove_on_nonpos

/-- If an `AlmostHom` is bounded below on {g | g ≤ 0}, its negative is non-negative. -/
lemma nonpos_of_bddBelow_on_nonpos
    : (⇑f).BddBelowOn (Set.Iic 0) → (-f).NonNeg:=
  (-f).nonneg_of_bddAbove_on_nonpos ∘ Exists.imp'' (Int.neg_le_neg ∘ ·)

/-- The negative of an `AlmostHom` f is non-negative iff f is bounded below on {g | g ≤ 0}. -/
lemma nonpos_iff_bddBelow_on_nonpos
    : (-f).NonNeg ↔ (⇑f).BddBelowOn (Set.Iic 0) :=
  ⟨bddBelow_on_nonpos_of_nonpos, nonpos_of_bddBelow_on_nonpos⟩

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

namespace QuasiHom

/-- Non-negativity of `AlmostHom`s lifts to `QuasiHom`s,
beause bounded `AlmostHom`s are non-negative. -/
protected def NonNeg : QuasiHom G → Prop :=
  Quot.lift AlmostHom.NonNeg fun f₁ f₂ h_b => propext <|
    let h_b : (-f₁ + f₂).Bounded := QuotientAddGroup.leftRel_apply.mp h_b
    ⟨((show f₁ + (-f₁ + f₂) = f₂ from add_neg_cancel_left ..) ▸
        AlmostHom.add_nonneg · h_b.nonneg),
     ((show f₂ + -(-f₁ + f₂) = f₁ by rw [neg_add_rev, add_neg_cancel_left,
                                         neg_neg]) ▸
        AlmostHom.add_nonneg · h_b.nonpos)⟩

/-- The sum of non-negative `QuasiHom`s is non-negative. -/
protected lemma add_nonneg {f₁ f₂ : QuasiHom G}
    : f₁.NonNeg → f₂.NonNeg → (f₁ + f₂).NonNeg :=
  Quotient.inductionOn₂ f₁ f₂ fun _ _ => AlmostHom.add_nonneg

/-- The zero `QuasiHom` is non-negative. -/
protected lemma zero_nonneg : (0 : QuasiHom G).NonNeg :=
  (boundedAlmostHoms G).zero_mem'.nonneg

end QuasiHom

end PartialOrder
section LinearOrder
variable [LinearOrderedAddCommGroup G] {f f₁ f₂ : AlmostHom G}

namespace AlmostHom

lemma bounded_of_nonneg_of_nonpos (h₁ : f.NonNeg) (h₂ : (-f).NonNeg)
    : f.Bounded :=
  let ⟨bound₁, h₁'⟩ := bddAbove_on_nonneg_of_nonpos h₂
  let ⟨bound₂, h₂'⟩ := bddAbove_on_nonneg_of_nonpos <| (neg_neg f).symm ▸ h₁
  let ⟨bound₃, h₃'⟩ := h₁.bddAbove_on_nonpos
  let ⟨bound₄, h₄'⟩ := h₂.bddAbove_on_nonpos
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
protected lemma nonneg_antisymm {f : QuasiHom G}
    : f.NonNeg → (-f).NonNeg → f = 0 :=
  Quotient.inductionOn f (motive := fun f : QuasiHom G => f.NonNeg → (-f).NonNeg → f = 0)
    fun f h₁ h₂ =>
      (QuotientAddGroup.eq_zero_iff f).mpr <| f.bounded_of_nonneg_of_nonpos h₁ h₂

/- This depends on the corresponding result for almost-homomorphisms, which is not yet proved. -/
/-- If `f` is a quasi-morphism, then at least one of `f` and `-f` must be non-negative. -/
protected lemma nonneg_total : ∀ f : QuasiHom G, f.NonNeg ∨ (-f).NonNeg :=
  Quotient.ind AlmostHom.nonneg_total

/- The lemma used for `nonneg_total` is not yet proved. -/
/-- The set of non-negative quasi-morphisms, as a 'total positive cone' (the
convenient way to construct ordered additive groups). -/
noncomputable def GP : AddCommGroup.TotalPositiveCone (QuasiHom G) where
  nonneg := QuasiHom.NonNeg
  zero_nonneg := QuasiHom.zero_nonneg
  add_nonneg := QuasiHom.add_nonneg
  nonneg_antisymm := QuasiHom.nonneg_antisymm
  nonneg_total := QuasiHom.nonneg_total
  nonnegDecidable := Classical.decPred _

noncomputable instance : LinearOrderedAddCommGroup (QuasiHom G) :=
  .mkOfPositiveCone GP

end QuasiHom

end LinearOrder
