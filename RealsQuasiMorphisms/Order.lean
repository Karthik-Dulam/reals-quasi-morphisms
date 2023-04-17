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
      apply Int.le_trans (Int.le_natAbs ..); apply Int.ofNat_le.mpr
      rewrite [show f g - -f (-g) = f (-g) - -f g by abel]; exact hₐ g
    linarith [this, h (neg_nonneg_of_nonpos h_g)]

/-- An `AlmostHom` is non-negative if bounded above on {g | g ≤ 0}. -/
lemma nonneg_of_bddAbove_on_nonpos
    : (⇑f).BddAboveOn (Set.Iic 0) → f.NonNeg :=
  let ⟨bound', hₐ⟩ := f.almost_neg
  Exists.imp'' fun {bound} h {g} h_g =>
    show f g ≥ -bound - bound' by
    have : f (-g) - -f g ≥ -bound' := Int.neg_le_self_of_natAbs_le (hₐ g)
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
/-! `QuasiHom G` is partially ordered when `G` is linearly ordered. -/
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

end AlmostHom

namespace QuasiHom

/-- If `f` and `-f` are both non-negative quasi-morphisms, then `f` must be `0`. -/
protected lemma nonneg_antisymm {f : QuasiHom G}
    : f.NonNeg → (-f).NonNeg → f = 0 :=
  Quotient.inductionOn f (motive := fun f : QuasiHom G => f.NonNeg → (-f).NonNeg → f = 0)
    fun f h₁ h₂ =>
      (QuotientAddGroup.eq_zero_iff f).mpr <| f.bounded_of_nonneg_of_nonpos h₁ h₂

variable (G)

noncomputable def positiveCone : AddCommGroup.PositiveCone (QuasiHom G) where
  nonneg := QuasiHom.NonNeg
  zero_nonneg := QuasiHom.zero_nonneg
  add_nonneg := QuasiHom.add_nonneg
  nonneg_antisymm := QuasiHom.nonneg_antisymm

noncomputable instance : OrderedAddCommGroup (QuasiHom G) :=
  .mkOfPositiveCone (positiveCone G)

end QuasiHom

end LinearOrder
/-! `QuasiHom G` is totally ordered when `G` is `ℤ` specifically. -/
section Integers

namespace AlmostHom

-- Note: the next three results have terrible names.

theorem positive_linear_growth_of_large_enough_value
    {f : ℤ → ℤ} {bound : ℕ} (h_bound : AlmostAdditive f bound)
    {m : ℕ} (h : f m > bound * 2)
    : ∀ n : ℕ, f n ≥ n - ↑((m + 3) * bound) :=
  have h_fm_nonneg : |f m| = f m := Eq.symm <| Int.eq_natAbs_of_zero_le <|
    calc (0:ℤ) ≤ bound * 2 := Int.ofNat_zero_le ..
             _ ≤ f m       := Int.le_of_lt h
  -- Linear growth for multiples of m
  have : ∀ n : ℕ, |f (n * m)| ≥ (f m - bound) * |n| - bound := by
    intro n
    rewrite [←h_fm_nonneg, show (_:ℤ) * (m:ℤ) = (_:ℤ) • (m:ℤ) from rfl]
    -- Poor man's controlled norm_cast
    norm_cast; rewrite [Int.abs_eq_natAbs,
                        Int.subNatNat_of_le <|
                          show bound ≤ |f m| from Int.ofNat_le.mp <|
                          calc (bound:ℤ) ≤ bound * 2 := by linarith
                                       _ ≤ f m       := Int.le_of_lt h
                                       _ ≤ |f m|     := Int.le_natAbs]
    norm_cast; rewrite [Int.abs_eq_natAbs]; apply Int.le_trans (Int.subNatNat_le_sub ..)
    exact_mod_cast h_bound.linear_growth_lower_bound n m
  sorry

theorem diverges_nonneg_of_nonneg_of_not_bddAbove_on_nonneg {f : AlmostHom ℤ}
    (h : ¬(⇑f).BddAboveOn (Set.Ici 0))
    : ∀ R : ℤ, ∃ N : ℕ, ∀ n : ℤ, n ≥ N → f n ≥ R :=
  let ⟨bound, h_a⟩ := f.almost_additive
  let ⟨m, h⟩ : ∃ m : ℕ, bound * 2 < f m := by
    unfold Function.BddAboveOn Function.BddAboveOnBy at h; push_neg at h
    let ⟨m, h_nonneg, h⟩ := h (bound * 2)
    -- All we really need here is that `m = ↑(_something_)`.
    exact ⟨m.toNat, Int.toNat_of_nonneg h_nonneg ▸ h⟩
  fun R => ⟨R.toNat + (m + 3) * bound, fun n h_ge => by
    -- Replace n:ℤ to n':ℤ
    let n' := n.toNat
    have : ↑n' = n :=
      Int.toNat_of_nonneg <| Int.le_trans (Int.ofNat_zero_le ..) h_ge
    rewrite [←this] at h_ge ⊢
    let h_ge : n' ≥ R.toNat + (m + 3) * bound := Int.ofNat_le.mp h_ge
    calc f n' ≥ n' - ↑((m + 3) * bound)
                  := positive_linear_growth_of_large_enough_value h_a h n'
            _ ≥ ↑(R.toNat + (m + 3) * bound) - ↑((m + 3) * bound)
                  := Int.sub_le_sub_right (c := _) <| Int.ofNat_le.mpr h_ge
            _ ≥ R.toNat := by custom_zify; linarith
            _ ≥ R       := Int.self_le_toNat ..⟩

lemma diverges_nonpos_of_nonneg_of_not_bddAbove_on_nonneg {f : AlmostHom ℤ}
    (h : ¬(⇑f).BddAboveOn (Set.Ici 0))
    (R : ℤ) : ∃ N : ℕ, ∀ n : ℤ, n ≤ -N → f n ≤ R :=
  let ⟨bound, h_a⟩ := f.almost_neg
  let ⟨N, h⟩ := diverges_nonneg_of_nonneg_of_not_bddAbove_on_nonneg h (-R + bound)
  ⟨N, fun n (h_le : n ≤ -N) =>
        have : f n - -f (-n) ≤ bound := by
          conv in f n => rw [←neg_neg n]
          exact Int.le_trans (Int.le_natAbs ..) (Int.ofNat_le.mpr <| h_a (-n))
        by linarith [this, h (-n) (Int.le_neg_of_le_neg h_le)]⟩

theorem nonneg_total_integers (f : AlmostHom ℤ) : f.NonNeg ∨ (-f).NonNeg :=
  Classical.byCases (p := (⇑f).BddAboveOn (Set.Ici 0))
    (Or.inr ∘ f.nonpos_of_bddAbove_on_nonneg)
    fun h => Or.inl <|
      have ⟨N, h⟩ := diverges_nonneg_of_nonneg_of_not_bddAbove_on_nonneg h 0
      let ⟨a, b, h'⟩ := f.linear_growth_upper_bound_int
      ⟨-(a * N + b : ℕ), fun {n} h_nonneg => if h_comp : n ≥ N then
         Int.le_trans (Int.neg_ofNat_le_zero (a * N + b)) (h n h_comp)
       else
         Int.neg_le_self_of_natAbs_le <| calc
           |f n| ≤ a * |n| + b := h' n
               _ ≤ a * N + b
                     := Nat.add_le_add_right (k := b) <| Nat.mul_le_mul_left (k := a) <|
                        show |n| ≤ N from
                        Int.natAbs_le
                          (by linarith [h_comp])
                          (Int.le_trans (Int.neg_nonpos_of_nonneg h_nonneg)
                                        (Int.ofNat_zero_le ..))⟩

end AlmostHom

namespace EudoxusReal

/-- If `f` is a quasi-morphism, then at least one of `f` and `-f` must be non-negative. -/
protected lemma nonneg_total : ∀ f : EudoxusReal, f.NonNeg ∨ (-f).NonNeg :=
  Quotient.ind AlmostHom.nonneg_total_integers

noncomputable def totalPositiveCone
    : AddCommGroup.TotalPositiveCone EudoxusReal where
  toPositiveCone := QuasiHom.positiveCone ℤ
  nonneg_total := EudoxusReal.nonneg_total
  nonnegDecidable := Classical.decPred _

noncomputable instance : LinearOrderedAddCommGroup EudoxusReal :=
  .mkOfPositiveCone totalPositiveCone

end EudoxusReal

end Integers
