import RealsQuasiMorphisms.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.Cone


variable {G : Type _} [OrderedAddCommGroup G]

namespace AlmostHom

/-- An almost-homomorphism `f : G → ℤ` is non-negative if the image (under `f`) of `G ≥ 0` is bounded below. -/
protected def nonneg (f : AlmostHom G) : Prop := ∃ a : ℤ , ∀ x : G, x ≥ 0 → f x ≥ a
/-- An almost-homomorphism `f : G → ℤ` is non-positive if the image (under `f`) of `G ≥ 0` is bounded above (unused). -/
protected def nonpos (f : AlmostHom G) : Prop := ∃ b : ℤ , ∀ x : G, x ≥ 0 → f x ≤ b
/-- `f ≤ g` is equivalent to stating `g - f` is non-negative. -/
protected def le (f g : AlmostHom G) : Prop := AlmostHom.nonneg (g - f)


-- why exactly this is needed is well beyond me
private lemma add_reduces_to_fun (f g : AlmostHom G) : toFun (f + g) = toFun f + toFun g := by rfl
private lemma neg_reduces_to_fun (f : AlmostHom G) : toFun (-f) = - toFun f:= by rfl
private lemma sub_reduces_to_fun (f g : AlmostHom G) : toFun (f - g) = toFun f - toFun g := by rfl


/-- `AlmostHom.le` as defined  gives us a preorder on `AlmostHom G`. -/
instance : Preorder (AlmostHom G) where
  le := AlmostHom.le
  le_refl f := by
                simp only [AlmostHom.le, AlmostHom.nonneg, sub_self]
                use -1; intro x _
                show -1 ≤ 0; simp only [Left.neg_nonpos_iff]
  le_trans p q r:= by
                    intro hpq hqr
                    let ⟨a, hpq⟩ := hpq; let ⟨b, hqr⟩ := hqr
                    use a+b; intro x hx
                    simp only [sub_reduces_to_fun, Pi.sub_apply, ge_iff_le] at hpq hqr ⊢ 
                    let h := add_le_add (hpq x hx) (hqr x hx)
                    rw [sub_add_sub_cancel'] at h
                    apply h


/- Adding a bounded function to any other can only change the image of
any element by at most some bound. Thus any lower bound is preserved
up to a shift in the bound. -/
private lemma bounded_plus_nonneg_nonneg' (f : AlmostHom G)
        ⦃g : AlmostHom G⦄ (h : ∃ bound : ℕ, Bounded g bound)
    : f.nonneg → (f + g).nonneg := by
  intro hf
  let ⟨bound, hb⟩ := h
  rw [Bounded] at hb
  let ⟨a, ha⟩ := hf
  use a - bound; intro x hx
  have hb : -bound ≤ g.toFun x := by
    simp only [←Int.ofNat_le, Int.coe_natAbs, abs_le] at hb
    exact (hb x).left
  exact add_le_add (ha x hx) hb

/-- If `f` is a non-negative almost-homomorphism and `g` is bounded, then `f + g` is non-negative. -/
protected theorem bounded_plus_nonneg_nonneg {f : AlmostHom G} (g : boundedAlmostHoms G)
    : f.nonneg → (f + g).nonneg := by
  exact AlmostHom.bounded_plus_nonneg_nonneg' f g.property

/-- The almost-homomorphism 0 is non-negative. -/
protected lemma zero_nonneg : (0 : AlmostHom G).nonneg := by
  use -1; intro x _
  show -1 ≤ 0; simp only [Left.neg_nonpos_iff]

/-- If `f` and `g` are non-negative almost-homomorphisms then `f + g` is also non-negative. -/
protected lemma add_nonneg {f g : AlmostHom G} : f.nonneg → g.nonneg → (f + g).nonneg := by
  intro hf hg
  let ⟨a, ha⟩ := hf; let ⟨b, hb⟩ := hg
  use a + b; intro x hx
  exact add_le_add (ha x hx) (hb x hx)

-- this might exist somewhere already
private lemma neg_natAbs_le (a : ℤ) : -a.natAbs ≤ a := by
  simp only [←Int.ofNat_le, Int.coe_natAbs]
  exact neg_abs_le_self a

private lemma neg_le_natAbs (a : ℤ) : -a ≤ a.natAbs := by
  simp only [←Int.ofNat_le, Int.coe_natAbs]
  exact neg_le_abs_self a


-- this really need not be split up like this
private lemma nonneg_and_neg_nonneg_bounded' {f : AlmostHom G}
    : f.nonneg → (-f).nonneg → (∃ bound : ℕ, Bounded f bound) := by
  intro hf hf'
  let ⟨a, ha⟩ := hf; let ⟨b, hb⟩ := hf'
  let ⟨bound, hf⟩ := f.almostAdditive
  let y := f 0
  let nb := a.natAbs + b.natAbs + bound + y.natAbs
  use nb
  rw [Bounded]
  intro x
  by_cases hx:(x ≥ 0)
  · have h' : f x ≤ -b := by
      rw [le_neg]
      exact hb x hx
    let h'' := ha x hx
    simp only [←Int.ofNat_le, Int.coe_natAbs, abs_le]
    apply And.intro
    · have hga : a.natAbs ≤ nb := by
        simp only [add_assoc, le_add_iff_nonneg_right, zero_le]
      have hga : -nb ≤ -(↑a.natAbs : ℤ) := by
        simp only [←Int.ofNat_le] at hga
        simp only [neg_le_neg, hga]
      linarith [neg_natAbs_le a]
    · have hgb : Int.natAbs b ≤ Int.natAbs b + Int.natAbs a + bound + Int.natAbs (toFun f 0) := by
        simp only [add_assoc, le_add_iff_nonneg_right, zero_le]
      simp only [←Int.ofNat_le] at hgb
      have nbe : ↑(Int.natAbs b + Int.natAbs a + bound + Int.natAbs (toFun f 0)) = (↑nb : ℤ)  := by
        simp only [add_comm, Nat.cast_add, Int.coe_natAbs]
      linarith [neg_natAbs_le b]
  · sorry

/-- If `f` is an almost-homomorphism such that both `f` and `-f` are non-negative, then `f` is bounded. -/
protected lemma nonneg_and_neg_nonneg_bounded {f : AlmostHom G}
    : f.nonneg → (-f).nonneg → f ∈ boundedAlmostHoms G := by
  intro hf hf'
  let ⟨bound, hb⟩ := nonneg_and_neg_nonneg_bounded' (f := f) hf hf'
  use bound
  exact hb

/- This is a somewhat non-trivial result and not proven yet. -/
/-- If `f` is an almost-homomorphism, then at least one of `f` and `-f` must be non-negative. -/
protected lemma nonneg_total (f : AlmostHom G) : f.nonneg ∨ (-f).nonneg := by
  sorry

end AlmostHom


namespace QuasiHom

/-- A quasi-morphism `f` is non-negative if any representative almost-homomorphism is non-negative.

This is well-defined by `bounded_plus_nonneg_nonneg`. -/
protected def nonneg (f : QuasiHom G) : Prop := Quot.liftOn f AlmostHom.nonneg (λ f g h ↦ by
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
    apply AlmostHom.bounded_plus_nonneg_nonneg x hf
  · intro hg
    rw [h₂]
    apply AlmostHom.bounded_plus_nonneg_nonneg (-x) hg
  )


/-- The quasi-morphism 0 is non-negative. -/
protected lemma zero_nonneg : QuasiHom.nonneg (0 : QuasiHom G) := by
  apply AlmostHom.zero_nonneg

/-- The sum of two non-negative quasi-morphisms is non-negative. -/
protected lemma add_nonneg {f g : QuasiHom G} : f.nonneg → g.nonneg → (f + g).nonneg := by
  apply QuotientAddGroup.induction_on f
  apply QuotientAddGroup.induction_on g
  intro f g hf hg
  apply AlmostHom.add_nonneg hf hg

/-- If `f` and `-f` are both non-negative quasi-morphisms, then `f` must be `0`. -/
protected lemma nonneg_antisymm {f : QuasiHom G} : f.nonneg → (-f).nonneg → f = 0 := by
  apply QuotientAddGroup.induction_on f
  intro f hf hf'
  rw [QuotientAddGroup.eq_zero_iff]
  exact AlmostHom.nonneg_and_neg_nonneg_bounded hf hf'

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
