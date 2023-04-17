import RealsQuasiMorphisms.Ring
import RealsQuasiMorphisms.Order

import Mathlib.Algebra.Order.Field.Defs

lemma int_wf_of_lower_bound (s : Set ℤ) (a : ℤ) (h : a ∈ lowerBounds s)
    : s.IsWf :=
  -- Anything works in place of `.natAbs` as long as it sends non-negative
  -- integers to the corresponding natural numbers and we can easily
  -- prove that it does so.
  have : ∀ x : s, (x - a).natAbs = ↑x - a := fun ⟨_, h_x⟩ =>
    Eq.symm <| Int.eq_natAbs_of_zero_le <| Int.sub_nonneg_of_le (h h_x)
  have : (fun x y : s => (x:ℤ) < y) = Measure (fun x : s => x - a |>.natAbs) := by
    ext x y
    unfold Measure InvImage; dsimp; rewrite [←Int.ofNat_lt, this, this]
    show (x:ℤ) < y ↔ x - a < y - a  -- can't find a lemma for this, so proving it
    apply Iff.intro
    · apply Int.sub_lt_sub_right (c := a)
    · conv => rhs; rewrite [←Int.sub_add_cancel x a,
                            ←Int.sub_add_cancel y a]
      apply Int.add_lt_add_right (c := a)
  by unfold Set.IsWf Set.WellFoundedOn; rewrite [this]; apply IsWellFounded.wf

namespace AlmostHom

private noncomputable def invAlmostHom_pos
    {f : AlmostHom ℤ} (hb : ¬f.Bounded) (hf : f.NonNeg)
    : AlmostHom ℤ where
  toFun :=
    have h : ¬(⇑f).BddAboveOn (Set.Ici 0) := by
      rewrite [←AlmostHom.nonpos_iff_bddAbove_on_nonneg]
      exact mt (AlmostHom.bounded_of_nonneg_of_nonpos hf) hb
    have h_pos := diverges_nonneg_of_nonneg_of_not_bddAbove_on_nonneg h
    have h_neg := diverges_nonpos_of_nonneg_of_not_bddAbove_on_nonneg h
    fun n =>
    let hl := { m : ℤ | f m ≥ n }
    have hwf : hl.IsWf := by
      let ⟨N, hN⟩ := h_neg (n-1)
      apply int_wf_of_lower_bound _ (-N)
      intro a ha
      simp only [ge_iff_le, Set.mem_setOf_eq] at ha
      specialize hN a
      have contra := mt hN
      push_neg at contra
      exact le_of_lt (contra $ Int.sub_one_lt_of_le ha)
    have hnbd : hl.Nonempty := by
      unfold Function.BddAboveOn Function.BddAboveOnBy at h; push_neg at h
      let ⟨N, _, h⟩ := h (n-1)
      exact ⟨N, Int.le_of_sub_one_lt h⟩
    Set.IsWf.min hwf hnbd
  almostAdditive := sorry

protected noncomputable def inv (f : AlmostHom ℤ) (h : ¬f.Bounded)
    : AlmostHom ℤ :=
  have h' : ¬(-f).Bounded := (mt (boundedAlmostHoms ℤ).neg_mem' (by rwa [neg_neg f]))
  dite (h := Classical.dec f.NonNeg)
    (f.invAlmostHom_pos h ·)
    (Neg.neg <|
      (-f).invAlmostHom_pos h' <|
        Or.resolve_left f.nonneg_total_integers ·)

protected theorem mul_inv {f : AlmostHom ℤ} (h : ¬f.Bounded)
    : -f.comp (f.inv h) + AlmostHom.id |>.Bounded :=
  sorry

end AlmostHom

/-! It would be suboptimal to attempt to directly define the inverse
of a `EudoxusReal` directly, as that requires showing that the
definition is independent of the choice of representing `AlmostHom`.

It is easier to use the above to show that there exists an inverse and
rely on general abstract algebra to go from there to a field. -/

namespace EudoxusReal

noncomputable instance instField : Field EudoxusReal :=
  IsField.toField {
    exists_pair_ne := Nontrivial.exists_pair_ne
    mul_comm := CommRing.mul_comm
    mul_inv_cancel := fun {a} => Quotient.inductionOn a fun f h =>
      have h : ¬f.Bounded := show f ∉ boundedAlmostHoms ℤ from
                             mt (QuotientAddGroup.eq_zero_iff f).mpr h
      ⟨f.inv h, (QuotientAddGroup.eq ..).mpr (f.mul_inv h)⟩
  }

noncomputable instance : LinearOrderedField EudoxusReal :=
  { instField, inferInstanceAs (LinearOrderedAddCommGroup EudoxusReal) with
    zero_le_one :=
      ⟨0, fun {n} (h : n ≥ 0) => show n - 0 ≥ 0 from Int.sub_zero n |>.symm ▸ h⟩
    mul_pos := fun a b h_a h_b => sorry }

end EudoxusReal
