import RealsQuasiMorphisms.Ring
import RealsQuasiMorphisms.Order

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

private noncomputable def invFun_pos {f : AlmostHom ℤ}
    (hb : ¬f.Bounded) (hf : f.NonNeg)
    : ℤ → ℤ := by
  have h : ¬(⇑f).BddAboveOn (Set.Ici 0) := by
    rewrite [←AlmostHom.nonpos_iff_bddAbove_on_nonneg]
    exact mt (AlmostHom.bounded_of_nonneg_of_nonpos hf) hb
  have hdiv := diverges_nonpos_of_nonneg_of_not_bddAbove_on_nonneg h
  have hdiv' := diverges_nonneg_of_nonneg_of_not_bddAbove_on_nonneg h
  intro n
  let hl := { m : ℤ | f m ≥ n }
  have hwf : hl.IsWf := by
    let ⟨N, hN⟩ := hdiv (n-1)
    apply int_wf_of_lower_bound _ (-N)
    intro a ha
    simp only [ge_iff_le, Set.mem_setOf_eq] at ha
    specialize hN a
    have contra := mt hN
    push_neg at contra
    exact le_of_lt (contra $ Int.sub_one_lt_of_le ha)
  have hnbd : hl.Nonempty := by
    let ⟨N, hN⟩ := hdiv' n
    specialize hN N (by exact le_refl ..)
    use N
    assumption
  exact Set.IsWf.min hwf hnbd

private noncomputable def invAlmostHom_pos {f : AlmostHom ℤ} (hb : ¬f.Bounded) (hf : f.NonNeg)
    : AlmostHom ℤ where
  toFun := f.invFun_pos hb hf
  almostAdditive := sorry

noncomputable def inv (f : AlmostHom ℤ) (hf : ¬f.Bounded) : AlmostHom ℤ :=
  dite (h := Classical.dec f.NonNeg)
    (f.invAlmostHom_pos hf ·)
    (Neg.neg <|
      (-f).invAlmostHom_pos (mt (boundedAlmostHoms ℤ).neg_mem' (by rwa [neg_neg f])) <|
      Or.resolve_left f.nonneg_total_integers ·)

end AlmostHom
