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

example (a b c : ℤ) : a - b ≤ c -> a ≤ c + b  := fun a_1 => Int.le_add_of_sub_right_le a_1
example (a b c : ℤ) : a + b ≤ c + b -> a ≤ c  := fun a_1 => le_of_add_le_add_right a_1

def unbounded_below (f : AlmostHom ℤ) (hb : f ∉ boundedAlmostHoms ℤ) (hf : f.NonNeg)
    : ∀ n, ∃ k, f k ≤ n := by
  have pos := bdd_and_nonneg_of_pos hf hb
  let ⟨b', hb'⟩ := almost_neg f
  simp only [boundedAlmostHoms, AddSubgroup.mem_mk, Set.mem_setOf_eq, not_exists, _root_.Bounded, Bounded] at hb
  push_neg at hb
  let ⟨k, hf⟩ := hf
  intro n
  specialize hb $ |n| + b'
  let ⟨g, hb⟩ := hb
  have :=  Int.le_add_of_sub_right_le $ Int.sub_le_natAbs_sub (f (-g)) (-f g)
  simp only [sub_neg_eq_add, Int.natAbs_neg] at this
  simp at hb'
  use -g
  calc
    f (-g) ≤ |f (-g)| := Int.le_natAbs
         _ ≤ |f (-g) + f g| + |f g| := this
         _ ≤ b' + |f g| := by rw [add_le_add_iff_right]; norm_cast; exact hb' g
         _ ≤ n := sorry
      /- _ ≤ sorry := sorry -/
  /- exact ⟨-g, calc -/
  /-   f g ≤ |f g| := Int.le_natAbs -/
  /-     _ ≤ -/
    /- _ ≤ sorry := sorry⟩ -/


noncomputable def invFun (f : AlmostHom ℤ) (hb : b ∉ boundedAlmostHoms ℤ) (hf : f.NonNeg)
    : ℤ → ℤ := by
  intro n
  let hl := { m : ℤ | f m ≥ n }
  have hwf : Set.IsWf $ hl := by
    let ⟨k, hf⟩ := hf
    simp only [boundedAlmostHoms, AddSubgroup.mem_mk, Set.mem_setOf_eq,
               not_exists, Bounded] at hb
    push_neg at hb
    apply int_wf_of_lower_bound _ $ k
    rw [lowerBounds]
    intro a ha
    simp at ha
    sorry

    /- rw [Set.IsWf] -/
    /- apply bdd_below.well_founded_on_lt -/
  have hnbd : hl.Nonempty := sorry
  exact Set.IsWf.min hwf hnbd

lemma infFunAlmosthom (f : AlmostHom ℤ) (hb : f ∉ boundedAlmostHoms ℤ) (hf : f.NonNeg) :
    ∃ k : ℕ, ∀ n₁ n₂, |(invFun f hb hf) (n₁ + n₂)  - (invFun f hb hf) n₁ - (invFun f hb hf) n₂| ≤ k := sorry

def neg_id  : AlmostHom ℤ :=
  ⟨fun n => -n, 0, by
    intro n₁ n₂
    simp only [neg_add_rev, sub_neg_eq_add,
    neg_add_cancel_right, sub_self, Int.natAbs_zero, le_refl]⟩

noncomputable def inv (f : AlmostHom ℤ) (hf : f ∉ boundedAlmostHoms ℤ) : AlmostHom ℤ := by
  have pos_inv (g : AlmostHom ℤ) (hgb : g ∉ boundedAlmostHoms ℤ) (hg : g.NonNeg) : AlmostHom ℤ := by
    exact
      ⟨invFun g hgb hg, infFunAlmosthom g hgb hg⟩
  by_cases f.NonNeg
  case pos => exact pos_inv f hf h
  case neg =>
    exact -(pos_inv (-f) (by rwa [neg_mem_iff ..]) (Or.resolve_left f.nonneg_total h))

private def inv (a : QuasiHom ℤ) : QuasiHom ℤ := by
  /- have : @DecidablePred (AlmostHom ℤ) (AlmostHom.Bounded)  := Classical.decPred _ -/
  /- have : ∀ f : AlmostHom ℤ, @Decidable (f ∈ boundedAlmostHoms ℤ) := by sorry -/
  open QuotientAddGroup in
  refine
    lift (boundedAlmostHoms ℤ)
    fun f => by
      by_cases c: f ∈ boundedAlmostHoms ℤ
      · exact (0 : AlmostHom ℤ)
      · exact AlmostHom.inv f c
      -- if c: (f ∈ boundedAlmostHoms ℤ) then 0 else AlmostHom.inv f c
  sorry

