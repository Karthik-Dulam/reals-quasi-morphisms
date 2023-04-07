import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Hom.Group
import Aesop

import Util.Arithmetic
import RealsQuasiMorphisms.Basic
import RealsQuasiMorphisms.Order

open scoped Int.natAbs

variable {G : Type _} [AddCommGroup G]

section Comp
namespace AlmostAdditive

/-- The composition of almost additive functions (on appropriate domains) is
almost additive. -/
protected theorem comp
        ⦃f₁ : ℤ → ℤ⦄ ⦃bound₁ : ℕ⦄ (h₁ : AlmostAdditive f₁ bound₁)
        ⦃f₂ : G → ℤ⦄ ⦃bound₂ : ℕ⦄ (h₂ : AlmostAdditive f₂ bound₂)
    : AlmostAdditive (f₁ ∘ f₂) <|
        (bound₁ + |f₁ 1|) * bound₂ + bound₁ * 3 := fun x y =>
  calc |f₁ (f₂ (x + y)) - f₁ (f₂ x) - f₁ (f₂ y)|
    ≤ |f₁ (f₂ (x + y)) - f₁ (f₂ (x + y) - f₂ x - f₂ y) - f₁ (f₂ x + f₂ y)|
      + |f₁ (f₂ (x + y) - f₂ x - f₂ y)|
      + |f₁ (f₂ x + f₂ y) - f₁ (f₂ x) - f₁ (f₂ y)|
        := by lax_exact Int.natAbs_add_le₃ (f₁ (f₂ (x + y)) - f₁ (f₂ (x + y) - f₂ x - f₂ y) - f₁ (f₂ x + f₂ y))
                                           (f₁ (f₂ (x + y) - f₂ x - f₂ y))
                                           (f₁ (f₂ x + f₂ y) - f₁ (f₂ x) - f₁ (f₂ y))
              linarith
  _ ≤ bound₁
      + ((bound₁ + |f₁ 1|) * |f₂ (x + y) - f₂ x - f₂ y| + bound₁)
      + bound₁
        := by conv in f₁ (f₂ (x + y)) =>
                /- Need `f₂ (x + y)` like this to use `h₁.almost_additive`. -/
                rw [show f₂ (x + y) = (f₂ (x + y) - f₂ x - f₂ y) + (f₂ x + f₂ y)
                    by linarith]
              refine Nat.add_le_add₃ ?_ ?using_lemma ?_;
              case using_lemma => apply h₁.linear_growth_upper_bound_int
              all_goals apply h₁.almost_additive
  _ = (bound₁ + |f₁ 1|) * |f₂ (x + y) - f₂ x - f₂ y| + bound₁ * 3 := by linarith
  _ ≤ (bound₁ + |f₁ 1|) * bound₂ + bound₁ * 3
        := h₂.almost_additive .. |> Nat.mul_le_mul_left (k := _)
                                 |> Nat.add_le_add_right (k := _)

/-- If f₂ - f₁ is bounded then f ∘ (f₂ - f₁) is bounded. -/
lemma comp_congr_right
        ⦃f  : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f  bound)
        ⦃f₁ f₂ : G → ℤ⦄ ⦃bound' : ℕ⦄ (h' : Bounded (-f₁ + f₂) bound')
    : Bounded (-f.comp f₁ + f.comp f₂) <|
        (bound + |f 1|) * bound' + bound * 2 := fun g =>
  calc |(-f (f₁ g)) + f (f₂ g)|
      = |f (f₁ g + (f₂ g - f₁ g)) - f (f₁ g) - f (f₂ g - f₁ g)
         + f (f₂ g - f₁ g)|
          := congrArg Int.natAbs <| by
               rw [Int.add_sub_cancel_right (f₁ g) (f₂ g),
                   ←Int.sub_eq_neg_add, Int.sub_add_cancel]
    _ ≤ bound + ((bound + |f 1|) * |f₂ g - f₁ g| + bound)
          := Trans.trans (Int.natAbs_add_le ..) <| Nat.add_le_add
               (h.almost_additive ..)
               (h.linear_growth_upper_bound_int ..)
    _ ≤ (bound + |f 1|) * bound' + bound * 2
          := by have : |f₂ g - f₁ g| ≤ bound' := Int.sub_eq_neg_add .. ▸ h' g
                have := Nat.mul_le_mul_left (bound + (f 1).natAbs) this
                linarith [this]

/-- Composition of almost additive functions is distributive over addition on
the right, up to a bounded function. -/
lemma almost_comp_add
        ⦃f  : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f  bound)
        (f₁ f₂ : G → ℤ)
    : Bounded (-f ∘ (f₁ + f₂) + (f ∘ f₁ + f ∘ f₂)) bound := fun g => by
  show |(-f (f₁ g + f₂ g)) + (f (f₁ g) + f (f₂ g))| ≤ bound
  rewrite [←Int.natAbs_neg]
  lax_exact h.almost_additive (f₁ g) (f₂ g); linarith

end AlmostAdditive

namespace AlmostHom

/-- Composition of almost-homomorphisms (with appropriate domains), returning
another almost-homomorphism. -/
protected def comp  (f₁ : AlmostHom ℤ) (f₂ : AlmostHom G) : AlmostHom G where
  toFun := f₁ ∘ f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    -- bound is filled in based on the proof :)
    ⟨_, AlmostAdditive.comp h₁ h₂⟩

/-- Concrete statement of well-defined-ness of `QuasiHom.comp` wrt second argument. -/
lemma comp_congr_right (f : AlmostHom ℤ)
        ⦃f₁ f₂ : AlmostHom G⦄ (h : -f₁ + f₂ |>.Bounded)
    : -f.comp f₁ + f.comp f₂ |>.Bounded :=
  let ⟨_, h'⟩ := h; let ⟨_, h⟩ := f.almostAdditive
  ⟨_, h.comp_congr_right h'⟩

/-- Concrete statement of additivity of `QuasiHom.comp` wrt second argument. -/
lemma almost_comp_add (f : AlmostHom ℤ) (f₁ f₂ : AlmostHom G)
    : -f.comp (f₁ + f₂) + (f.comp f₁ + f.comp f₂) |>.Bounded :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, h.almost_comp_add f₁ f₂⟩

/-- Left distributivity of composition over addition. -/
lemma add_comp (f : AlmostHom G) (f₁ f₂ : AlmostHom ℤ)
    : (f₁ + f₂).comp f = f₁.comp f + f₂.comp f := by ext; rfl
/-- If f₁ is bounded then f₁.comp f₂ is bounded. -/
lemma bounded_comp (f₂ : AlmostHom G)
                   ⦃f₁ : AlmostHom ℤ⦄ (h : f₁.Bounded)
    : f₁.comp f₂ |>.Bounded :=
  let ⟨bound, h⟩ := h; ⟨bound, fun g => h (f₂ g)⟩

/-- Composition of AlmostHoms f g is almost equal to (f n * g n)/n -/
private lemma comp_almost_mul (f₁ f₂ : AlmostHom ℤ) 
    : ∃ k, ∀ n, |n * (f₁.comp f₂ n) - f₂ n * f₁ n| ≤ (|n| + 1) * k := by
  let ⟨a', b', hlin⟩ := linear_growth_upper_bound_int f₂
  let ⟨b₁, hf₁⟩ := f₁.almostAdditive 
  exact ⟨_, by
    intro n
    have hypcomm := AlmostAdditive.almost_smul_interchange (hf₁) (f₂ n) n 1
    specialize hlin n
    simp only [smul_eq_mul, mul_one] at hypcomm
    calc |n * (f₁.comp f₂ n) - f₂ n * f₁ n| 
        ≤ b₁*(|f₂ n| + |n| + 2) := hypcomm
      _ ≤ b₁*(a'*|n| + b' + |n| + 2) := 
          by apply mul_le_mul_of_nonneg_left 
              (by simp only [add_le_add_iff_right, hlin]) (zero_le _)
      _ = b₁*(|n| * (a' + 1) + (b'+ 2)) := by ring
      _ ≤ b₁*(|n| * (a' + 1) + (b'+ 2)) + b₁*(a'+1) := 
          by simp only [le_add_iff_nonneg_right, zero_le]
      _ ≤ b₁*(|n| * (a' + 1) + (b'+ 2)) + b₁*(a'+1) + b₁*(|n|)*(b'+2) := 
          by simp only [le_add_iff_nonneg_right, zero_le]
      _ = (|n|+1)*(b₁*(a'+1 + b'+2)) := by ring
  ⟩

lemma succ_le_two_mul (a : ℕ) (ha : a ≠ 0) : a+1 ≤ 2*a := by cases a; contradiction; apply Nat.succ_le.2; linarith [NeZero.pos]

/-- Composition of AlmostHoms is commutative. -/
lemma comp_almost_comm (f₁ f₂ : AlmostHom ℤ) 
    : (f₁.comp f₂) - (f₂.comp f₁) ∈ boundedAlmostHoms ℤ := by
  simp only [boundedAlmostHoms, Bounded, AddSubgroup.mem_mk, Set.mem_setOf_eq]
  let ⟨k₁, hf₁⟩ := comp_almost_mul f₁ f₂
  let ⟨k₂, hf₂⟩ := comp_almost_mul f₂ f₁
  exact ⟨_, by 
    intro n
    have triag := Int.natAbs_add_le (n * (f₁.comp f₂ n) - f₂ n * f₁ n) (f₂ n * f₁ n - n * (f₂.comp f₁ n))
    simp only [sub_add_sub_cancel, Int.diff_eq] at triag
    if c: n = 0 
    then 
      simp only [c, zero_mul, zero_sub, Int.natAbs_neg, ge_iff_le] at hf₁ hf₂ |-
      exact self_le_add_right |(f₁.comp f₂ - f₂.comp f₁) 0| (2*(k₁ + k₂))
    else 
    have goal_mul_n := 
      calc 
        |n| * |f₁.comp f₂ n - f₂.comp f₁ n|
          = |n*f₁.comp f₂ n - n*f₂.comp f₁ n| := by rw [←Int.natAbs_mul, mul_sub_left_distrib]
        _ ≤ |n*f₁.comp f₂ n - f₂ n * f₁ n| + |f₂ n * f₁ n - n*f₂.comp f₁ n| := triag
        _ ≤ |n*f₁.comp f₂ n - f₂ n * f₁ n| + (|n|+1)*k₂  := 
            by 
              rw [mul_comm $ f₂ n, ←Int.natAbs_neg (f₁ n * f₂ n - n*f₂.comp f₁ n)]
              apply Nat.add_le_add_left; 
              simp only [neg_sub, Int.diff_eq]; exact hf₂ ..
        _ ≤ (|n|+1)*k₁ + (|n|+1)*k₂ := Nat.add_le_add_right (hf₁ ..) ..
        _ = (|n|+1)*(k₁ + k₂) := by ring
        _ ≤ |n| * (2*(k₁ + k₂)) := 
            by 
              rw [←mul_assoc, mul_comm |n|]
              exact Nat.mul_le_mul_of_nonneg_right 
                <| succ_le_two_mul |n| 
                <| Int.natAbs_ne_zero.2 c
    calc |f₁.comp f₂ n - f₂.comp f₁ n| 
      ≤ 2*(k₁ + k₂) := le_of_mul_le_mul_left goal_mul_n 
        <| Or.resolve_left (Nat.eq_zero_or_pos ..) (Int.natAbs_ne_zero.2 c)
    _ ≤ _ := self_le_add_left  (2*(k₁ + k₂)) |(f₁.comp f₂ - f₂.comp f₁) 0| ⟩



variable {α : Type _} {s : Set α} [Preorder α] [LocallyFiniteOrder α]

lemma bdd_below.well_founded_on_lt : BddBelow s → s.WellFoundedOn (·<·)  := sorry

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


def almostSurj (f : AlmostHom ℤ) (hb : f ∉ boundedAlmostHoms ℤ) (hf : f.nonneg) 
    : ∀ n, ∃ k, f k ≤ n := by 
  simp only [boundedAlmostHoms, AddSubgroup.mem_mk, Set.mem_setOf_eq, not_exists, Bounded] at hb
  push_neg at hb
  let ⟨k, hf⟩ := hf
  intro n
  specialize hb |n|
  let ⟨g, hb⟩ := hb
  by_cases c : f g ≥ 0
  
  

noncomputable def invFun (f : AlmostHom ℤ) (hb : b ∉ boundedAlmostHoms ℤ) (hf : f.nonneg) 
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

lemma infFunAlmosthom (f : AlmostHom ℤ) (hb : f ∉ boundedAlmostHoms ℤ) (hf : f.nonneg) : 
    ∃ k : ℕ, ∀ n₁ n₂, |(invFun f hb hf) (n₁ + n₂)  - (invFun f hb hf) n₁ - (invFun f hb hf) n₂| ≤ k := sorry

def neg_id  : AlmostHom ℤ :=
  ⟨fun n => -n, 0, by 
    intro n₁ n₂
    simp only [neg_add_rev, sub_neg_eq_add, 
    neg_add_cancel_right, sub_self, Int.natAbs_zero, le_refl]⟩

noncomputable def inv (f : AlmostHom ℤ) (hf : f ∉ boundedAlmostHoms ℤ) : AlmostHom ℤ := by
  have pos_inv (g : AlmostHom ℤ) (hgb : g ∉ boundedAlmostHoms ℤ) (hg : g.nonneg) : AlmostHom ℤ := by 
    exact
      ⟨invFun g hgb hg, infFunAlmosthom g hgb hg⟩
  by_cases f.nonneg
  case pos => exact pos_inv f hf h
  case neg =>
    exact -(pos_inv (-f) (by rwa [neg_mem_iff ..]) (Or.resolve_left f.nonneg_total h))


end AlmostHom


-- Tidy up the proof and add it to suitable namespace
@[aesop norm unfold] def smulHom : QuasiHom ℤ →+ QuasiHom G →+ QuasiHom G := by
  /- Skeleton. This is glue code tying `Quotient`s and
  `QuotientAddGroup`s and `MonoidHom`-related functions to define the
  homomorphism in terms of the actual concrete proofs needed, which
  are given as holes (except for the function, which is filled in). -/
  open QuotientAddGroup in
  refine
    lift (boundedAlmostHoms ℤ)
      (AddMonoidHom.mk' (fun f => AddMonoidHom.mk'
          (Quotient.map (sa := leftRel _) (sb := leftRel _)
            /- Function definition -/
            f.comp
            /- Well-defined wrt second arg -/
            (fun f₁ f₂ =>
              show (leftRel _).r .. → (leftRel _).r ..
                by (repeat rewrite [leftRel_apply]); exact
              f.comp_congr_right (f₁ := f₁) (f₂ := f₂)))
          /- Hom wrt second arg as `QuasiHom G` -/
          (Quotient.ind₂ <| fun g₁ g₂ => Quotient.sound <|
           show (leftRel _).r (f.comp (g₁ + g₂)) (f.comp g₁ + f.comp g₂)
             by rewrite [leftRel_apply]; exact
           f.almost_comp_add g₁ g₂))
        /- Hom wrt first arg as `AlmostHom ℤ` -/
        fun f₁ f₂ =>
          AddMonoidHom.ext <|
          Quotient.ind <| fun g => congrArg mk <|
          g.add_comp f₁ f₂)
      /- Show output is 0 if first arg is in `boundedAlmostHoms ℤ`
      (i.e, well-defined wrt first arg as `QuasiHom ℤ`) -/
      fun f h =>
        AddMonoidHom.ext <|
        Quotient.ind <| fun g => Quotient.sound <| by
          simp only [HasEquiv.Equiv, leftRel_apply];
          show -f.comp g + 0 ∈ boundedAlmostHoms G
          rewrite [add_zero, neg_mem_iff]; exact g.bounded_comp h

namespace QuasiHom

/- The following 'helper lemmas' are for showing field structure. -/

private lemma right_distrib (a b c : QuasiHom ℤ) :
    smulHom (a + b) c = smulHom a c + smulHom b c := by
  rw [AddMonoidHom.map_add]; apply AddMonoidHom.add_apply

private lemma zero_mul (a : QuasiHom ℤ) : smulHom 0 a = 0 := by
  simp only [map_zero, AddMonoidHom.zero_apply]

private lemma mul_zero (a : QuasiHom ℤ) : @smulHom ℤ _ a 0 = 0 := by
  simp only [map_zero]

private lemma mul_assoc (a b c : QuasiHom ℤ) :
    smulHom (smulHom a b) c = smulHom a (smulHom b c) := by
  apply QuotientAddGroup.induction_on a
  apply QuotientAddGroup.induction_on b
  apply QuotientAddGroup.induction_on c
  intro _ _ _; rfl

private def one : QuasiHom ℤ := ⟦ ⟨ fun n => n, ⟨0, by intros _ _ ; simp only
                      [add_sub_cancel', sub_self,
                      Int.natAbs_zero, le_refl]⟩⟩  ⟧

private def one_mul  (a : QuasiHom ℤ) : smulHom one a = a := by
  apply QuotientAddGroup.induction_on a; intro _; rfl

private def mul_one (a : QuasiHom ℤ) : smulHom a one = a := by
  apply QuotientAddGroup.induction_on a; intro _; rfl

private def inv (a : QuasiHom ℤ) : QuasiHom ℤ := by
  sorry

private def exists_pair_ne : one ≠ ⟦⟨0, 0, fun _ _ => Nat.le_refl ..⟩⟧ := by
  /- rewrite [show ∀ a : QuasiHom ℤ, a ≠ 0 ↔ ¬a = 0 by intro; rfl] -/
  /- by_contra h -/
  /- apply QuotientAddGroup.eq -/
  
  /- apply Quotient.exact  (⟨ fun n => n, ⟨0, by intros _ _ ; simp only -/
  /-                         [add_sub_cancel', sub_self, -/
  /-                         Int.natAbs_zero, le_refl]⟩⟩) -/
  /- have := Quotient.exact h; -/
  /- simp [funext] at this; -/ 
  sorry

private def mul_comm (a b : QuasiHom ℤ) : smulHom a b = smulHom b a := by
  apply QuotientAddGroup.induction_on a
  apply QuotientAddGroup.induction_on b
  intro a b
  rw [smulHom]
  apply (QuotientAddGroup.eq ..).2
  rw [add_comm]
  show a.comp b - b.comp a ∈ boundedAlmostHoms ℤ
  exact AlmostHom.comp_almost_comm a b

/- For some reason LSP is quite slow if it is allowed to work on this instance declaration. -/
#exit
instance : Field (QuasiHom ℤ) :=
  let mul : Mul (QuasiHom ℤ) := ⟨ fun f g => smulHom f g ⟩
  {
    sub_eq_add_neg := SubNegMonoid.sub_eq_add_neg
    left_distrib := by intros _ _ _;  apply AddMonoidHom.map_add
    right_distrib := right_distrib
      -- aesop? (add norm unfold [HMul.hMul, Mul.mul], norm simp AddMonoidHom.map_add, safe apply AddMonoidHom.add_apply)
    mul_comm := mul_comm
    zero_mul  := zero_mul
    mul_zero  := mul_zero
    mul_assoc := mul_assoc
    one := one
    one_mul := one_mul
    mul_one := mul_one
    add_left_neg := add_left_neg
    inv := sorry
    exists_pair_ne := sorry
    mul_inv_cancel := sorry
    inv_zero := sorry
  }

end QuasiHom

end Comp
