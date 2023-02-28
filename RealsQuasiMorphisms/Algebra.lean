import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Hom.Group
import Aesop

import Util.Arithmetic
import RealsQuasiMorphisms.Basic

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
        ⦃f₁ f₂ : AlmostHom G⦄ (h : ∃ bound : ℕ, Bounded (-f₁ + f₂) bound)
    : ∃ bound : ℕ, Bounded (-f.comp f₁ + f.comp f₂) bound :=
  let ⟨_, h'⟩ := h; let ⟨_, h⟩ := f.almostAdditive
  ⟨_, h.comp_congr_right h'⟩

/-- Concrete statement of additivity of `QuasiHom.comp` wrt second argument. -/
lemma almost_comp_add (f : AlmostHom ℤ) (f₁ f₂ : AlmostHom G)
    : ∃ bound : ℕ, Bounded (-f.comp (f₁ + f₂) + (f.comp f₁ + f.comp f₂)) bound :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, h.almost_comp_add f₁ f₂⟩

/-- Left distributivity of composition over addition. -/
lemma add_comp (f : AlmostHom G) (f₁ f₂ : AlmostHom ℤ)
    : (f₁ + f₂).comp f = f₁.comp f + f₂.comp f := by ext; rfl

/-- If f₁ is bounded then f₁ ∘ f₂ is bounded. -/
lemma bounded_comp (f₂ : AlmostHom G)
                   ⦃f₁ : AlmostHom ℤ⦄ (h : ∃ bound : ℕ, Bounded f₁ bound)
    : ∃ bound : ℕ, Bounded (f₁.comp f₂) bound :=
  let ⟨bound, h⟩ := h; ⟨bound, fun g => h (f₂ g)⟩

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

private def mul_comm (a b : QuasiHom ℤ) : smulHom a b = smulHom b a := 
  sorry

/- For some reason LSP is quite slow if it is allowed to work on this instance declaration. -/
#exit
instance : Field (QuasiHom ℤ) :=
  let mul : Mul (QuasiHom ℤ) := ⟨ fun f g => smulHom f g ⟩
  {
    sub_eq_add_neg := SubNegMonoid.sub_eq_add_neg
    left_distrib := by intros _ _ _;  apply AddMonoidHom.map_add
    right_distrib := right_distrib
      -- aesop? (add norm unfold [HMul.hMul, Mul.mul], norm simp AddMonoidHom.map_add, safe apply AddMonoidHom.add_apply)
    mul_comm := sorry
    zero_mul  := zero_mul
    mul_zero  := mul_zero
    mul_assoc := mul_assoc
    one :=  one
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
