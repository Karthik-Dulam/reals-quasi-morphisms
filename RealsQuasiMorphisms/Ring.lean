import RealsQuasiMorphisms.Basic

import Util.Arithmetic

import Mathlib.Tactic.Abel

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

/-- The composition of an almost additive function with a bounded function is
bounded. -/
lemma almost_comp_bounded
        ⦃f : ℤ → ℤ⦄ ⦃bound  : ℕ⦄ (h : AlmostAdditive f bound)
        ⦃g : G → ℤ⦄ ⦃bound' : ℕ⦄ (h' : Bounded g bound')
    : Bounded (f ∘ g) <| (bound + |f 1|) * bound' + bound := fun x =>
  calc |f (g x)| ≤ (bound + |f 1|) * |g x| + bound
        := h.linear_growth_upper_bound_int (g x)
    _ ≤ (bound + |f 1|) * bound' + bound
        := h' x |> Nat.mul_le_mul_left (k:=_) |> Nat.add_le_add_right (k:=_)

/-- If -f₁ + f₂ is bounded then -f ∘ f₁ + f ∘ f₂ is bounded. -/
lemma comp_sub_bounded_of_sub_bounded
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f  bound)
        ⦃f₁ f₂ : G → ℤ⦄ ⦃bound' : ℕ⦄ (h' : Bounded (-f₁ + f₂) bound')
    : Bounded (-f ∘ f₁ + f ∘ f₂) <|
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
    _ ≤ bound + ((bound + |f 1|) * bound' + bound)
          := Int.sub_eq_neg_add .. ▸ h' g |>
               Nat.mul_le_mul_left (k:=bound + |f 1|) |>
               Nat.add_le_add_right (k:=_) |> Nat.add_le_add_left (k:=_)
    _ = (bound + |f 1|) * bound' + bound * 2
          := by rw [Nat.add_comm, Nat.add_assoc, Nat.mul_two]

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
protected def comp (f₁ : AlmostHom ℤ) (f₂ : AlmostHom G) : AlmostHom G where
  toFun := f₁ ∘ f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    -- bound is filled in based on the proof :)
    ⟨_, AlmostAdditive.comp h₁ h₂⟩

/-- The identity function on ℤ as an `AlmostHom`. -/
protected def id : AlmostHom ℤ where
  toFun := id
  almostAdditive :=
    ⟨0, fun m n => have : (m + n) - m - n = 0 := by abel
                   this ▸ show |0| ≤ 0 from Nat.le_refl 0⟩

/-- Concrete statement of well-defined-ness of `QuasiHom.comp` wrt second argument. -/
lemma comp_sub_bounded_of_sub_bounded (f : AlmostHom ℤ)
        ⦃f₁ f₂ : AlmostHom G⦄ (h : -f₁ + f₂ |>.Bounded)
    : -f.comp f₁ + f.comp f₂ |>.Bounded :=
  let ⟨_, h'⟩ := h; let ⟨_, h⟩ := f.almostAdditive
  ⟨_, h.comp_sub_bounded_of_sub_bounded h'⟩

/-- Concrete statement of additivity of `QuasiHom.comp` wrt second argument. -/
lemma almost_comp_add (f : AlmostHom ℤ) (f₁ f₂ : AlmostHom G)
    : -f.comp (f₁ + f₂) + (f.comp f₁ + f.comp f₂) |>.Bounded :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, h.almost_comp_add f₁ f₂⟩

/-- Left distributivity of composition over addition. -/
lemma add_comp (g : AlmostHom G) (f₁ f₂ : AlmostHom ℤ)
    : (f₁ + f₂).comp g = f₁.comp g + f₂.comp g := by ext; rfl

/-- If f₁ is bounded then f₁.comp f₂ is bounded. -/
lemma bounded_comp (f₂ : AlmostHom G)
                   ⦃f₁ : AlmostHom ℤ⦄ (h : f₁.Bounded)
    : f₁.comp f₂ |>.Bounded :=
  let ⟨bound, h⟩ := h; ⟨bound, fun g => h (f₂ g)⟩

end AlmostHom

namespace QuasiHom

/-- Multiplication of a `EudoxusReal` and a `QuasiHom G` as an bi-additive map. -/
def smulHom : EudoxusReal →+ QuasiHom G →+ QuasiHom G := by
  /- Skeleton. This is glue code tying `Quotient`- and
  `QuotientAddGroup`- and `MonoidHom`-related functions to define the
  homomorphism in terms of the actual concrete proofs needed. -/
  refine
    open QuotientAddGroup (lift leftRel) in
    open AddMonoidHom (mk') in
    open Quotient (map ind ind₂ sound) in
    lift (boundedAlmostHoms ℤ) (mk'
        -- AlmostHom ℤ → QuasiHom G →+ QuasiHom G
        (fun f => mk'
          -- QuasiHom G → QuasiHom G
          /- Note: we can't use QuotientAddGroup.mk because this is _not_ additive as a function `AlmostHom G → AlmostHom G`. -/
          (map (sa := leftRel _) (sb := leftRel _)
            -- AlmostHom G → AlmostHom G
            f.comp
            -- `AlmostHom G → AlmostHom G` lifts to `QuasiHom G → QuasiHom G`
            (fun _ _ => show (leftRel _).r .. → (leftRel _).r .. from ?well_def₂))
          -- `QuasiHom G → QuasiHom G` is additive
          (ind₂ fun _ _ => sound <| show (leftRel _).r .. from ?additive₂))
        -- `AlmostHom ℤ → …` is additive
        fun _ _ => AddMonoidHom.ext <| ind fun _ => sound <|
          show (leftRel _).r .. from ?additive₁)
      -- boundedAlmostHoms ℤ ⊆ kernel (AlmostHom ℤ →+ QuasiHom G →+ QuasiHom G)
      fun _ _ => AddMonoidHom.ext <| ind fun _ => sound <|
        show (leftRel _).r .. from ?well_def₁
  -- For this goal alone, we want to keep it as Setoid.r
  case additive₁ f₁ f₂ g =>
    rw [g.add_comp f₁ f₂]; exact (QuotientAddGroup.leftRel ..).refl ..
  all_goals repeat rewrite [QuotientAddGroup.leftRel_apply]
  case well_def₁ f h g =>
    rewrite [add_zero, neg_mem_iff]; exact g.bounded_comp h
  case well_def₂ g₁ g₂ =>
    exact f.comp_sub_bounded_of_sub_bounded (f₁ := g₁) (f₂ := g₂)
  case additive₂ g₁ g₂ =>
    exact f.almost_comp_add g₁ g₂

def smul (f : EudoxusReal) (g : QuasiHom G) : QuasiHom G :=
  smulHom f g

end QuasiHom

namespace EudoxusReal export QuasiHom (smulHom smul) end EudoxusReal

/- The following 'helper lemmas' are for showing field structure.

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
-/

namespace EudoxusReal

/-- The identity for the multiplication of `QuasiHom`s. -/
@[reducible]
instance : One EudoxusReal where
  one := ⟦AlmostHom.id⟧

/-- The multiplicative and additive identities of `EudoxusReal` are distinct. -/
lemma one_ne_zero : (1:EudoxusReal) ≠ 0 := by
  -- rewrite fails badly
  apply not_iff_not.mpr (QuotientAddGroup.eq ..) |>.mpr
  intro ⟨bound, h⟩              -- suppose ∀ n, |-id n + 0| ≤ bound
  -- Simplify type of `h`
  have h : ∀ n : ℤ, |(-n + 0)| ≤ bound := h
  have h : ∀ n : ℤ, |n| ≤ bound := fun n =>
    Int.neg_neg n ▸ Int.add_zero (- -n) ▸ h (-n)
  have : bound + 1 ≤ bound := by
    rewrite [←Int.natAbs_cast (bound + 1),
             show ↑(bound + 1) = ↑bound + 1 from rfl]
    exact h (bound + 1)
  apply Nat.not_succ_le_self; assumption

end EudoxusReal

namespace AlmostHom

/-- For `AlmostHom`s f₁ f₂ on ℤ, n * (f₁ (f₂ n)) is approximately (f₂ n * f₁ n). -/
lemma comp_almost_mul (f₁ f₂ : AlmostHom ℤ)
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
      _ = (|n|+1)*(b₁*(a'+1 + b'+2)) := by ring⟩

/-- Composition of `AlmostHom`s on ℤ is commutative upto a constant bound. -/
theorem comp_almost_comm (f₁ f₂ : AlmostHom ℤ)
    : -f₁.comp f₂ + f₂.comp f₁ |>.Bounded := by
  have succ_le_two_mul (a : ℕ) (ha : a ≠ 0) : a+1 ≤ 2*a := by
    cases a
    case zero => contradiction
    case succ => apply Nat.succ_le.2; linarith [NeZero.pos]
  simp only [Bounded, _root_.Bounded]
  let ⟨k₁, hf₁⟩ := comp_almost_mul f₁ f₂
  let ⟨k₂, hf₂⟩ := comp_almost_mul f₂ f₁
  exact ⟨_, by
    intro n
    rewrite [show (-f₁.comp f₂ + f₂.comp f₁) n = (-f₁.comp f₂ n + f₂.comp f₁ n) from rfl,
             ←Int.natAbs_neg,
             show -(-f₁.comp f₂ n + f₂.comp f₁ n) = f₁.comp f₂ n - f₂.comp f₁ n by
               rw [neg_add_rev, neg_neg, sub_eq_neg_add]]
    have triag := Int.natAbs_add_le (n * (f₁.comp f₂ n) - f₂ n * f₁ n) (f₂ n * f₁ n - n * (f₂.comp f₁ n))
    simp only [sub_add_sub_cancel, Int.diff_eq] at triag
    if c: n = 0
    then
      simp only [c, zero_mul, zero_sub, Int.natAbs_neg, ge_iff_le] at hf₁ hf₂ |-
      exact self_le_add_right |(f₁.comp f₂ - f₂.comp f₁) 0| (2*(k₁ + k₂))
    else
    have goal_mul_n :=
      calc |n| * |f₁.comp f₂ n - f₂.comp f₁ n|
        = |n*f₁.comp f₂ n - n*f₂.comp f₁ n| := by rw [←Int.natAbs_mul, mul_sub_left_distrib]
      _ ≤ |n*f₁.comp f₂ n - f₂ n * f₁ n| + |f₂ n * f₁ n - n*f₂.comp f₁ n| := triag
      _ ≤ |n*f₁.comp f₂ n - f₂ n * f₁ n| + (|n|+1)*k₂  :=
          by
            rw [mul_comm (f₂ n), ←Int.natAbs_neg (f₁ n * f₂ n - n * f₂.comp f₁ n)]
            apply Nat.add_le_add_left;
            simp only [neg_sub, Int.diff_eq]; exact hf₂ ..
      _ ≤ (|n|+1)*k₁ + (|n|+1)*k₂ := Nat.add_le_add_right (hf₁ ..) ..
      _ = (|n|+1)*(k₁ + k₂) := by ring
      _ ≤ |n| * (2*(k₁ + k₂)) :=
          by
            rw [←mul_assoc, mul_comm |n|]
            exact Nat.mul_le_mul_of_nonneg_right <|
                  succ_le_two_mul |n| <|
                  Int.natAbs_ne_zero.2 c
    calc |f₁.comp f₂ n - f₂.comp f₁ n|
      ≤ 2*(k₁ + k₂) := le_of_mul_le_mul_left goal_mul_n
        <| Or.resolve_left (Nat.eq_zero_or_pos ..) (Int.natAbs_ne_zero.2 c)
    _ ≤ _ := self_le_add_left  (2*(k₁ + k₂)) |(f₁.comp f₂ - f₂.comp f₁) 0|⟩

end AlmostHom

namespace EudoxusReal

/-- Multiplication of Eudoxus reals is commutative. -/
protected theorem mul_comm : ∀ (a b : EudoxusReal), smulHom a b = smulHom b a :=
  Quotient.ind₂ fun f₁ f₂ => Quotient.sound <| by
    show (QuotientAddGroup.leftRel ..).r ..
    rewrite [QuotientAddGroup.leftRel_apply]
    exact AlmostHom.comp_almost_comm f₁ f₂

instance : CommRing EudoxusReal where
  mul := smul
  left_distrib f := smulHom f |>.map_add
  right_distrib f₁ f₂ g :=
    congrArg (·.toFun g) <| (smulHom (G := ℤ)).map_add f₁ f₂
  mul_zero f := smulHom f |>.map_zero
  zero_mul f :=
    congrArg (·.toFun f) <| (smulHom (G := ℤ)).map_zero
  one_mul := Quotient.ind (congrArg (Quotient.mk _) <|
    AlmostHom.ext <| Function.left_id ·)
  mul_one := Quotient.ind (congrArg (Quotient.mk _) <|
    AlmostHom.ext <| Function.right_id ·)
  mul_assoc := (Quotient.inductionOn₃ · · · (congrArg (Quotient.mk _) <|
    AlmostHom.ext <| Function.comp.assoc · · ·))
  mul_comm := EudoxusReal.mul_comm

  sub_eq_add_neg := SubNegMonoid.sub_eq_add_neg
  add_left_neg := AddGroup.add_left_neg

end EudoxusReal
