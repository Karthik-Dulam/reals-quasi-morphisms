import Mathlib.GroupTheory.QuotientGroup

import Util.Arithmetic
import Util.FunctionBounds
import Util.Meta.Tactics

import Mathlib.Tactic.Linarith

/-! Defines quasi-morphisms from an abelian group to ℤ and algebraic operations on them.

Reference(s):
1. http://web.science.mq.edu.au/~street/EffR.pdf
-/

/- Use absolute value notation defined in `Util.Arithemtic`. -/
open scoped Int.natAbs

/-! # Definition of `AlmostAdditive` and `AlmostHom` -/
variable {G : Type _}

section TypeDef
variable [Add G]

/- Generalise this to functions from an Add to an NormedAdd?
Of course, a norm requires the reals, so perhaps a uniform space
structure on the codomain. -/
/-- A function from an AddCommGroup to ℤ is 'almost additive' if it
respects addition as a group homomorphism would within an error which
is bounded independently of the arguments. -/
def AlmostAdditive (f : G → ℤ) (bound : ℕ) :=
  ∀ g₁ g₂ : G, |f (g₁ + g₂) - f g₁ - f g₂| ≤ bound

/- Remark: we have used an `∃ ...` field rather than flattening out
with an additional `bound` field so that the same function with a
different bound is the same `AlmostHom`. This is necessary for
`AlmostHom` to be a lawful algebraic structure at all, since most of
the laws only hold for the functions, not for the bounds. -/
variable (G) in
/-- An `AlmostHom G` is a function from `G` to ℤ which is almost additive
(see `AlmostAdditive`). -/
structure AlmostHom where
  toFun : G → ℤ
  almostAdditive : ∃ bound : ℕ, AlmostAdditive toFun bound

instance : CoeFun (AlmostHom G) fun _ => G → ℤ where
  coe := AlmostHom.toFun

/-- An `AlmostHom` is determined by its underlying function. -/
@[ext]
theorem AlmostHom.ext
    : {f₁ f₂ : AlmostHom G} → f₁.toFun = f₂.toFun → f₁ = f₂
| ⟨_f, _⟩, ⟨.(_f), _⟩, rfl => rfl

end TypeDef


/-! # Properties and structure of `AlmostAdditive`/`AlmostHom` -/

variable [AddCommGroup G]

/- Because we can no longer directly access the bound associated with
a quasi-morphism, we first prove lemmas assuming an AlmostAdditive
hypothesis. Then we bundle them up into lemmas taking a AlmostHom and
showing existential statements. -/


/- Perhaps we should automate this more, similar to `to_additive`. -/

/-- This is equivalent to binding `⟨bound, h⟩` to `f.almostAdditive`,
then returning the bound specified with the `using` clause (inferred
as `_` if not specified) with the proof being the given field of `h`
applied to the specified number of arguments (or to `..` if not
specified). -/
local syntax (name := __localWrapper)
  "local_wrapper " ident (num)? (" using " term)? : term

macro_rules (kind := __localWrapper)
| `(local_wrapper $field:ident $[$args:num]? $[using $bound:term]?) => do
  let secondTerm : Lean.Syntax.Term ← match args with
  | some numArgs => `(h.$field $(.mkArray numArgs.getNat (←`(_)))*)
    /- If the number of args to apply the field of `h` to is not
    specified, use `..`. -/
  | none         => `(h.$field ..)
  /- Unhygienic visible `bound` (if bound argument is provided) and captured `f`. -/
  `(let ⟨$(if bound.isSome then
             -- set_option hygiene false in ←`(bound)
             Lean.mkIdent `bound
           else
             ←`(bound))         , h⟩ := $(Lean.mkIdent `f).almostAdditive
     /- `bound` is by default `_`, i.e., to be filled by unification. -/
    ⟨$(bound.getD <|← `(_)), $secondTerm⟩)

section AlmostProperties

namespace AlmostAdditive
variable ⦃f : G → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound)
variable (m n : ℤ) (g : G)

lemma almost_additive : ∀ g₁ g₂ : G, |f (g₁ + g₂) - f g₁ - f g₂| ≤ bound := h

/-- An almost additive function `f` maps 0 to 0, up to an error at most the bound. -/
lemma almost_zero : |f 0| ≤ bound := -- by simpa using h.almost_additive 0 0
  calc |f 0| = |f (0+0) - f 0 - f 0| := by rw [←Int.natAbs_neg, add_zero,
                                               sub_self, zero_sub]
         _ ≤ bound                 := h.almost_additive 0 0

/-- An almost additive function `f` respects negation, up to an error at most
twice the bound. -/
lemma almost_neg : |f (-g) - -f g| ≤ bound * 2 :=
  calc |f (-g) - (- (f g))|
    ≤ |f (-g) + f g - f 0| + |f 0|
        := by lax_exact Int.natAbs_add_le (f (-g) + f g - f 0) (f 0); linarith
  _ = |f (-g + g) - f (-g) - f g| + |f 0|
        := by congr 1; rewrite [←Int.natAbs_neg, ←add_left_neg g]
              congr; linarith
  _ ≤ bound * 2
        := by linarith [h.almost_additive (-g) g, h.almost_zero]

/- First inequality proven in reference 1. -/
/-- An almost additive function `f` respects scaling by ℤ, up to an error
proportional to the scaling factor. -/
lemma almost_smul : |f (m • g) - m * f g| ≤ bound * (|m| + 1) := by
  cases m <;> (rename_i m; induction m)
  case ofNat.zero => simp; exact h.almost_zero
  case ofNat.succ m hᵢ =>
    rewrite [Int.ofNat_eq_coe, ofNat_zsmul] at hᵢ ⊢
    /- Rewriting these somewhat deep subterms with 'calc' would
    involve verbosely repeating the surroundings. -/
    rewrite [show m.succ • g = g + m • g from AddMonoid.nsmul_succ ..,
             show ↑(m.succ) * f g = f g + m * f g
               by rewrite [Nat.succ_eq_add_one, Nat.cast_succ]; linarith]
    calc |f (g + m • g) - (f g + m * f g)|
        = |(f (g + m • g) - f g - f (m • g)) + (f (m • g) - m * f g)|
            := congrArg Int.natAbs <| by linarith
      _ ≤ |f (g + m • g) - f g - f (m • g)| + |f (m • g) - m * f g|
            := Int.natAbs_add_le ..
      _ ≤ bound + bound * (m + 1)
            := Nat.add_le_add (h.almost_additive ..) hᵢ
      _ = bound * (m.succ + 1)
            := by linarith
  case negSucc.zero =>
    rewrite [show Int.negSucc Nat.zero = -1 by rfl]; simpa using h.almost_neg g
  case negSucc.succ m hᵢ =>
    conv => lhs; rewrite [←Int.negSucc_sub_one]
    rewrite [sub_zsmul, one_zsmul, sub_mul, one_mul]
    calc |f (Int.negSucc m • g + -g) - (Int.negSucc m * f g - f g)|
        = |(-(f (Int.negSucc m • g) - f (Int.negSucc m • g + -g) - f g))
           + (f (Int.negSucc m • g) - Int.negSucc m * f g)|
            := congrArg Int.natAbs <| by linarith
      _ ≤ |f (Int.negSucc m • g) - f (Int.negSucc m • g + -g) - f g|
          + |f (Int.negSucc m • g) - Int.negSucc m * f g|
            := by conv => rhs; arg 1; rewrite [←Int.natAbs_neg]
                  apply Int.natAbs_add_le
      _ ≤ bound + bound * (|Int.negSucc m| + 1)
            := Nat.add_le_add (by -- change `f (-[m+1])` to `f (-[m+1] + -g + g)`
                                  rewrite [←congrArg f <| neg_add_cancel_right ..]
                                  apply h.almost_additive _ g)
                              hᵢ
      _ = bound * (|Int.negSucc m.succ| + 1)
            := by simp only [Int.natAbs_negSucc]; linarith

/- Second inequality proven in reference 1, generalised to arbitrary abelian groups. -/
/-- A kind of commutativity of scaling by ℤ for almost additive functions, with
one scale factor before and another after applying the function. -/
lemma almost_smul_interchange
    : |n * f (m • g) - m * f (n • g)| ≤ bound * (|m| + |n| + 2) :=
  calc |n * f (m • g) - m * f (n • g)|
    ≤ |f ((m * n) • g) - n * f (m • g)| + |f ((m * n) • g) - m * f (n • g)|
        := Int.triangle_ineq' ..
  _ = |f (n • m • g) - n * f (m • g)| + |f (m • n • g) - m * f (n • g)|
              /- TODO find a better syntax for this - same-line ·'s -/
        := by congr 3; (· rw [mul_zsmul']); (· rw [mul_zsmul])
  _ ≤ bound * (|n| + 1) + bound * (|m| + 1)
           /- In this case, writing `Nat.add_le_add` is easier than
           specifying the almost_smul arguments for `linarith`. -/
        := by apply Nat.add_le_add <;> apply h.almost_smul
  _ = bound * (|m| + |n| + 2) := by linarith

/-- `almost_smul_interchange` specialised to almost additive functions on ℤ applied to 1.

This is equation (1) in the first reference. -/
lemma almost_smul_interchange_int
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound) (m n : ℤ)
    : |n * f m - m * f n| ≤ bound * (|m| + |n| + 2) := by
  lax_exact h.almost_smul_interchange m n 1 <;> rw [zsmul_int_one]

/- The following lemmas are useful in bounding compositions of quasi-morphisms. -/

/-- An almost additive function grows at most linearly (as a function of a scale
factor applied to its argument). -/
lemma linear_growth_upper_bound
    : |f (n • g)| ≤ (bound + |f g|) * |n| + bound :=
  calc |f (n • g)|
    ≤ |f (n • g) - n * f g| + |n * f g|
        := by lax_exact Int.natAbs_add_le (f (n • g) - n * f g) (n * f g); linarith
  _ ≤ (bound + |f g|) * |n| + bound
        := by linarith [h.almost_smul n g, Int.natAbs_mul n (f g)]

/-- Lemma `linear_growth_upper_bound` specialised to functions on ℤ applied to 1. -/
lemma linear_growth_upper_bound_int
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound) (n : ℤ)
    : |f n| ≤ (bound + |f 1|) * |n| + bound := by
  lax_exact h.linear_growth_upper_bound n 1; rw [zsmul_int_one]

/-- An almost additive function grows at least linearly (as a function of a scale
factor applied to its argument). -/
lemma linear_growth_lower_bound
    : (|f g| - bound) * |n| - bound ≤ |f (n • g)| := by
  rewrite [tsub_mul, Nat.sub_sub, ←Nat.mul_succ]
  apply Nat.sub_le_of_le_add; rewrite [Nat.add_comm]
  calc |f g| * |n|
    = |n * f g|                       := by rw [Nat.mul_comm, Int.natAbs_mul]
  _ ≤ |n * f g - f (n • g)| + |f (n • g)|
        := by lax_exact Int.natAbs_add_le (n * f g - f (n • g)) (f (n • g)); linarith
  _ = |f (n • g) - n * f g| + |f (n • g)|
        := by congr 1; rewrite [←Int.natAbs_neg]
              congr 1; linarith
  _ ≤ bound * (|n| + 1) + |f (n • g)| := by linarith [h.almost_smul n g]

/-- Lemma `linear_growth_lower_bound` specialised to functions on ℤ applied to 1. -/
lemma linear_growth_lower_bound_int
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound) (n : ℤ)
    : (|f 1| - bound) * |n| - bound ≤ |f n| := by
  lax_exact h.linear_growth_lower_bound n 1; rw [zsmul_int_one]

end AlmostAdditive

namespace AlmostHom
variable (f : AlmostHom G) (g : G) (m n : ℤ)

/- `bdd <expr>` says there is some `bound : ℕ` which |<expr>| is bounded by.
(Admittedly, this is tautological.)
`bdd <expr> for all (<bindings>)` expresses a uniform bound. -/
-- Why is there no way to say "exactly what ∀ accepts"?
local syntax (name := __existsBound) "bdd " term ("for all " bracketedBinder)? : term
macro_rules (kind := __existsBound)
| `(bdd $expr:term for all $binders:bracketedBinder) =>
  `(∃ bound : ℕ, ∀ $binders, |$expr| ≤ bound)
| `(bdd $expr:term) => `(∃ bound : ℕ, |$expr| ≤ bound)

/-- An almost-homomorphism respects addition up to an error with a uniform bound. -/
lemma almost_additive : bdd f (g₁ + g₂) - f g₁ - f g₂ for all (g₁ g₂ : G) :=
  local_wrapper almost_additive 0

/- Not useful, since we can't say anything useful about what the bound is.
lemma almost_zero : bdd f 0 :=
  local_wrapper almost_zero 0
-/

/-- An almost-homomorphism respects negation up to an error with a uniform bound. -/
lemma almost_neg : bdd f (-g) - -f g for all (g : G) :=
  local_wrapper almost_neg 0

/-- An almost-homomorphism respects scaling by ℤ up to an error with a bound
uniform with respect to the `G` argument. -/
lemma almost_smul : bdd f (m • g) - m * f g for all (g : G) :=
  local_wrapper almost_smul 1

/-- A kind of commutativity of scaling by ℤ for almost-homomorphisms, with one
scale factor before and another after applying the function. -/
lemma almost_smul_interchange
    : bdd n * f (m • g) - m * f (n • g) for all (g : G) :=
  local_wrapper almost_smul_interchange 2

/- Not useful, since we end up not saying anything useful about what the bound is.
lemma almost_smul_interchange_int (f : AlmostHom ℤ) (m n : ℤ)
    : bdd n * f m - m * f n :=
  local_wrapper almost_smul_interchange_int
-/

/-- An almost-homomorphism grows at most linearly (as a function of a scale factor
applied to its argument). -/
lemma linear_growth_upper_bound
    : ∃ a b : ℕ, ∀ n : ℤ, |f (n • g)| ≤ a * |n| + b :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, _, h.linear_growth_upper_bound (g := g)⟩

/-- Lemma `linear_growth_upper_bound` specialised to domain ℤ applied to 1. -/
lemma linear_growth_upper_bound_int (f : AlmostHom ℤ)
    : ∃ a b : ℕ, ∀ n : ℤ, |f n| ≤ a * |n| + b :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, _, h.linear_growth_upper_bound_int⟩

/- Not useful, since we end up not saying anything useful about what the bound is.

/-- An almost-homomorphism grows at least linearly (as a function of a scale factor
applied to its argument). -/
lemma linear_growth_lower_bound
    : ∃ a b : ℕ, ∀ n : ℤ, a * |n| - b ≤ |f (n • g)| :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, _, h.linear_growth_lower_bound (g := g)⟩

/-- Lemma `linear_growth_lower_bound` specialised to domain ℤ applied to 1. -/
lemma linear_growth_lower_bound_int (f : AlmostHom ℤ)
    : ∃ a b : ℕ, ∀ n : ℤ, a * |n| - b ≤ |f n| :=
  let ⟨_, h⟩ := f.almostAdditive
  ⟨_, _, h.linear_growth_lower_bound_int⟩

-/

end AlmostHom

end AlmostProperties

section AlgebraicStructure

namespace AlmostAdditive
variable ⦃f : G → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound)
         ⦃f₁ : G → ℤ⦄ ⦃bound₁ : ℕ⦄ (h₁ : AlmostAdditive f₁ bound₁)
         ⦃f₂ : G → ℤ⦄ ⦃bound₂ : ℕ⦄ (h₂ : AlmostAdditive f₂ bound₂)

/-- The (pointwise) sum of almost additive functions is almost additive, with
bound the sum of their bounds. -/
protected theorem add : AlmostAdditive (f₁ + f₂) (bound₁ + bound₂) := fun x y =>
  calc |f₁ (x + y) + f₂ (x + y) - (f₁ x + f₂ x) - (f₁ y + f₂ y)|
    = |(f₁ (x + y) - f₁ x - f₁ y) + (f₂ (x + y) - f₂ x - f₂ y)|
        := congrArg Int.natAbs (by linarith)
  _ ≤ bound₁ + bound₂ := by transitivity
                            · apply Int.natAbs_add_le
                            · linarith [h₁ x y, h₂ x y]

/-- The (pointwise) negation of an almost additive function is almost additive
with the same bound. -/
protected theorem neg : AlmostAdditive (-f) bound := fun x y =>
  calc |(-f (x + y)) - (-f x) - (-f y)|
    = |(-(-f (x + y) - (-f x) - (-f y)))| := by rw [Int.natAbs_neg]
  _ = |f (x + y) - f x - f y|             := congrArg Int.natAbs (by linarith)
  _ ≤ bound                               := h ..

end AlmostAdditive

namespace AlmostHom
variable (f f₁ f₂ : AlmostHom G)

/- Haven't written local_wrapper to be able to destructure multiple
`AlmostAdditive` hypotheses yet. -/
/-- The sum of two almost-homomorphisms. It is simply the pointwise sum. -/
protected def add : AlmostHom G where
  toFun := f₁ + f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    ⟨_, AlmostAdditive.add h₁ h₂⟩

/-- Negation  of an almost-homomorphism. It is simply the pointwise negation. -/
protected def neg : AlmostHom G where
  toFun := -f
  almostAdditive := local_wrapper neg 0

/-- Additive abelian group structure on `AlmostHom G` using pointwise operations. -/
instance : AddCommGroup (AlmostHom G) where
  add := AlmostHom.add
  add_comm := by intros; ext; apply Int.add_comm
  add_assoc := by intros; ext; apply Int.add_assoc
  zero := ⟨0, 0, fun _ _ => Nat.le_refl ..⟩
  zero_add := by intros; ext; apply Int.zero_add
  add_zero f := by intros; ext; apply Int.add_zero
  neg := AlmostHom.neg
  add_left_neg := by intros; ext; apply Int.add_left_neg

end AlmostHom

end AlgebraicStructure

section Quotient

/-- `Bounded f` states that `f` is bounded over all arguments. -/
def Bounded (f : G → ℤ) (bound : ℕ) := ∀ g : G, |f g| ≤ bound

namespace Bounded

lemma of_bddAbove_of_bddBelow {f : G → ℤ}
        {boundᵤ : ℤ} (hᵤ : f.BddAboveBy boundᵤ)
        {boundₗ : ℤ} (hₗ : f.BddBelowBy boundₗ)
    : Bounded f (max |boundᵤ| |boundₗ|) := by
  intro g
  apply Int.natAbs_le <;> custom_zify
  · calc f g ≤ boundᵤ           := hᵤ g
           _ ≤ |boundᵤ|         := Int.le_natAbs
           _ ≤ /- inferred -/ _ := le_max_left ..
  · calc -f g ≤ -boundₗ          := Int.neg_le_neg <| hₗ g
            _ ≤ |boundₗ|         := Int.neg_le_natAbs ..
            _ ≤ /- inferred -/ _ := le_max_right ..

lemma bddAbove {f : G → ℤ} {bound : ℕ} (h : Bounded f bound)
    : f.BddAboveBy bound :=
  fun g => Int.le_trans (f g).le_natAbs (by exact_mod_cast h g)

lemma bddBelow {f : G → ℤ} {bound : ℕ} (h : Bounded f bound)
    : f.BddBelowBy (-bound) :=
  fun g => Int.neg_le_of_neg_le <|
    Int.le_trans (f g).neg_le_natAbs (by exact_mod_cast h g)

/- We don't really need this, but we might as well prove it. -/
variable {f : G → ℤ} {bound : ℕ} in
/-- A bounded function G → ℤ is almost additive. -/
lemma Bounded.almost_additive (h : Bounded f bound)
    : AlmostAdditive f (bound * 3) := fun g₁ g₂ =>
  calc |f (g₁ + g₂) - f g₁ - f g₂|
      ≤ |f (g₁ + g₂)| + |(-f g₁)| + |(-f g₂)| := Int.natAbs_add_le₃ ..
    _ ≤ bound * 3 := by linarith [(f g₁).natAbs_neg, (f g₂).natAbs_neg,
                                  h (g₁ + g₂), h g₁, h g₂]

end Bounded

def AlmostHom.Bounded (f : AlmostHom G) := Exists (_root_.Bounded f)

namespace AlmostHom.Bounded

lemma of_bddAbove_of_bddBelow (f : AlmostHom G)
    : (⇑f).BddAbove → (⇑f).BddBelow → f.Bounded :=
  fun ⟨_, hᵤ⟩ ⟨_, hₗ⟩ =>
    ⟨_, _root_.Bounded.of_bddAbove_of_bddBelow hᵤ hₗ⟩

lemma bddAbove {f : AlmostHom G} : f.Bounded → (⇑f).BddAbove :=
  fun ⟨_bound, h⟩ => ⟨_, _root_.Bounded.bddAbove h⟩

lemma bddBelow {f : AlmostHom G} : f.Bounded → (⇑f).BddBelow :=
  fun ⟨_bound, h⟩ => ⟨_, _root_.Bounded.bddBelow h⟩

end AlmostHom.Bounded

variable (G) in
/-- The subgroup of `AlmostHom G` consisting of bounded quasi-morphisms. -/
def boundedAlmostHoms : AddSubgroup (AlmostHom G) where
  carrier := setOf AlmostHom.Bounded
  add_mem' {f₁ f₂} := fun ⟨bound₁, h₁⟩ ⟨bound₂, h₂⟩ => .intro _ fun g =>
    calc |f₁ g + f₂ g| ≤ |f₁ g| + |f₂ g| := Int.natAbs_add_le ..
                     _ ≤ bound₁ + bound₂ := Nat.add_le_add (h₁ g) (h₂ g)
  zero_mem' := ⟨0, fun _ => show |(0:ℤ)| ≤ 0 from Nat.le_refl 0⟩
  neg_mem' {f} := fun ⟨bound, h⟩ => .intro _ fun g =>
    calc |(-f g)| = |f g| := Int.natAbs_neg ..
                _ ≤ bound := h g

variable (G) in
/-- Quasi-homomorphisms from an `AddCommGroup` `G` to ℤ.

This is the quotient of the `AlmostHom`s by the additive subgroup of bounded
functions. -/
abbrev QuasiHom := AlmostHom G ⧸ boundedAlmostHoms G

/-- The Eudoxus construction of the real numbers as quasi-homomorphisms from ℤ to ℤ. -/
abbrev EudoxusReal := QuasiHom ℤ

end Quotient
