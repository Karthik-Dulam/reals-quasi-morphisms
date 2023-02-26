import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup

import Util.Arithmetic
import Util.Tactics

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

def AlmostAdditive (f : G → ℤ) (bound : ℕ) :=
∀ g₁ g₂ : G, |f (g₁ + g₂) - f g₁ - f g₂| ≤ bound

/- Remark: we have used an `∃ ...` field rather than flattening out
with an additional `bound` field so that the same function with a
different bound is the same `AlmostHom`. This is necessary for
`AlmostHom` to be a lawful algebraic structure at all, since most of
the laws only hold for the functions, not for the bounds. -/
variable (G) in structure AlmostHom where
  toFun : G → ℤ
  almostAdditive : ∃ bound : ℕ, AlmostAdditive toFun bound

instance : CoeFun (AlmostHom G) fun _ => G → ℤ where
  coe := AlmostHom.toFun

@[ext]
theorem AlmostHom.ext
  : {f₁ f₂ : AlmostHom G} → f₁.toFun = f₂.toFun → f₁ = f₂
| ⟨_f, _⟩, ⟨.(_f), _⟩, rfl => rfl

end TypeDef


/-! # Properties and structure of `AlmostAdditive`/`AlmostHom` -/
variable [AddCommGroup G]

/-! Because we can no longer directly access the bound associated with
a quasi-morphism, we first prove lemmas assuming an AlmostAdditive
hypothesis. Then we bundle them up into lemmas taking a AlmostHom and
showing existential statements. -/


/- Perhaps we should automate this more, similar to `to_additive`. -/

/- This is equivalent to binding `⟨bound, h⟩` to `f.almostAdditive`,
then returning the bound specified with the `using` clause (or just
`bound` if not specified) with the proof being the given field of `h`
applied to the specified number of arguments (or to `..` if not
specified). -/
local syntax (name := __localWrapper) "local_wrapper " ident (num)? (" using " term)? : term

set_option hygiene false in
open Lean (TSyntax) in open Lean.Syntax in
macro_rules (kind := __localWrapper)
  /- `bound` is by default `_`, i.e., to be filled by unification. -/
| `(local_wrapper $field:ident $[$args:num]?) =>
  `(local_wrapper $field $[$args]? using _)
| `(local_wrapper $field:ident $[$args:num]? using $bound:term) => do
  let hField : TSyntax `term ← `(h.$field:ident)
  let secondTerm : TSyntax `term ← match args with
  | some numArgs => pure<| .mkArray numArgs.getNat (←`(_)) |> mkApp hField
    /- If the number of args to apply the field of `h` to is not
    specified, use `..`. -/
  | none         => `($hField ..)
  `(let ⟨bound, h⟩ := f.almostAdditive
    ⟨$bound, $secondTerm⟩)

section AlmostProperties

namespace AlmostAdditive
variable ⦃f : G → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound)
variable (m n : ℤ) (g : G)

lemma almost_additive : ∀ g₁ g₂ : G, |f (g₁ + g₂) - f g₁ - f g₂| ≤ bound := h

/-- A quasi-morphism `f` maps 0 to 0, within an error of up to `f.bound`. -/
lemma almost_zero : |f 0| ≤ bound := -- by simpa using h.almost_additive 0 0
  calc |f 0| = |f (0+0) - f 0 - f 0| := by rewrite [←Int.natAbs_neg]; congr 1
                                           rewrite [add_zero]; linarith
         _ ≤ bound                 := h.almost_additive 0 0

/-- A quasi-morphism `f` respects negation, within an error of up to `f.bound * 2`. -/
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
/-- A quasi-morphism `f` respects scaling by ℤ, within an error proportional to the scaling factor. -/
lemma almost_smul : |f (m • g) - m * f g| ≤ bound * (|m| + 1) := by
  cases m <;> (rename_i m; induction m)
  case ofNat.zero => simp; exact h.almost_zero
  case ofNat.succ m hᵢ =>
    rewrite [Int.ofNat_eq_coe, ofNat_zsmul] at hᵢ ⊢
    -- Rewriting these somewhat deep subterms with 'calc' would
    -- involve verbosely repeating the surroundings.
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
/-- A kind of commutativity of scaling by ℤ, with
one scale factor before and another after applying a quasi-morphism. -/
private lemma almost_smul_comm
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

/- `almost_smul_comm'` specialised to quasi-morphisms on integers and applied to 1.
Eq (1) of reference 1. -/
private lemma almost_smul_comm_int
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound) (m n : ℤ)
    : |n * f m - m * f n| ≤ bound * (|m| + |n| + 2) := by
  lax_exact h.almost_smul_comm m n 1 <;> rw [zsmul_int_one]

lemma linear_growth_upper_bound
  : |f (n • g)| ≤ (bound + |f g|) * |n| + bound :=
  calc |f (n • g)|
    ≤ |f (n • g) - n * f g| + |n * f g|
        := by lax_exact Int.natAbs_add_le (f (n • g) - n * f g) (n * f g); linarith
  _ ≤ (bound + |f g|) * |n| + bound
        := by linarith [h.almost_smul n g, Int.natAbs_mul n (f g)]

lemma linear_growth_upper_bound_int
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound) (n : ℤ)
    : |f n| ≤ (bound + |f 1|) * |n| + bound := by
  lax_exact h.linear_growth_upper_bound n 1; rw [zsmul_int_one]

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
set_option hygiene false in
macro_rules (kind := __existsBound)
| `(bdd $expr:term for all $binders:bracketedBinder) =>
  `(∃ bound : ℕ, ∀ $binders, |$expr| ≤ bound)
| `(bdd $expr:term) => `(∃ bound : ℕ, |$expr| ≤ bound)

lemma almost_additive : bdd f (g₁ + g₂) - f g₁ - f g₂ for all (g₁ g₂ : G) :=
local_wrapper almost_additive 0

/- Not useful, since we don't say anything about what the bound is.
lemma almost_zero : bdd f 0 :=
local_wrapper almost_zero 0
-/

lemma almost_neg : bdd f (-g) - -f g for all (g : G) :=
local_wrapper almost_neg 0

lemma almost_smul : bdd f (m • g) - m * f g for all (g : G) :=
local_wrapper almost_smul 1

private lemma almost_smul_comm
  : bdd n * f (m • g) - m * f (n • g) for all (g : G) :=
local_wrapper almost_smul_comm 2

/- Not useful, since we don't say anything about what the bound is.
private lemma almost_smul_comm_int (f : AlmostHom ℤ) (m n : ℤ)
    : bdd n * f m - m * f n :=
  local_wrapper almost_smul_comm_int
-/

lemma linear_growth_upper_bound
  : ∃ a b : ℕ, ∀ n : ℤ, |f (n • g)| ≤ a * |n| + b :=
let ⟨_, h⟩ := f.almostAdditive
⟨_, _, h.linear_growth_upper_bound (g := g)⟩

lemma linear_growth_upper_bound_int (f : AlmostHom ℤ)
  : ∃ a b : ℕ, ∀ n : ℤ, |f n| ≤ a * |n| + b :=
let ⟨_, h⟩ := f.almostAdditive
⟨_, _, h.linear_growth_upper_bound_int⟩

lemma linear_growth_lower_bound
  : ∃ a b : ℕ, ∀ n : ℤ, a * |n| - b ≤ |f (n • g)| :=
let ⟨_, h⟩ := f.almostAdditive
⟨_, _, h.linear_growth_lower_bound (g := g)⟩

lemma linear_growth_lower_bound_int (f : AlmostHom ℤ)
  : ∃ a b : ℕ, ∀ n : ℤ, a * |n| - b ≤ |f n| :=
let ⟨_, h⟩ := f.almostAdditive
⟨_, _, h.linear_growth_lower_bound_int⟩

end AlmostHom

end AlmostProperties

section AlgebraicStructure

namespace AlmostAdditive
variable ⦃f : G → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound)
         ⦃f₁ : G → ℤ⦄ ⦃bound₁ : ℕ⦄ (h₁ : AlmostAdditive f₁ bound₁)
         ⦃f₂ : G → ℤ⦄ ⦃bound₂ : ℕ⦄ (h₂ : AlmostAdditive f₂ bound₂)

protected theorem add : AlmostAdditive (f₁ + f₂) (bound₁ + bound₂) := fun x y =>
  calc |f₁ (x + y) + f₂ (x + y) - (f₁ x + f₂ x) - (f₁ y + f₂ y)|
    = |(f₁ (x + y) - f₁ x - f₁ y) + (f₂ (x + y) - f₂ x - f₂ y)|
        := congrArg Int.natAbs (by linarith)
  _ ≤ bound₁ + bound₂ := by transitivity
                            · apply Int.natAbs_add_le
                            · linarith [h₁ x y, h₂ x y]

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
protected def add : AlmostHom G where
  toFun := f₁ + f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    -- bound is filled in based on the proof :)
    ⟨_, AlmostAdditive.add h₁ h₂⟩

protected def neg : AlmostHom G where
  toFun := -f
  almostAdditive := local_wrapper neg 0

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

def Bounded (f : G → ℤ) (bound : ℕ) := ∀ g : G, |f g| ≤ bound

/- We don't really need this, but we might as well prove it. -/
variable {f : G → ℤ} {bound : ℕ} in
lemma Bounded.almost_additive (h : Bounded f bound)
    : AlmostAdditive f (bound * 3) := fun g₁ g₂ =>
  calc |f (g₁ + g₂) - f g₁ - f g₂|
      ≤ |f (g₁ + g₂)| + |(-f g₁)| + |(-f g₂)| := Int.natAbs_add_le₃ ..
    _ ≤ bound * 3 := by linarith [(f g₁).natAbs_neg, (f g₂).natAbs_neg,
                                  h (g₁ + g₂), h g₁, h g₂]

variable (G) in
/-- The subgroup of `AlmostHom G` consisting of bounded quasi-morphisms. -/
def boundedAlmostHoms : AddSubgroup (AlmostHom G) where
  carrier := {f | ∃ bound : ℕ, Bounded f bound}
  add_mem' {f₁ f₂} := fun ⟨bound₁, h₁⟩ ⟨bound₂, h₂⟩ => .intro _ fun g =>
    calc |f₁ g + f₂ g| ≤ |f₁ g| + |f₂ g| := Int.natAbs_add_le ..
                     _ ≤ bound₁ + bound₂ := Nat.add_le_add (h₁ g) (h₂ g)
  zero_mem' := ⟨0, fun _ => show |(0:ℤ)| ≤ 0 from Nat.le_refl 0⟩
  neg_mem' {f} := fun ⟨bound, h⟩ => .intro _ fun g =>
    calc |(-f g)| = |f g| := Int.natAbs_neg ..
                _ ≤ bound := h g

variable (G) in
def QuasiHom := AlmostHom G ⧸ boundedAlmostHoms G

instance : HasEquiv (AlmostHom G) where
  Equiv f g := f - g ∈ boundedAlmostHoms G

abbrev EudoxusReal := QuasiHom ℤ

/- Typeclass inference won't unfold the definition of `QuasiHom`
automatically, so the instance must be defined manually. -/
instance : AddCommGroup (QuasiHom G) := by unfold QuasiHom; infer_instance

end Quotient
