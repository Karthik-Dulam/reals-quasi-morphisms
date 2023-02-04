import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup

/-! Defines quasi-morphisms from an abelian group to ℤ and algebraic operations on them.

Reference(s):
1. http://web.science.mq.edu.au/~street/EffR.pdf
-/

-- Note: we can avoid the AbsoluteValue import by using simp? to get
-- exact `simp only`s for every use. However, this results in huge lists
-- of lemmas sometimes, so this hasn't been done for now.

/-! # Absolute value notation for convenience
We can think about scoping this with sections later. -/

/- This conflicts with match-case notation. -/
-- 	local notation (priority := high) "|" x "|" => Int.natAbs x
/- This is copied with modifications from Mathlib.Algebra.Abs. -/
/- Splitting into `syntax` and `macro_rules` seems to be necessary to use `local`. -/
local syntax (name := __natAbs) atomic("|" noWs) term noWs "|" : term
macro_rules (kind := __natAbs) | `(|$x:term|) => `(Int.natAbs $x)
/- This is supposedly automatically local and prevents an instance for
`Abs ℤ` which would conflict with the above notation. -/
attribute [-instance] Neg.toHasAbs
/- This should make the pretty printer use this notation.
Copied with modifications from https://github.com/leanprover/lean4/issues/2045#issuecomment-1396168913. -/
@[local app_unexpander Int.natAbs]
private def __natAbs_unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $n:term) => `(|$n|)
| _ => throw ()

/-! # Definition of `AlmostAdditive` and `QuasiMorphism` -/
variable {G : Type _}

section TypeDef
variable [Add G]

def AlmostAdditive (f : G → ℤ) (bound : ℕ) :=
∀ g₁ g₂ : G, |f (g₁ + g₂) - f g₁ - f g₂| ≤ bound

/- Remark: we have used an `∃ ...` field rather than flattening out
with an additional `bound` field so that the same function with a
different bound is the same `QuasiMorphism`. This is necessary for
`QuasiMorphism` to be a lawful algebraic structure at all, since most
of the laws only hold for the functions, not for the bounds. -/
variable (G) in structure QuasiMorphism where
  toFun : G → ℤ
  almostAdditive : ∃ bound : ℕ, AlmostAdditive toFun bound

instance : CoeFun (QuasiMorphism G) fun _ => G → ℤ where
  coe := QuasiMorphism.toFun

@[ext]
theorem QuasiMorphism.ext
  : {f₁ f₂ : QuasiMorphism G} → f₁.toFun = f₂.toFun → f₁ = f₂
| ⟨_f, _⟩, ⟨.(_f), _⟩, rfl => rfl

end TypeDef


/-! # Properties and structure of `AlmostAdditive`/`QuasiMorphism` -/
variable [AddCommGroup G]

/-! Because we can no longer directly access the bound associated with
a quasi-morphism, we first prove lemmas assuming an AlmostAdditive
hypothesis. Then we bundle them up into lemmas taking a QuasiMorphism
and showing existential statements. -/


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
| `(local_wrapper $field:ident $[$args:num]?) =>
  `(local_wrapper $field $[$args]? using _)
| `(local_wrapper $field:ident $[$args:num]? using $bound:term) => do
  let hField : TSyntax `term ← `(h.$field:ident)
  let secondTerm : TSyntax `term ← match args with
  | some numArgs => pure<| .mkArray numArgs.getNat (←`(_)) |> mkApp hField
  | none         => `($hField ..)
  `(let ⟨bound, h⟩ := f.almostAdditive
    ⟨$bound, $secondTerm⟩)

section AlmostProperties

namespace AlmostAdditive
variable ⦃f : G → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound)
variable (m n : ℤ) (g : G)

lemma almost_additive : ∀ g₁ g₂ : G, |f (g₁ + g₂) - f g₁ - f g₂| ≤ bound := h

/-- A quasi-morphism `f` maps 0 to 0, within an error of up to `f.bound`. -/
lemma almost_zero : |f 0| ≤ bound := by simpa using h.almost_additive 0 0
/-
calc |f 0| = |(-f 0)|              := by rw [Int.natAbs_neg]
         _ = |f (0+0) - f 0 - f 0| := congrArg Int.natAbs <|
                                        by rewrite [add_zero]; linarith
         _ ≤ bound                 := h.almost_additive 0 0
-/

/-- A quasi-morphism `f` respects negation, within an error of up to `f.bound * 2`. -/
lemma almost_neg : |f (-g) - -f g| ≤ bound * 2 :=
calc |f (-g) - (- (f g))| = |(f (-g) + f g - f 0) + f 0|
                              := congrArg Int.natAbs <| by linarith
                        _ ≤ |f (-g) + f g - f 0| + |f 0| := Int.natAbs_add_le ..
                        _ = |f (-g + g) - f (-g) - f g| + |f 0|
                              := by apply congrArg (· + |f 0|)
                                    rewrite [←Int.natAbs_neg, ←add_left_neg g]
                                    apply congrArg Int.natAbs; linarith
                        _ ≤ bound * 2
                              := Nat.mul_two .. ▸
                                   Nat.add_le_add (h.almost_additive (-g) g)
                                                  h.almost_zero

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
    = |(n * f (m • g) - f ((m * n) • g)) + (f ((m * n) • g) - m * f (n • g))|
        := congrArg Int.natAbs <| by linarith
  _ ≤ |n * f (m • g) - f ((m * n) • g)| + |f ((m * n) • g) - m * f (n • g)|
        := Int.natAbs_add_le ..
  _ = |f (n • m • g) - n * f (m • g)| + |f (m • n • g) - m * f (n • g)|
        := by conv => lhs; arg 1; rewrite [←Int.natAbs_neg, mul_zsmul']
              conv => lhs; arg 2; rewrite [mul_zsmul]
              congr; linarith
  _ ≤ bound * (|n| + 1) + bound * (|m| + 1)
        := Nat.add_le_add (h.almost_smul ..) (h.almost_smul ..)
  _ = bound * (|m| + |n| + 2) := by linarith

/- `almost_smul_comm'` specialised to quasi-morphisms on integers and applied to 1.
Eq (1) of reference 1. -/
private lemma almost_smul_comm'
        ⦃f : ℤ → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound) (m n : ℤ)
    : |n * f m - m * f n| ≤ bound * (|m| + |n| + 2) := by
  conv => lhs; rewrite [←congrArg f (zsmul_int_one m), ←congrArg f (zsmul_int_one n)]
  exact h.almost_smul_comm m n 1

private lemma linear_growth_upper_bound
  : |f (n • g)| ≤ (bound + |f g|) * |n| + bound :=
calc |f (n • g)| = |f (n • g) - n * f g + n * f g| := by rw [Int.sub_add_cancel]
               _ ≤ |f (n • g) - n * f g| + |n * f g| := Int.natAbs_add_le ..
               _ ≤ bound * (|n| + 1) + |n| * |f g|
                     := Int.natAbs_mul .. ▸
                          Nat.add_le_add_right (h.almost_smul ..) _
               _ ≤ (bound + |f g|) * |n| + bound := by linarith

private lemma linear_growth_lower_bound
  : (|f g| - bound) * |n| - bound ≤ |f (n • g)| := by
  rewrite [tsub_mul, Nat.sub_sub, ←Nat.mul_succ]
  apply Nat.sub_le_of_le_add; rewrite [Nat.add_comm]
  calc |f g| * |n| = |n * f g| := by rw [Nat.mul_comm, ←Int.natAbs_mul]
    _ = |n * f g - f (n • g) + f (n • g)| := by congr; linarith
    _ ≤ |n * f g - f (n • g)| + |f (n • g)| := Int.natAbs_add_le ..
    _ = |f (n • g) - n * f g| + |f (n • g)|
          := congrArg (· + _) <| by rewrite [←Int.natAbs_neg]; congr; linarith
    _ ≤ bound * (|n| + 1) + |f (n • g)| := Nat.add_le_add_right (h.almost_smul ..) _

end AlmostAdditive

namespace QuasiMorphism
variable (f : QuasiMorphism G) (g : G) (m n : ℤ)

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
private lemma almost_smul_comm' (f : QuasiMorphism ℤ) (m n : ℤ)
  : bdd n * f m - m * f n :=
local_wrapper almost_smul_comm'
-/

private lemma linear_growth_upper_bound
  : ∃ a b : ℕ, ∀ n : ℤ, |f (n • g)| ≤ a * |n| + b :=
let ⟨_, h⟩ := f.almostAdditive
⟨_, _, h.linear_growth_upper_bound (g := g)⟩

private lemma linear_growth_lower_bound
  : ∃ a b : ℕ, ∀ n : ℤ, a * |n| - b ≤ |f (n • g)| :=
let ⟨_, h⟩ := f.almostAdditive
⟨_, _, h.linear_growth_lower_bound (g := g)⟩

end QuasiMorphism

end AlmostProperties

section AlgebraicStructure

namespace AlmostAdditive
variable ⦃f : G → ℤ⦄ ⦃bound : ℕ⦄ (h : AlmostAdditive f bound)
         ⦃f₁ : G → ℤ⦄ ⦃bound₁ : ℕ⦄ (h₁ : AlmostAdditive f₁ bound₁)
         ⦃f₂ : G → ℤ⦄ ⦃bound₂ : ℕ⦄ (h₂ : AlmostAdditive f₂ bound₂)

protected theorem add : AlmostAdditive (f₁ + f₂) (bound₁ + bound₂) := fun x y =>
calc |f₁ (x + y) + f₂ (x + y) - (f₁ x + f₂ x) - (f₁ y + f₂ y)|
    = |(f₁ (x + y) - f₁ x - f₁ y) + (f₂ (x + y) - f₂ x - f₂ y)|
        := congrArg Int.natAbs <| by linarith
  _ ≤ |f₁ (x + y) - f₁ x - f₁ y| + |f₂ (x + y) - f₂ x - f₂ y|
        := Int.natAbs_add_le ..
  _ ≤ bound₁ + bound₂
        := Nat.add_le_add (h₁ ..) (h₂ ..)

protected theorem neg : AlmostAdditive (-f) bound := fun x y =>
calc |(-f (x + y)) - (-f x) - (-f y)|
    = |(-(-f (x + y) - (-f x) - (-f y)))| := by rw [Int.natAbs_neg]
  _ = |f (x + y) - f x - f y|             := congrArg Int.natAbs <| by linarith
  _ ≤ bound                               := h ..

protected theorem comp
    ⦃f₁ : ℤ → ℤ⦄ ⦃bound₁ : ℕ⦄ (h₁ : AlmostAdditive f₁ bound₁)
    ⦃f₂ : G → ℤ⦄ ⦃bound₂ : ℕ⦄ (h₂ : AlmostAdditive f₂ bound₂)
  : AlmostAdditive (f₁ ∘ f₂) <| (bound₁ + |f₁ 1|) * bound₂ + bound₁ * 3 :=
fun x y => calc
  |f₁ (f₂ (x + y)) - f₁ (f₂ x) - f₁ (f₂ y)|
    = |(f₁ ((f₂ (x + y) - f₂ x - f₂ y) + (f₂ x + f₂ y))
        - f₁ (f₂ (x + y) - f₂ x - f₂ y) - f₁ (f₂ x + f₂ y))
       + (f₁ (f₂ (x + y) - f₂ x - f₂ y))
       + (f₁ (f₂ x + f₂ y) - f₁ (f₂ x) - f₁ (f₂ y))|
        := congrArg Int.natAbs <| by
             conv in f₂ (x + y) =>
               rw [←Int.sub_add_cancel (f₂ (x + y)) (f₂ x + f₂ y), ←Int.sub_sub]
             linarith
  _ ≤ |f₁ ((f₂ (x + y) - f₂ x - f₂ y) + (f₂ x + f₂ y))
        - f₁ (f₂ (x + y) - f₂ x - f₂ y) - f₁ (f₂ x + f₂ y)|
      + |f₁ (f₂ (x + y) - f₂ x - f₂ y)|
      + |f₁ (f₂ x + f₂ y) - f₁ (f₂ x) - f₁ (f₂ y)|
        := Trans.trans (Int.natAbs_add_le ..)
                       (Nat.add_le_add_right (Int.natAbs_add_le ..) _)
  _ ≤ bound₁
      + ((bound₁ + |f₁ 1|) * |f₂ (x + y) - f₂ x - f₂ y| + bound₁)
      + bound₁
        := by refine Nat.add_le_add (Nat.add_le_add ?_ ?complex) ?_
              case complex =>
                conv in f₁ _ => arg 1; rewrite [←zsmul_int_one (_ - _ - _)]
                apply h₁.linear_growth_upper_bound
              all_goals apply h₁.almost_additive
  _ = (bound₁ + |f₁ 1|) * |f₂ (x + y) - f₂ x - f₂ y| + bound₁ * 3 := by linarith
  _ ≤ (bound₁ + |f₁ 1|) * bound₂ + bound₁ * 3
        := h₂.almost_additive .. |> Nat.mul_le_mul_left (k := _)
                                 |> Nat.add_le_add_right (k := _)

end AlmostAdditive

namespace QuasiMorphism
variable (f f₁ f₂ : QuasiMorphism G)

/- Haven't written local_wrapper to be able to destructure multiple
`AlmostAdditive` hypotheses yet. -/
protected def add : QuasiMorphism G where
  toFun := f₁ + f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    -- bound is filled in based on the proof :)
    ⟨_, AlmostAdditive.add h₁ h₂⟩

protected def neg : QuasiMorphism G where
  toFun := -f
  almostAdditive := local_wrapper neg 0

instance : AddCommGroup (QuasiMorphism G) where
  add := QuasiMorphism.add
  add_comm := by intros; ext; apply Int.add_comm
  add_assoc := by intros; ext; apply Int.add_assoc
  zero := ⟨0, 0, fun _ _ => Nat.le_refl ..⟩
  zero_add := by intros; ext; apply Int.zero_add
  add_zero f := by intros; ext; apply Int.add_zero
  neg := QuasiMorphism.neg
  add_left_neg := by intros; ext; apply Int.add_left_neg

/-- Composition with a quasi-morphism on ℤ, returning another quasi-morphism. -/
protected def comp  (f₁ : QuasiMorphism ℤ) (f₂ : QuasiMorphism G) : QuasiMorphism G where
  toFun := f₁ ∘ f₂
  almostAdditive :=
    let ⟨_, h₁⟩ := f₁.almostAdditive
    let ⟨_, h₂⟩ := f₂.almostAdditive
    -- bound is filled in based on the proof :)
    ⟨_, AlmostAdditive.comp h₁ h₂⟩

end QuasiMorphism

end AlgebraicStructure

section Quotient

def BoundedQuasiMorphs : AddSubgroup (QuasiMorphism G) where
  carrier := {f | ∃ bound, ∀ g, |f g| ≤ bound}

  add_mem' := fun {f₁} {f₂} ⟨bound₁, h₁⟩  ⟨bound₂, h₂⟩ => 
    ⟨bound₁ + bound₂, fun g => by
      have hf : (f₁ + f₂) g = f₁ g + f₂ g := rfl
      rewrite [hf]; linarith [Int.natAbs_add_le .., h₁ g, h₂ g]⟩

  zero_mem' := ⟨0, fun _ => Nat.le_refl ..⟩

  neg_mem' := fun {f} h => 
    let ⟨bound, h⟩ := h
    ⟨bound, fun g => by
      have hf : (-f) g = -f g := rfl
      simp [hf, h]⟩

/- #reduce BoundedQuasiMorphs -/
/- def BoundedQuasiMorphs_is_Normal : (BoundedQuasiMorphs (BoundedQuasiMorphs G)).Normal := -/ 
  /- AddSubgroup.normal_of_comm -/

end Quotient
