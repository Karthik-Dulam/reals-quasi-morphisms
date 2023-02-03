import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Range
import Mathlib.Data.List.MinMax
import RealsQuasiMorphisms.ArgMax
import Mathlib.Tactic.LibrarySearch

/-! Defines quasi-morphisms from an abelian group to ℤ and algebraic operations on them.

Reference(s):
1. http://web.science.mq.edu.au/~street/EffR.pdf
-/

-- Note: we can avoid the AbsoluteValue import by using simp? to get
-- exact `simp only`s for every use. However, this results in huge lists
-- of lemmas sometimes, so this hasn't been done for now.

-- For convenience. We can think about scoping this with sections later.
local notation (priority := high) "|" x "|" => Int.natAbs x

variable {G : Type u} [AddCommGroup G]

/- Remark: we have included `bound` as a field rather than
encapsulating the "almost additive" property into an `∃ bound, ...`.
This has the effect that the same function with different choices of
bound is a different `QuasiMorphism`, i.e., that `QuasiMorphism` is a
function with additional data, rather than just properties. -/
variable (G) in
structure QuasiMorphism where
  toFun : G → ℤ
  bound : ℕ 
  almostAdditive x y : |toFun (x + y) - toFun x - toFun y| ≤ bound

instance : CoeFun (QuasiMorphism G) fun _ => G → ℤ where
  coe := QuasiMorphism.toFun

namespace QuasiMorphism

section AlmostProperties
variable (f : QuasiMorphism G) (g : G) (m : ℤ)

/-- A quasi-morphism `f` maps 0 to 0, within an error of up to `f.bound`. -/
lemma almost_zero : |f 0| ≤ f.bound := by simpa using f.almostAdditive 0 0
/-   calc |f 0| = | -(f 0)|             := by rw [Int.natAbs_neg]
           _ = |f (0+0) - f 0 - f 0| := congrArg (|·|) <| by abel_nf
           _ ≤ f.bound               := f.almostAdditive 0 0 -/

/-- A quasi-morphism `f` respects negation, within an error of up to `f.bound * 2`. -/
lemma almost_neg : |f (-g) - (- (f g))| ≤ f.bound * 2 :=
  calc |f (-g) - (- (f g))|
           = |(f (-g) + f g - f 0) + f 0|
               := congrArg (|·|) <| by linarith
         _ ≤ |f (-g) + f g - f 0| + |f 0| := Int.natAbs_add_le ..
         _ = |f (-g + g) - f (-g) - f g| + |f 0|
               := by apply congrArg (· + |f 0|)
                     conv => arg 1 -- inside left ||
                             rewrite [←Int.natAbs_neg, ←add_left_neg g]
                     apply congrArg (|·|); linarith
         _ ≤ f.bound * 2
               := Nat.mul_two .. ▸ Nat.add_le_add (f.almostAdditive (-g) g)
                                                  f.almost_zero

/- First inequality proven in reference 1. -/
/-- A quasi-morphism `f` respects scaling by ℤ, within an error proportional to the scaling factor. -/
lemma almost_smul : |f (m • g) - m * f g| ≤ f.bound * (|m| + 1) := by
  cases m <;> (rename_i m; induction m)
  case ofNat.zero => simp; exact f.almost_zero
  case ofNat.succ m hᵢ =>
    rewrite [Int.ofNat_eq_coe, ofNat_zsmul] at hᵢ ⊢
    -- Rewriting these somewhat deep subterms with 'calc' would
    -- involve verbosely repeating the surroundings.
    rewrite [show m.succ • g = g + m • g from AddMonoid.nsmul_succ ..,
             show ↑(m.succ) * f g = f g + m * f g
               by rewrite [Nat.succ_eq_add_one, Nat.cast_succ]; linarith]
    calc |f (g + m • g) - (f g + m * f g)|
        = |(f (g + m • g) - f g - f (m • g)) + (f (m • g) - m * f g)|
            := congrArg (|·|) <| by linarith
      _ ≤ |f (g + m • g) - f g - f (m • g)| + |f (m • g) - m * f g|
            := Int.natAbs_add_le ..
      _ ≤ f.bound + f.bound * (m + 1)
            := Nat.add_le_add (f.almostAdditive ..) hᵢ
      _ = f.bound * (m.succ + 1)
            := by linarith
  case negSucc.zero =>
    rewrite [show Int.negSucc Nat.zero = -1 by rfl]; simpa using f.almost_neg g
  case negSucc.succ m hᵢ =>
    conv => lhs; rewrite [show Int.negSucc m.succ = Int.negSucc m - 1 by rfl]
    rewrite [sub_zsmul, one_smul, sub_mul, one_mul]
    calc |f (Int.negSucc m • g + -g) - (Int.negSucc m * f g - f g)|
        = | -(f (Int.negSucc m • g) - f (Int.negSucc m • g + -g) - f g)
            + (f (Int.negSucc m • g) - Int.negSucc m * f g)|
            := congrArg (|·|) <| by linarith
      _ ≤ |f (Int.negSucc m • g) - f (Int.negSucc m • g + -g) - f g|
          + |f (Int.negSucc m • g) - Int.negSucc m * f g|
            := by conv => rhs; arg 1; rewrite [←Int.natAbs_neg]
                  apply Int.natAbs_add_le
      _ ≤ f.bound + f.bound * (|Int.negSucc m| + 1)
            := Nat.add_le_add (by -- change `f (Int.negSucc m)` to `f (Int.negSucc m + -g + g)`
                                  rewrite [← congrArg f <| neg_add_cancel_right ..]
                                  apply f.almostAdditive _ g)
                              hᵢ
      _ = f.bound * (|Int.negSucc m.succ| + 1)
            := by simp only [Int.natAbs_negSucc]; linarith

/- Second inequality proven in reference 1, generalised to arbitrary abelian groups. -/
/-- A kind of commutativity of scaling by ℤ, one scale factor before and another after applying a quasi-morphism. -/
private lemma almost_smul_comm (m n : ℤ)
    : |n * f (m • g) - m * f (n • g)| ≤ f.bound * (|m| + |n| + 2) :=
  calc |n * f (m • g) - m * f (n • g)|
      = |(n * f (m • g) - f (n • m • g)) + (f (n • m • g) - m * f (n • g))|
          := congrArg (|·|) <| by linarith
    _ ≤ |n * f (m • g) - f (n • m • g)| + |f (n • m • g) - m * f (n • g)|
          := Int.natAbs_add_le ..
    _ = |f (n • m • g) - n * f (m • g)| + |f (m • n • g) - m * f (n • g)|
          := by conv => lhs; arg 1; rewrite [←Int.natAbs_neg]
                rewrite [smul_comm m n g]
                congr; linarith
    _ ≤ f.bound * (|n| + 1) + f.bound * (|m| + 1)
          := Nat.add_le_add (f.almost_smul ..) (f.almost_smul ..)
    _ = f.bound * (|m| + |n| + 2) := by linarith

/- `almost_smul_comm'` specialised to quasi-morphisms on integers and applied to 1.
Eq (1) of reference 1. -/
private lemma almost_smul_comm' (f : QuasiMorphism ℤ) (m n : ℤ)
    : |n * f m - m * f n| ≤ f.bound * (|m| + |n| + 2) := by
  conv => lhs; rewrite [←congrArg f (zsmul_int_one m), ←congrArg f (zsmul_int_one n)]
  exact f.almost_smul_comm 1 m n

end AlmostProperties

section AlgebraicStructure

/-- Addition of quasi-morphisms. -/
def add (f g : QuasiMorphism G) : QuasiMorphism G where
  toFun := f + g
  bound := f.bound + g.bound
  almostAdditive x y :=
    calc |f (x + y) + g (x + y) - (f x + g x) - (f y + g y)|
        = |(f (x + y) - f x - f y) + (g (x + y) - g x - g y)|
            := congrArg (|·|) <| by linarith
      _ ≤ |f (x + y) - f x - f y| + |g (x + y) - g x - g y|
            := Int.natAbs_add_le ..
      _ ≤ f.bound + g.bound
            := by apply Nat.add_le_add <;> apply almostAdditive

/-- Negation of quasi-morphisms. -/
def neg (f : QuasiMorphism G) : QuasiMorphism G where
  toFun := fun x => -(f x)
  bound := f.bound
  almostAdditive x y := by
    calc | -f (x + y) - (-f x) - (-f y)|
        = | -(-f (x + y) - (-f x) - (-f y))| := by rw [Int.natAbs_neg]
      _ = |f (x + y) - f x - f y|            := congrArg (|·|) <| by linarith
      _ ≤ f.bound                            := f.almostAdditive ..

-- We can't prove equality of quasi-morphisms yet. We need to prove an
-- ext lemma.
instance : AddCommGroup (QuasiMorphism G) where
  add := QuasiMorphism.add
  add_comm f g := sorry
  add_assoc f g h := sorry
  zero := ⟨0, 0, fun _ _ => Nat.le_refl ..⟩
  zero_add f := sorry
  add_zero f := sorry
  neg := QuasiMorphism.neg
  add_left_neg f := sorry

/-- Composition of quasi-morphisms on ℤ, returning another quasi-morphism. -/
def comp  (f : QuasiMorphism ℤ) (g : QuasiMorphism ℤ) : QuasiMorphism ℤ where
  toFun := f ∘ g
  bound := by
    let list_k : List ℤ := Int.range (-g.bound) (g.bound + 1)
    have hlist_k : list_k ≠ [] := by simp [Int.range]; linarith
    let k : ℤ := ArgMax list_k hlist_k (fun i => f (g x + g y + i))
  almostAdditive x y := by 
    let list_k : List ℤ := Int.range (-g.bound) (g.bound + 1)
    have hg : ∃ i ∈ list_k, g (x+y) - g x - g y = i := by
      /- simp [Int.range]; have hgg := g.almostAdditive x y; -/ 
      use (g (x+y) - g x - g y); simp; 
      /- linarith [Int.natAbs, Int.le_natAbs .., List.mem_range ..] -/
      sorry
      /- linarith [g.almostAdditive .., Int.natAbs_neg, Int.natAbs_add_le] -/
    have hlist_k : list_k ≠ [] := by simp [Int.range]; linarith
    let k : ℤ := ArgMax list_k hlist_k (fun i => f (g x + g y + i))
    have hf : f (g x + g y + k) 
        ≤ f (g x) + f (g y) + f (k) + 2*f.bound := by
      linarith 
        [@Int.le_natAbs (f (g x + g y + k) - f (g x + g y) - f (k)),
        f.almostAdditive ..,
        @Int.le_natAbs (f (g x + g y) - f (g x) - f (g y)),
        f.almostAdditive (g x) (g y),
        Int.le_natAbs]
    have hk : ∀ i ∈ list_k, f (g x + g y + i) ≤ f (g x + g y + k) := by
      apply le_ArgMax list_k hlist_k (fun i => f (g x + g y + i))
      /- simp [Int.range]; use 2*g.bound; exact ⟨by simp; linarith, by simp; linarith⟩ -/
    have : f (g (x + y)) - f (g x) - f (g y) ≤ f (k) + 2*f.bound := by 

      sorry
    simp [hf] at hg; linarith [Int.le_natAbs]


end AlgebraicStructure

end QuasiMorphism
