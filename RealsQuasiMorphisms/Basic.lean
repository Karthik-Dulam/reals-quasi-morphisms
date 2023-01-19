import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch

-- Note: we can avoid the AbsoluteValue import by using simp? to get
-- exact `simp only`s for every use. However, this results in huge lists
-- of lemmas sometimes, so this hasn't been done for now.

-- For convenience. We can think about scoping this with sections later.
local notation (priority := high) "|" x "|" => Int.natAbs x

variable {G : Type u} [AddCommGroup G]

variable (G) in
structure QuasiMorphism where
  toFun : G → ℤ
  bound : ℕ 
  almostAdditive x y : |toFun (x + y) - toFun x - toFun y| ≤ bound

instance : CoeFun (QuasiMorphism G) fun _ => G → ℤ where
  coe := QuasiMorphism.toFun

/-- Reference: first inequality proven in
http://web.science.mq.edu.au/~street/EffR.pdf. -/
private lemma almost_linear (f : QuasiMorphism G) (g : G) (m : ℤ)
    : |f (m • g) - m * f g| ≤ (|m| + 1) * f.bound := by
  suffices forNats (g : G) (m : ℕ) : |f (m • g) - m * f g| ≤ (m + 1) * f.bound
  · cases m
    case ofNat m => simpa /- only [Int.ofNat_eq_coe, coe_nat_zsmul, Int.natAbs_ofNat] -/
                      using forNats g m
    case negSucc m => /- simpa using forNats (-g) m.succ -/ sorry
  -- Thus, proving the lemma reduces to proving `forNats`.
  induction m
  case zero => simpa /- only [Nat.zero_eq, (show 0 • g = 0 from AddMonoid.nsmul_zero ..), Nat.cast_zero, zero_mul, sub_zero, zero_add, one_mul, add_zero, sub_self, zero_sub, Int.natAbs_neg] -/
                     using f.almostAdditive 0 0
  case succ m hᵢ =>
    -- Rewriting these somewhat deep subterms with 'calc' would
    -- involve verbosely repeating the surroundings.
    rewrite [show m.succ • g = g + m • g from AddMonoid.nsmul_succ ..,
             show m.succ * f g = f g + m * f g
               -- It would be nice if linarith 'knew' about these lemmas
               by rewrite [Nat.succ_eq_add_one, Nat.cast_succ]; linarith]
    calc |f (g + m • g) - (f g + m * f g)|
        = |(f (g + m • g) - f g - f (m • g)) + (f (m • g) - m * f g)|
            := by congr; linarith
      _ ≤ |f (g + m • g) - f g - f (m • g)| + |f (m • g) - m * f g|
            := Int.natAbs_add_le ..
      _ ≤ f.bound + (m + 1) * f.bound
            := Nat.add_le_add (f.almostAdditive ..) hᵢ
      _ = (m.succ + 1) * f.bound
            := by linarith

/-- May generalize to qh(G,ℤ) later
Reference: second inequality proven in
http://web.science.mq.edu.au/~street/EffR.pdf.
Eq (1) --/
private lemma almost_cross_linear (f : QuasiMorphism ℤ) (m n:ℤ)
    : |n * f m - m * f n| ≤ (|m| + |n| + 2) * f.bound := by
  have h₁ : n * f m - m * f n = (n * f m - f (n*m)) + (f (n*m) - m * f n) := by linarith
  have h₂ : |n * f m - m * f n| ≤ |n * f m - f (n*m)|+ |f (n*m) - m * f n|:= by
    rw [h₁]
    exact Int.natAbs_add_le ..
  have h₃ : |n * f m - f (n*m)| ≤ (|n| + 1) * f.bound := by
    rw [← Int.natAbs_neg]; simp
    exact almost_linear ..
  have h₄ : |f (n*m) - m * f n| ≤ (|m| + 1) * f.bound := by
    rw [Int.mul_comm]
    exact almost_linear ..
  linarith

namespace QuasiMorphism


def comp  (f : QuasiMorphism ℤ) (g : QuasiMorphism ℤ) : QuasiMorphism ℤ where
  toFun := f ∘ g
  bound := sorry
  almostAdditive x y := by 
    have hg : g (x+y) ≤ g x + g y + g.bound := by linarith [Int.le_natAbs, g.almostAdditive ..]
    have hf (k : ℤ): f (g x + g y + k) 
        ≤ f (g x) + f (g y) + f (k) + 2*f.bound := by
      linarith 
        [@Int.le_natAbs (f (g x + g y + k) - f (g x + g y) - f (k)),
        f.almostAdditive ..,
        @Int.le_natAbs (f (g x + g y) - f (g x) - f (g y)),
        f.almostAdditive (g x) (g y),
        Int.le_natAbs]
    -- k = argmax{f(g(x) + g(y) + k}} for k in ℤ ∩ [-g.bound, g.bound]
    have k : ℕ := sorry 
    have hk : f (g x + g y + g.bound) ≤ f (g x + g y + k) := sorry
    have : f (g (x + y)) - f (g x) - f (g y) ≤ f (k) + 2*f.bound := by 
      sorry
    sorry


instance : HAdd (QuasiMorphism G) (QuasiMorphism G) (QuasiMorphism G) where
  hAdd := sorry

def add (f g : QuasiMorphism G): QuasiMorphism G where 
  toFun := f + g
  bound := f.bound + g.bound
  almostAdditive x y := sorry


instance : AddCommGroup (QuasiMorphism G) where 
  add := sorry
  add_assoc := sorry
  zero := sorry 
  zero_add := sorry
  add_zero := sorry 
  neg := sorry 
  add_left_neg := sorry
  add_comm := sorry

