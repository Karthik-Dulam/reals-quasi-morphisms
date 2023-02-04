import Mathlib.Data.Nat.Basic

import Util.Tactics

/-! Properties of `Int.natAbs` or otherwise useful for working with it. -/

-- TODO question namespace choices

/- `linarith` is powerful, but generates huge proof terms with all
kinds of stuff in them.

In another construction this caused a mysterious error, so I'm
avoiding `linarith` for simple proofs where it's unnecessary and not
especially convenient. -/

section Identities
namespace Int
variable (a b c : ℤ)

protected lemma sub_eq_neg_add : a - b = -b + a :=
  Int.add_comm .. ▸ Int.sub_eq_add_neg ..

protected lemma add_sub_cancel_right
    : a + (b - a) = b := by
  /- rewrite [Int.sub_eq_add_neg, Int.add_comm b (-a)]
  apply Int.add_neg_cancel_left -/
  rewrite [Int.add_comm]; apply Int.sub_add_cancel

end Int
end Identities

/- These should probably be proved for any OrderedSemigroup or something. -/
section NatIneqs
variable {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℕ}

lemma Nat.add_le_add₃ (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    : a₁ + a₂ + a₃ ≤ b₁ + b₂ + b₃ :=
  /- `by linarith` works, but I'm avoiding it. -/
  Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃

lemma Nat.add_le_add₄ (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
                      (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄)
    : a₁ + a₂ + a₃ + a₄ ≤ b₁ + b₂ + b₃ + b₄ :=
  /- `by linarith` works, but I'm avoiding it. -/
  Nat.add_le_add (Nat.add_le_add₃ h₁ h₂ h₃) h₄

section variable {a b₁ b₂ c₁ c₂ c₃ c₄ : ℕ} (h : a ≤ b₁ + b₂)

lemma Nat.le_trans_le_sum_left (h' : b₁ ≤ c₁ + c₂)
    : a ≤ c₁ + c₂ + b₂ :=
  calc a ≤ b₁ + b₂ := h
       _ ≤ c₁ + c₂ + b₂ := Nat.add_le_add_right h' b₂

lemma Nat.le_trans_le_sum_right (h' : b₂ ≤ c₁ + c₂)
    : a ≤ b₁ + c₁ + c₂ :=
  calc a ≤ b₁ + b₂ := h
       _ ≤ b₁ + c₁ + c₂ := Nat.add_assoc .. ▸ Nat.add_le_add_left h' b₁

lemma Nat.le_trans_le_sum (h₁' : b₁ ≤ c₁ + c₂) (h₂' : b₂ ≤ c₃ + c₄)
    : a ≤ c₁ + c₂ + c₃ + c₄ :=
  calc a ≤ b₁ + b₂           := h
       _ ≤ c₁ + c₂ + c₃ + c₄ := Nat.add_assoc .. ▸ Nat.add_le_add h₁' h₂'

end

end NatIneqs


/-! # Absolute value notation for convenience -/
namespace Int.natAbs            -- scoped to this namespace

/- This conflicts with match-case notation. -/
-- 	local notation (priority := high) "|" x "|" => Int.natAbs x
/- This is copied with modifications from Mathlib.Algebra.Abs. -/
/- Splitting into `syntax` and `macro_rules` seems to be necessary to use `local`. -/
scoped syntax:arg (name := __notation) (priority := default+1)
  atomic("|" noWs) term:min noWs "|" : term
scoped macro_rules (kind := __notation)
  | `(|$x:term|) => `(Int.natAbs $x)

/- This should make the pretty printer use this notation.
Copied with modifications from https://github.com/leanprover/lean4/issues/2045#issuecomment-1396168913. -/
@[scoped app_unexpander Int.natAbs]
private def __unexpander : Lean.PrettyPrinter.Unexpander
| `($(_) $n:term) => `(|$n|)
| _ => throw ()

end Int.natAbs


abbrev Int.diff : ℤ → ℤ → ℕ := (· - · |>.natAbs)

-- Lemmas about Int.natAbs and Int.diff
namespace Int
variable (a b c d : ℤ)

open scoped Int.natAbs

lemma natAbs_add_le₃ : |a + b + c| ≤ |a| + |b| + |c| :=
  /- `by linarith [Int.natAbs_add_le (a + b) c, Int.natAbs_add_le a b]`
  works, but I'm avoiding it. -/
  Nat.le_trans_le_sum_left (Int.natAbs_add_le (a + b) c)
                           (Int.natAbs_add_le a b)

lemma natAbs_add_le₄
    : |a + b + c + d| ≤ |a| + |b| + |c| + |d| :=
  /- `by linarith [Int.natAbs_add_le (a + b + c) d, Int.natAbs_add_le₃ a b c]`
  works, but I'm avoiding it. -/
  Nat.le_trans_le_sum_left (Int.natAbs_add_le (a + b + c) d)
                           (Int.natAbs_add_le₃ a b c)


@[simp] lemma diff_eq : a.diff b = |a - b| := rfl

lemma diff_self_eq_zero : a.diff a = 0 := by
  unfold diff natAbs; rw [Int.sub_self a]

lemma diff_comm : a.diff b = b.diff a := by
  unfold diff; rw [←Int.natAbs_neg, Int.neg_sub]

lemma triangle_ineq : a.diff c ≤ a.diff b + b.diff c := by
  unfold diff; rewrite [show a - c = (a - b) + (b - c)
                        by rw [←Int.add_sub_assoc, Int.sub_add_cancel]]
  apply Int.natAbs_add_le

lemma triangle_ineq' : b.diff c ≤ a.diff b + a.diff c :=
  diff_comm b a ▸ triangle_ineq b a c

lemma triangle_ineq₃ : a.diff d ≤ a.diff b + b.diff c + c.diff d :=
  Nat.le_trans_le_sum_left (triangle_ineq a c d) (triangle_ineq a b c)

end Int
