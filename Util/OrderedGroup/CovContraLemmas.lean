import Mathlib.Algebra.Order.Group.Defs

/-! # Lemmas about various ordered group structures

Note that `Util.OrderedGroup.Classes` already defines
`Co(ntra)variantClass` instances given ordered group structures, which
is enough for many lemmas to be applicable. This file consists
primarily of giving recognisable names to specialisations of those
lemmas.  -/

section Conj
variable {α} [Mul α] [Inv α] [LE α]
variable [CovariantClass α α (fun g => (g * · * g⁻¹)) (· ≤ ·)]
variable [CovariantClass α α (fun g => (g⁻¹ * · * g)) (· ≤ ·)]
variable [ContravariantClass α α (fun g => (g * · * g⁻¹)) (· ≤ ·)]
variable [ContravariantClass α α (fun g => (g⁻¹ * · * g)) (· ≤ ·)]

@[to_additive add_conj_le_add_conj_left']
lemma conj_le_conj_left' {a b : α} (h : a ≤ b) (g : α)
    : g * a * g⁻¹ ≤ g * b * g⁻¹ :=
  act_rel_act_of_rel (μ := fun g => (g * · * g⁻¹)) g h

@[to_additive le_of_add_conj_le_add_conj_left']
lemma le_of_conj_le_conj_left' {g a b : α} (h : g * a * g⁻¹ ≤ g * b * g⁻¹)
    : a ≤ b :=
  rel_of_act_rel_act (μ := fun g => (g * · * g⁻¹)) g h

@[to_additive add_conj_le_add_conj_iff_left]
lemma conj_le_conj_iff_left (g : α) {a b : α}
    : g * a * g⁻¹ ≤ g * b * g⁻¹ ↔ a ≤ b :=
  rel_iff_cov α α (fun g => (g * · * g⁻¹)) (· ≤ ·) g

@[to_additive add_conj_le_add_conj_right']
lemma conj_le_conj_right' {a b : α} (h : a ≤ b) (g : α)
    : g⁻¹ * a * g ≤ g⁻¹ * b * g :=
  act_rel_act_of_rel (μ := fun g => (g⁻¹ * · * g)) g h

@[to_additive le_of_add_conj_le_add_conj_right']
lemma le_of_conj_le_conj_right' {g a b : α} (h : g⁻¹ * a * g ≤ g⁻¹ * b * g)
    : a ≤ b :=
  rel_of_act_rel_act (μ := fun g => (g⁻¹ * · * g)) g h

@[to_additive add_conj_le_add_conj_iff_right]
lemma conj_le_conj_iff_right (g : α) {a b : α}
    : g⁻¹ * a * g ≤ g⁻¹ * b * g ↔ a ≤ b :=
  rel_iff_cov α α (fun g => (g⁻¹ * · * g)) (· ≤ ·) g

end Conj

section MulOne
variable {α} [MulOneClass α] [LE α]
variable [CovariantClass α α (· * ·) (· ≤ ·)]
variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
-- variable [ContravariantClass α α (· * ·) (· ≤ ·)]
-- variable [ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
lemma Left.le_mul_right_of_one_le {a : α} (h : 1 ≤ a) (b : α)
    : b ≤ b * a := by
  conv => lhs; rewrite [←mul_one b]
  exact mul_le_mul_left' h b

@[to_additive]
lemma Left.mul_right_le_of_le_one {a : α} (h : a ≤ 1) (b : α)
    : b * a ≤ b := by
  conv => rhs; rewrite [←mul_one b]
  exact mul_le_mul_left' h b

@[to_additive]
lemma Right.le_mul_left_of_one_le {a : α} (h : 1 ≤ a) (b : α)
    : b ≤ a * b := by
  conv => lhs; rewrite [←one_mul b]
  exact mul_le_mul_right' h b

@[to_additive]
lemma Right.mul_left_le_of_le_one {a : α} (h : a ≤ 1) (b : α)
    : a * b ≤ b := by
  conv => rhs; rewrite [←one_mul b]
  exact mul_le_mul_right' h b

end MulOne

section MulOneTrans
variable {α} [MulOneClass α] [Preorder α]
variable [CovariantClass α α (· * ·) (· ≤ ·)]
variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
-- variable [ContravariantClass α α (· * ·) (· ≤ ·)]
-- variable [ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
lemma Left.le_mul_of_le_left_of_one_le_right
    {a b c : α} (h₁ : a ≤ b) (h₂ : 1 ≤ c)
    : a ≤ b * c :=
  le_trans h₁ (Left.le_mul_right_of_one_le h₂ b)

@[to_additive]
lemma Left.mul_le_of_left_le_of_right_le_one
    {a b c : α} (h₁ : a ≤ b) (h₂ : c ≤ 1)
    : a * c ≤ b :=
  le_trans (Left.mul_right_le_of_le_one h₂ a) h₁

@[to_additive]
lemma Right.le_mul_of_le_right_of_one_le_left
    {a b c : α} (h₁ : a ≤ b) (h₂ : 1 ≤ c)
    : a ≤ c * b :=
  le_trans h₁ (Right.le_mul_left_of_one_le h₂ b)

@[to_additive]
lemma Right.mul_le_of_right_le_of_left_le_one
    {a b c : α} (h₁ : a ≤ b) (h₂ : c ≤ 1)
    : c * a ≤ b :=
  le_trans (Right.mul_left_le_of_le_one h₂ a) h₁

end MulOneTrans
