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
