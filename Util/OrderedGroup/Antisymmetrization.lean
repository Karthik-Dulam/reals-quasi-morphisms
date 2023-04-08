import Util.OrderedGroup.Classes
import Mathlib.GroupTheory.QuotientGroup

import Util.Logic

/-! # Antisymmetrization, extended from Preorder's to PreorderedGroup's.

Given a left-preordered group, the equivalence relation `AntisymmRel`,
which is quotiented by to turn a preorder into a partial order, is
equivalent to the left coset relation of the subgroup of elements
equivalent (by `AntisymmRel`) to the identity. This can be used to
equip the quotient space of left cosets with a partial order.

A similar result holds for a right-preordered group with the right
coset space. For a preordered group (on both sides), the subgroup of
elements equivalent to the identity is a normal subgroup and the
quotient group becomes a partially ordered group.

Note: it is perhaps more usable to consider any (normal) subgroup of
the subgroup of elements equivalent to the identity, show that the
preorder descends to a preorder on the quotient space, and that the
result is a partial order iff the subgroup was all elements equivalent
to the identity.

However, `Mathlib.Order.Antisymmetrization` does not appear to do
this, this file essentially uses that, transferring the orders defined
there to the quotients by subgroups, and we don't necessarily need
that level of generality for this project. So it is omitted.
-/

universe u

-- Convenience notation for right coset space.
-- We might as well define it for the left coset space as well.
local notation:35
  _G:35 "⧸'" H:36 => Quotient <| QuotientGroup.leftRel H
local notation:35
  H:36 "⧹" _G:35 => Quotient <| QuotientGroup.rightRel H

/-- The set of elements equivalent to 1 in the sense of being both ≤ and ≥ to it. -/
@[to_additive "The set of elements equivalent to 0 in the sense of being both ≤ and ≥ to it."]
def equivOneSet (α : Type u) [One α] [LE α] : Set α :=
  setOf <| AntisymmRel (· ≤ ·) 1

namespace LeftPreorderedGroup
variable (α : Type u) [inst : LeftPreorderedGroup α]

@[to_additive]
def equivOneSubgroup : Subgroup α where
  carrier := equivOneSet α
  mul_mem' := fun {a b} ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
    ⟨calc 1 ≤ a := h₁
          _ = a * 1 := mul_one (M := α) a |>.symm
          _ ≤ a * b := inst.mul_le_mul_left h₁' a,
     calc 1 ≥ a := h₂
          _ = a * 1 := mul_one (M := α) a |>.symm
          _ ≥ a * b := inst.mul_le_mul_left h₂' a⟩
  one_mem' := antisymmRel_refl (· ≤ ·) 1
  inv_mem' := fun ⟨h₁, h₂⟩ =>
    ⟨Left.one_le_inv_iff.mpr h₂, Left.inv_le_one_iff.mpr h₁⟩

variable {α}

@[to_additive]
theorem antisymmRel_iff_leftRel_equivOne (a b : α)
    : AntisymmRel (· ≤ ·) a b ↔ (QuotientGroup.leftRel inst.equivOneSubgroup).r a b :=
  Iff.symm <| Iff.trans QuotientGroup.leftRel_apply <|
  show 1 ≤ a⁻¹ * b ∧ a⁻¹ * b ≤ 1 ↔ a ≤ b ∧ b ≤ a from
  Iff.and (le_inv_mul_iff_le ..) (inv_mul_le_one_iff ..)

@[to_additive]
theorem leftRel_equivOne_iff_antisymmRel (a b : α)
    : (QuotientGroup.leftRel inst.equivOneSubgroup).r a b ↔ AntisymmRel (· ≤ ·) a b :=
  inst.antisymmRel_iff_leftRel_equivOne a b |>.symm

/- Using just the equality of types makes it difficult to work with their terms. -/
/- @[to_additive]
theorem antisymmRelSetoid_eq_leftRel
    : AntisymmRel.setoid α (· ≤ ·) = QuotientGroup.leftRel inst.equivOneSubgroup :=
  Setoid.ext antisymmRel_iff_leftCoset_equivOne_eq -/

variable (α) in
@[to_additive]
def Antisymmetrization := α ⧸' inst.equivOneSubgroup

@[to_additive]
def quotient_equivOneSubgroup_equiv_antisymmetrization
    : Antisymmetrization α ≃ _root_.Antisymmetrization α (· ≤ ·) :=
  Equiv.quotientEquivQuotient leftRel_equivOne_iff_antisymmRel

@[to_additive]
instance : PartialOrder (Antisymmetrization α) :=
  PartialOrder.lift quotient_equivOneSubgroup_equiv_antisymmetrization
    quotient_equivOneSubgroup_equiv_antisymmetrization.injective

end LeftPreorderedGroup

namespace RightPreorderedGroup
variable (α : Type u) [inst : RightPreorderedGroup α]

@[to_additive]
def equivOneSubgroup : Subgroup α where
  carrier := equivOneSet α
  mul_mem' := fun {a b} ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
    ⟨calc 1 ≤ b := h₁'
          _ = 1 * b := one_mul (M := α) b |>.symm
          _ ≤ a * b := inst.mul_le_mul_right h₁ b,
     calc 1 ≥ b := h₂'
          _ = 1 * b := one_mul (M := α) b |>.symm
          _ ≥ a * b := inst.mul_le_mul_right h₂ b⟩
  one_mem' := antisymmRel_refl (· ≤ ·) 1
  inv_mem' := fun ⟨h₁, h₂⟩ =>
    ⟨Right.one_le_inv_iff.mpr h₂, Right.inv_le_one_iff.mpr h₁⟩

variable {α}

@[to_additive]
theorem antisymmRel_iff_rightRel_equivOne (a b : α)
    : AntisymmRel (· ≤ ·) a b ↔ (QuotientGroup.rightRel inst.equivOneSubgroup).r a b :=
  Iff.symm <| Iff.trans QuotientGroup.rightRel_apply <|
  show 1 ≤ b * a⁻¹ ∧ b * a⁻¹ ≤ 1 ↔ a ≤ b ∧ b ≤ a from
  Iff.and (le_mul_inv_iff_le ..) (mul_inv_le_one_iff ..)

@[to_additive]
theorem rightRel_equivOne_iff_antisymmRel (a b : α)
    : (QuotientGroup.rightRel inst.equivOneSubgroup).r a b ↔ AntisymmRel (· ≤ ·) a b :=
  inst.antisymmRel_iff_rightRel_equivOne a b |>.symm

variable (α) in
@[to_additive]
def Antisymmetrization := inst.equivOneSubgroup ⧹ α

@[to_additive]
def quotient_equivOneSubgroup_equiv_antisymmetrization
    : inst.equivOneSubgroup ⧹ α ≃ _root_.Antisymmetrization α (· ≤ ·) :=
  Equiv.quotientEquivQuotient rightRel_equivOne_iff_antisymmRel

@[to_additive]
instance : PartialOrder (Antisymmetrization α) :=
  PartialOrder.lift quotient_equivOneSubgroup_equiv_antisymmetrization
    quotient_equivOneSubgroup_equiv_antisymmetrization.injective

end RightPreorderedGroup

namespace PreorderedGroup
variable (α : Type u) [inst : PreorderedGroup α]

@[to_additive]
abbrev equivOneSubgroup := inst.toLeftPreorderedGroup.equivOneSubgroup

variable {α}

@[to_additive]
instance equivOneSubgroup_normal : (inst.equivOneSubgroup).Normal where
  conj_mem := fun a ⟨h₁, h₂⟩ g =>
    show 1 ≤ g * a * g⁻¹ ∧ g * a * g⁻¹ ≤ 1 from
    (calc g * 1 * g⁻¹ = g * g⁻¹ := congrArg (· * g⁻¹) <| mul_one g
                    _ = 1       := mul_inv_self g) ▸
      ⟨conj_le_conj_left' h₁ g, conj_le_conj_left' h₂ g⟩


variable (α) in
@[to_additive]
def Antisymmetrization := α ⧸ inst.equivOneSubgroup

@[to_additive]
instance : OrderedGroup (Antisymmetrization α) :=
{ inferInstanceAs <| Group (α ⧸ inst.equivOneSubgroup),
  inferInstanceAs <| PartialOrder inst.toLeftPreorderedGroup.Antisymmetrization with
  mul_le_mul_left := by
    apply Quotient.ind₂; intro a b (h : a ≤ b)
    apply Quotient.ind; intro c
    show c * a ≤ c * b          -- because ⟦·⟧ is a ordered group hom
    exact inst.mul_le_mul_left h c
  mul_le_mul_right := by
    apply Quotient.ind₂; intro a b (h : a ≤ b)
    apply Quotient.ind; intro c
    show a * c ≤ b * c          -- because ⟦·⟧ is a ordered group hom
    exact inst.mul_le_mul_right h c }

end PreorderedGroup
