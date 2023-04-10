import Util.OrderedGroup.Classes
import Util.OrderedGroup.CovContraLemmas
import Mathlib.GroupTheory.QuotientGroup

import Util.Logic
import Util.Equiv

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

variable (α : Type u)

-- Convenience notation for right coset space.
-- We might as well define it for the left coset space as well.
local notation:35
  _G:35 "⧸'" H:36 => Quotient <| QuotientGroup.leftRel H
local notation:35
  H:36 "⧹" _G:35 => Quotient <| QuotientGroup.rightRel H

/-- The set of elements equivalent to 1 in the sense of being both ≤ and ≥ to it. -/
@[to_additive "The set of elements equivalent to 0 in the sense of being both ≤ and ≥ to it."]
def antisymmRelOneSet [One α] [LE α] : Set α :=
  setOf <| AntisymmRel (· ≤ ·) 1

namespace Preorder variable [Preorder α]
def Antisymmetrization : Type u := _root_.Antisymmetrization α (· ≤ ·)

instance : PartialOrder (Antisymmetrization α) := by
  unfold Antisymmetrization; infer_instance
end Preorder

instance [inst : TotalPreorder α]
    : TotalOrder (Preorder.Antisymmetrization α) where
  le_total := Quotient.ind₂ inst.le_total

/-! ## Antisymmetrization for preordered groups -/

namespace LeftPreorderedGroup
variable [inst : LeftPreorderedGroup α]

@[to_additive]
def equivOneSubgroup : Subgroup α where
  carrier := antisymmRelOneSet α
  mul_mem' := fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
    ⟨le_mul_of_le_of_one_le h₁ h₁', mul_le_of_le_of_le_one h₂ h₂'⟩
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
def antisymmetrizationEquivQuotientEquivOneSubgroup
    : Preorder.Antisymmetrization α ≃ α ⧸' inst.equivOneSubgroup :=
  Equiv.quotientEquivQuotient antisymmRel_iff_leftRel_equivOne

@[to_additive]
instance : PartialOrder (α ⧸' inst.equivOneSubgroup) :=
  let equiv := antisymmetrizationEquivQuotientEquivOneSubgroup.symm
  PartialOrder.lift equiv equiv.injective

end LeftPreorderedGroup

namespace RightPreorderedGroup
variable [inst : RightPreorderedGroup α]

@[to_additive]
def equivOneSubgroup : Subgroup α where
  carrier := antisymmRelOneSet α
  mul_mem' := fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ =>
    ⟨le_mul_of_one_le_of_le h₁ h₁', mul_le_of_le_one_of_le h₂ h₂'⟩
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
def antisymmetrizationEquivQuotientEquivOneSubgroup
    : Preorder.Antisymmetrization α ≃ inst.equivOneSubgroup ⧹ α :=
  Equiv.quotientEquivQuotient antisymmRel_iff_rightRel_equivOne

@[to_additive]
instance : PartialOrder (inst.equivOneSubgroup ⧹ α) :=
  let equiv := antisymmetrizationEquivQuotientEquivOneSubgroup.symm
  PartialOrder.lift equiv equiv.injective

end RightPreorderedGroup

namespace PreorderedGroup
variable [inst : PreorderedGroup α]

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

@[to_additive]
instance : OrderedGroup (Preorder.Antisymmetrization α) :=
{ LeftPreorderedGroup.antisymmetrizationEquivQuotientEquivOneSubgroup.Group <|
    inferInstanceAs <| Group (α ⧸ inst.equivOneSubgroup),
  inferInstanceAs <| PartialOrder (Preorder.Antisymmetrization α) with
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

/-! ## Antisymmetrization for totally preordered groups -/

namespace LeftTotalPreorderedGroup
variable [inst : LeftTotalPreorderedGroup α]

@[to_additive]
instance : TotalOrder (α ⧸' inst.equivOneSubgroup) where
  le_total := Quotient.ind₂ inst.le_total

end LeftTotalPreorderedGroup

namespace RightTotalPreorderedGroup
variable [inst : RightTotalPreorderedGroup α]

@[to_additive]
instance : TotalOrder (inst.equivOneSubgroup ⧹ α) where
  le_total := Quotient.ind₂ inst.le_total

end RightTotalPreorderedGroup

namespace TotalPreorderedGroup
variable (α : Type u) [inst : TotalPreorderedGroup α]

@[to_additive]
instance : TotalOrderedGroup (Preorder.Antisymmetrization α) where
  le_total := Quotient.ind₂ inst.le_total

end TotalPreorderedGroup
