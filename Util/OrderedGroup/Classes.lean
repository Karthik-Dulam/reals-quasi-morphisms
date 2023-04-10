import Mathlib.Algebra.Order.Group.Defs

/-! # Ordered Group Structures -/

variable (α : Sort _)

/-! ## Preorder -/

/-- A left-preordered additive group is an additive group with a

preorder such that addition on the left is monotone. -/
class LeftPreorderedAddGroup extends AddGroup α, Preorder α where
  /-- Addition on the left is monotone in an left-preordered additive group. -/
  protected add_le_add_left : ∀ {a b}, a ≤ b → ∀ c : α, c + a ≤ c + b
/-- A left-preordered group is a group with a preorder such that
multiplication on the left is monotone. -/
class LeftPreorderedGroup extends Group α, Preorder α where
  /-- Multiplication on the left is monotone in an left-preordered group. -/
  protected mul_le_mul_left : ∀ {a b}, a ≤ b → ∀ c : α, c * a ≤ c * b
attribute [to_additive] LeftPreorderedGroup
/- This isn't automatic for some reason - it appears only the first
parent gets this automatically.
Probably related to https://github.com/leanprover/lean4/issues/1881. -/
attribute [to_additive] LeftPreorderedGroup.toPreorder

/-- A right-preordered additive group is an additive group with a
preorder such that addition on the right is monotone. -/
class RightPreorderedAddGroup extends AddGroup α, Preorder α where
  /-- Addition on the right is monotone in an right-preordered additive group. -/
  protected add_le_add_right : ∀ {a b}, a ≤ b → ∀ c : α, a + c ≤ b + c
/-- A right-preordered group is a group with a preorder such that
multiplication on the right is monotone. -/
class RightPreorderedGroup extends Group α, Preorder α where
  /-- Multiplication on the right is monotone in an right-preordered group. -/
  protected mul_le_mul_right : ∀ {a b}, a ≤ b → ∀ c : α, a * c ≤ b * c
attribute [to_additive] RightPreorderedGroup
attribute [to_additive] RightPreorderedGroup.toPreorder

/-- A preordered additive group is an additive group with a preorder
such that addition (on both sides) is monotone. -/
class PreorderedAddGroup extends LeftPreorderedAddGroup α, RightPreorderedAddGroup α
/-- A preordered group is a group with a preorder such that
multiplication (on both sides) is monotone. -/
class PreorderedGroup extends LeftPreorderedGroup α, RightPreorderedGroup α
attribute [to_additive] PreorderedGroup
attribute [to_additive] PreorderedGroup.toRightPreorderedGroup

/-- A preordered additive commutative group is an additive commutative
group with a preorder such that addition is monotone. -/
class PreorderedAddCommGroup extends AddCommGroup α, PreorderedAddGroup α where
  -- `add_le_add_left` can be deduced from `add_le_add_right`.
  add_le_add_left {a b : α} (h : a ≤ b) (c : α) :=
    add_comm a c ▸ add_comm b c ▸ add_le_add_right h c
  -- `add_le_add_right` can be deduced from `add_le_add_left`.
  add_le_add_right {a b : α} (h : a ≤ b) (c : α) :=
    add_comm c a ▸ add_comm c b ▸ add_le_add_left h c
/-- A preordered commutative group is an commutative group with a
preorder such that multiplication is monotone. -/
class PreorderedCommGroup extends CommGroup α, PreorderedGroup α where
  -- `mul_le_mul_left` can be deduced from `mul_le_mul_right`.
  mul_le_mul_left {a b : α} (h : a ≤ b) (c : α) :=
    mul_comm a c ▸ mul_comm b c ▸ mul_le_mul_right h c
  -- `mul_le_mul_right` can be deduced from `mul_le_mul_left`.
  mul_le_mul_right {a b : α} (h : a ≤ b) (c : α) :=
    mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left h c
attribute [to_additive] PreorderedCommGroup
attribute [to_additive] PreorderedCommGroup.toPreorderedGroup

/-! ## Partial order -/

/-- A left-ordered additive group is an additive group with a partial
order such that addition on the left is monotone. -/
class LeftOrderedAddGroup extends LeftPreorderedAddGroup α, PartialOrder α
/-- A left-ordered group is a group with a partial order such that
multiplication on the left is monotone. -/
class LeftOrderedGroup extends LeftPreorderedGroup α, PartialOrder α
attribute [to_additive] LeftOrderedGroup
attribute [to_additive] LeftOrderedGroup.toPartialOrder

/-- A right-ordered additive group is an additive group with a partial
order such that addition on the right is monotone. -/
class RightOrderedAddGroup extends RightPreorderedAddGroup α, PartialOrder α
/-- A right-ordered group is a group with a partial order such that
multiplication on the right is monotone. -/
class RightOrderedGroup extends RightPreorderedGroup α, PartialOrder α
attribute [to_additive] RightOrderedGroup
attribute [to_additive] RightOrderedGroup.toPartialOrder

/-- An ordered additive group is an additive group with a partial
order such that addition (on both sides) is monotone. -/
class OrderedAddGroup extends PreorderedAddGroup α, PartialOrder α
/-- An ordered group is a group with a partial order such that
multiplication (on both sides) is monotone. -/
class OrderedGroup extends PreorderedGroup α, PartialOrder α
attribute [to_additive] OrderedGroup
attribute [to_additive] OrderedGroup.toPartialOrder

namespace OrderedGroup variable [self : OrderedGroup α]
@[to_additive]
instance toLeftOrderedGroup : LeftOrderedGroup α := { self with }

@[to_additive]
instance toRightOrderedGroup : RightOrderedGroup α := { self with }
end OrderedGroup

-- Ordered(Add)CommGroup is already defined

namespace OrderedCommGroup variable [self : OrderedCommGroup α]
@[to_additive]
instance toPreorderedCommGroup : PreorderedCommGroup α where
  mul_le_mul_left := self.mul_le_mul_left _ _

@[to_additive]
instance toOrderedGroup : OrderedGroup α :=
  { self.toPreorderedCommGroup, self with }
end OrderedCommGroup

/-! ## Total preorder -/

class TotalPreorder extends Preorder α where
  /-- The ordering is total - any two elements are comparable. -/
  protected le_total : ∀ (a b : α), a ≤ b ∨ b ≤ a

/-- A left-totally preordered additive group is an additive group with
a total preorder such that addition on the left is monotone. -/
class LeftTotalPreorderedAddGroup extends LeftPreorderedAddGroup α,
                                          TotalPreorder α
/-- A left-totally preordered group is a group with a total preorder
such that multiplication on the left is monotone. -/
class LeftTotalPreorderedGroup extends LeftPreorderedGroup α,
                                       TotalPreorder α
attribute [to_additive] LeftTotalPreorderedGroup
attribute [to_additive] LeftTotalPreorderedGroup.toTotalPreorder

/-- A right-totally preordered additive group is an additive group with
a total preorder such that addition on the right is monotone. -/
class RightTotalPreorderedAddGroup extends RightPreorderedAddGroup α,
                                           TotalPreorder α
/-- A right-totally preordered group is a group with a total preorder
such that multiplication on the right is monotone. -/
class RightTotalPreorderedGroup extends RightPreorderedGroup α,
                                        TotalPreorder α
attribute [to_additive] RightTotalPreorderedGroup
attribute [to_additive] RightTotalPreorderedGroup.toTotalPreorder

/-- A totally-preordered additive group is an additive group with a
total preorder such that addition (on both sides) is monotone. -/
class TotalPreorderedAddGroup extends PreorderedAddGroup α, TotalPreorder α
/-- A totally-preordered group is a group with a total preorder such
that multiplication (on both sides) is monotone. -/
class TotalPreorderedGroup extends PreorderedGroup α, TotalPreorder α
attribute [to_additive] TotalPreorderedGroup
attribute [to_additive] TotalPreorderedGroup.toTotalPreorder

namespace TotalPreorderedGroup variable [self : TotalPreorderedGroup α]
@[to_additive]
instance toLeftTotalPreorderedGroup : LeftTotalPreorderedGroup α :=
  { self with }

@[to_additive]
instance toRightTotalPreorderedGroup : RightTotalPreorderedGroup α :=
  { self with }
end TotalPreorderedGroup

/-- A totally-preordered additive commutative group is an additive
commutative group with a total preorder such that addition is
monotone. -/
class TotalPreorderedAddCommGroup extends PreorderedAddCommGroup α,
                                          TotalPreorder α
/-- A totally-preordered commutative group is a commutative group with
a total preorder such that multiplication is monotone. -/
class TotalPreorderedCommGroup extends PreorderedCommGroup α,
                                       TotalPreorder α
attribute [to_additive] TotalPreorderedCommGroup
attribute [to_additive] TotalPreorderedCommGroup.toTotalPreorder

namespace TotalPreorderedCommGroup variable [self : TotalPreorderedCommGroup α]
@[to_additive]
instance toTotalPreorderedGroup : TotalPreorderedGroup α := { self with }
end TotalPreorderedCommGroup

/-! ## Total order -/

class TotalOrder extends PartialOrder α, TotalPreorder α

/-- A left-totally ordered additive group is an additive group with a
total order such that addition on the left is monotone. -/
class LeftTotalOrderedAddGroup extends LeftOrderedAddGroup α, TotalOrder α
/-- A left-totally ordered group is a group with a total order such
that multiplication on the left is monotone. -/
class LeftTotalOrderedGroup extends LeftOrderedGroup α, TotalOrder α
attribute [to_additive] LeftTotalOrderedGroup
attribute [to_additive] LeftTotalOrderedGroup.toTotalOrder

namespace LeftTotalOrderedGroup variable [self : LeftTotalOrderedGroup α]
@[to_additive]
instance toLeftTotalPreorderedGroup : LeftTotalPreorderedGroup α :=
  { self with }
end LeftTotalOrderedGroup

/-- A right-totally ordered additive group is an additive group with a
total order such that addition on the right is monotone. -/
class RightTotalOrderedAddGroup extends RightOrderedAddGroup α, TotalOrder α
/-- A right-totally ordered group is a group with a total order such
that multiplication on the right is monotone. -/
class RightTotalOrderedGroup extends RightOrderedGroup α, TotalOrder α
attribute [to_additive] RightTotalOrderedGroup
attribute [to_additive] RightTotalOrderedGroup.toTotalOrder

namespace RightTotalOrderedGroup variable [self : RightTotalOrderedGroup α]
@[to_additive]
instance toRightTotalPreorderedGroup : RightTotalPreorderedGroup α :=
  { self with }
end RightTotalOrderedGroup

/-- A totally-ordered additive group is an additive group with a total
order such that addition (on both sides) is monotone. -/
class TotalOrderedAddGroup extends OrderedAddGroup α, TotalOrder α
/-- A totally-ordered group is an group with a total order such that
multiplication (on both sides) is monotone. -/
class TotalOrderedGroup extends OrderedGroup α, TotalOrder α
attribute [to_additive] TotalOrderedGroup
attribute [to_additive] TotalOrderedGroup.toTotalOrder

namespace TotalOrderedGroup variable [self : TotalOrderedGroup α]
@[to_additive]
instance toTotalPreorderedGroup : TotalPreorderedGroup α := { self with }

@[to_additive]
instance toLeftTotalOrderedGroup : LeftTotalOrderedGroup α := { self with }

@[to_additive]
instance toRightTotalOrderedGroup : RightTotalOrderedGroup α := { self with }
end TotalOrderedGroup

/- We inherit from `TotalPreordered(Add)CommGroup` rather than
`Ordered(Add)CommGroup` in order to have the same signature for
mul_le_mul_left/right as the other classes defined in this file. -/

/-- A totally-ordered additive commutative group is an additive
commutative group with a total order such that addition is
monotone. -/
class TotalOrderedAddCommGroup extends TotalPreorderedAddCommGroup α, TotalOrder α
/-- A totally-ordered commutative group is a commutative group with a
total order such that multiplication is monotone. -/
class TotalOrderedCommGroup extends TotalPreorderedCommGroup α, TotalOrder α
attribute [to_additive] TotalOrderedCommGroup
attribute [to_additive] TotalOrderedCommGroup.toTotalOrder

namespace TotalOrderedCommGroup variable [self : TotalOrderedCommGroup α]
@[to_additive]
instance toOrderedCommGroup : OrderedCommGroup α where
  mul_le_mul_left _ _ := self.mul_le_mul_left

@[to_additive]
instance toTotalOrderedGroup : TotalOrderedGroup α := { self with }
end TotalOrderedCommGroup

/-! ### Linear orders (decidable total orders) -/

namespace LinearOrder

instance toTotalOrder [self : LinearOrder α] : TotalOrder α :=
  { self with }

variable {α} in
instance ofTotalOrder [TotalOrder α] [@DecidableRel α (· ≤ ·)] : LinearOrder α :=
{ ‹TotalOrder α› with decidable_le := ‹DecidableRel LE.le› }

end LinearOrder

-- LinearOrdered(Add)CommGroup is already defined

namespace LinearOrderedCommGroup

@[to_additive]
instance toTotalOrderedCommGroup [self : LinearOrderedCommGroup α]
    : TotalOrderedCommGroup α :=
{ self with mul_le_mul_left := self.mul_le_mul_left _ _ }

@[to_additive]
instance ofTotalOrderedCommGroup
    [inst : TotalOrderedCommGroup α] [@DecidableRel α (· ≤ ·)]
    : LinearOrderedCommGroup α :=
{ inst with
  mul_le_mul_left := fun _ _ => inst.mul_le_mul_left
  decidable_le := ‹DecidableRel LE.le› }

end LinearOrderedCommGroup

/-! ## `Co(ntra)variantClass` instances, enabling all usual lemmas about operations and inequalities. -/

namespace LeftPreorderedGroup
open LeftPreorderedGroup (mul_le_mul_left)
variable [LeftPreorderedGroup α]

@[to_additive]
instance to_covariantClass_left_le 
    : CovariantClass α α (· * ·) (· ≤ ·) where
  elim a _ _ h := mul_le_mul_left h a

@[to_additive]
instance to_contravariantClass_left_le
    : ContravariantClass α α (· * ·) (· ≤ ·) :=
  inferInstance

end LeftPreorderedGroup

namespace RightPreorderedGroup
open RightPreorderedGroup (mul_le_mul_right)
variable [RightPreorderedGroup α]

@[to_additive]
instance to_covariantClass_right_le
    : CovariantClass α α (Function.swap (· * ·)) (· ≤ ·) where
  elim a _ _ h := mul_le_mul_right h a

@[to_additive]
instance to_contravariantClass_right_le
    : ContravariantClass α α (Function.swap (· * ·)) (· ≤ ·) :=
  inferInstance

end RightPreorderedGroup

namespace PreorderedGroup
variable [PreorderedGroup α]

@[to_additive]
instance to_covariantClass_conj_left_le
    : CovariantClass α α (fun g a => g * a * g⁻¹) (· ≤ ·) where
  elim a _ _ := (mul_le_mul_right' · a⁻¹) ∘ (mul_le_mul_left' · a)

@[to_additive]
instance to_covariantClass_conj_right_le
    : CovariantClass α α (fun g a => g⁻¹ * a * g) (· ≤ ·) where
  elim a _ _ := (mul_le_mul_right' · a) ∘ (mul_le_mul_left' · a⁻¹)

@[to_additive]
instance to_contravariantClass_conj_left_le
    : ContravariantClass α α (fun g a => g * a * g⁻¹) (· ≤ ·) where
  elim _ _ _ := le_of_mul_le_mul_left' ∘ le_of_mul_le_mul_right'

@[to_additive]
instance to_contravariantClass_conj_right_le
    : ContravariantClass α α (fun g a => g⁻¹ * a * g) (· ≤ ·) where
  elim _ _ _ := le_of_mul_le_mul_left' ∘ le_of_mul_le_mul_right'

end PreorderedGroup
