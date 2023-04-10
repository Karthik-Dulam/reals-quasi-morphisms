import Util.OrderedGroup.Classes
import Util.OrderedGroup.CovContraLemmas
import Mathlib.Algebra.Order.Group.Defs -- (Total)PositiveCone
import Mathlib.Algebra.Group.Commute    -- Commute

/-! # Weak versions of `PositiveCone` and `TotalPositiveCone` for `AddGroup`s

These cones are 'weak' in the sense that they do not require that only
0 be both non-negative and non-positive. They induce (totally)
preordered group structures just as their non-weak versions induce
partially or totally ordered group structures.

We use `AddGroup` instead of `AddCommGroup` because it's not any more
difficult to do so. We also extend the original cone structures to
`AddGroup`s, adding coercions between the new general definition and
the existing `AddCommGroup` definition in mathlib.
-/

universe u

variable (α : Type u)

/-! ## The weak cone structures -/

namespace AddGroup
variable [AddGroup α]

/-- Like a positive cone, but without the antisymmetry requirement.
It is also defined for `AddGroup`s rather than `AddCommGroup`s.

Note: `WeakPositiveCone'` only yields a one-sided preordered group
structure.
-/
structure WeakPositiveCone' where
  nonneg : α → Prop
  pos : α → Prop := fun a => nonneg a ∧ ¬nonneg (-a)
  pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬nonneg (-a) := by intros; rfl
  zero_nonneg : nonneg 0
  add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b)
/-- Like a positive cone, but without the antisymmetry requirement.
It is also defined for `AddGroup`s rather than `AddCommGroup`s.
-/
structure WeakPositiveCone extends WeakPositiveCone' α where
  conj_nonneg_left : ∀ {a}, nonneg a → ∀ b, nonneg (b + a + -b)

variable {α} in
def WeakPositiveCone.conj_nonneg_right (P : WeakPositiveCone α)
    {a : α} (h : P.nonneg a) (b : α)
    : P.nonneg (-b + a + b) := by
  conv in (-b + a + b) => rhs; rw [←neg_neg b];
  exact P.conj_nonneg_left h (-b)

/-- Like a positive cone, but defined for `AddGroup`s rather than `AddCommGroup`s.

Note: `PositiveCone'` only yields a one-sided ordered group structure.
-/
structure PositiveCone' extends WeakPositiveCone' α where
  nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0
/-- Like a positive cone, but defined for `AddGroup`s rather than `AddCommGroup`s.
-/
structure PositiveCone extends PositiveCone' α, WeakPositiveCone α

/-- Like a total positive cone, but without the antisymmetry requirement.
It is also defined for `AddGroup`s rather than `AddCommGroup`s.

Note: `TotalWeakPositiveCone'` only yields a one-sided preordered group
structure.
-/
structure TotalWeakPositiveCone' extends WeakPositiveCone' α where
  nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a)
/-- Like a total positive cone, but without the antisymmetry requirement.
It is also defined for `AddGroup`s rather than `AddCommGroup`s.
-/
structure TotalWeakPositiveCone extends TotalWeakPositiveCone' α, WeakPositiveCone α

/-- Like a total positive cone, but defined for `AddGroup`s rather than `AddCommGroup`s.

Note: `TotalPositiveCone'` only yields a one-sided ordered group structure.
-/
structure TotalPositiveCone' extends PositiveCone' α, TotalWeakPositiveCone' α
/-- Like a total positive cone, but defined for `AddGroup`s rather than `AddCommGroup`s.
-/
structure TotalPositiveCone extends TotalPositiveCone' α, WeakPositiveCone α

end AddGroup

variable {α}

/-! ## Coercions between different kinds of cones -/
namespace AddGroup
variable [AddGroup α]

namespace TotalPositiveCone
def toPositiveCone (P : TotalPositiveCone α) : PositiveCone α :=
  { P with }
def toTotalWeakPositiveCone (P : TotalPositiveCone α)
    : TotalWeakPositiveCone α :=
  { P with }
end TotalPositiveCone

namespace ConeCoercions
-- From unprimed to primed
scoped instance : Coe (WeakPositiveCone α) (WeakPositiveCone' α) where
  coe := WeakPositiveCone.toWeakPositiveCone'
scoped instance : Coe (PositiveCone α) (PositiveCone' α) where
  coe := PositiveCone.toPositiveCone'
scoped instance : Coe (TotalWeakPositiveCone α) (TotalWeakPositiveCone' α) where
  coe := TotalWeakPositiveCone.toTotalWeakPositiveCone'
scoped instance : Coe (TotalPositiveCone α) (TotalPositiveCone' α) where
  coe := TotalPositiveCone.toTotalPositiveCone'
-- From `PositiveCone`
scoped instance : Coe (PositiveCone' α) (WeakPositiveCone' α) where
  coe := PositiveCone'.toWeakPositiveCone'
scoped instance : Coe (PositiveCone α) (WeakPositiveCone α) where
  coe := PositiveCone.toWeakPositiveCone
-- From `TotalWeakPositiveCone`
scoped instance : Coe (TotalWeakPositiveCone' α) (WeakPositiveCone' α) where
  coe := TotalWeakPositiveCone'.toWeakPositiveCone'
scoped instance : Coe (TotalWeakPositiveCone α) (WeakPositiveCone α) where
  coe := TotalWeakPositiveCone.toWeakPositiveCone
-- From `TotalPositiveCone`
scoped instance : Coe (TotalPositiveCone' α) (PositiveCone' α) where
  coe := TotalPositiveCone'.toPositiveCone'
scoped instance : Coe (TotalPositiveCone α) (PositiveCone α) where
  coe := TotalPositiveCone.toPositiveCone
scoped instance : Coe (TotalPositiveCone' α) (TotalWeakPositiveCone' α) where
  coe := TotalPositiveCone'.toTotalWeakPositiveCone'
scoped instance : Coe (TotalPositiveCone α) (TotalWeakPositiveCone α) where
  coe := TotalPositiveCone.toTotalWeakPositiveCone
end ConeCoercions

/-! ### Coercions from primed to unprimed, given that addition is commutative -/

@[to_additive AddCommGroup.add_conj_left_eq_of_comm]
def _root_.CommGroup.conj_left_eq_of_comm [Group α] [@IsCommutative α /- Mul.mul -/ (· * ·)]
    (a b : α)
    : a * b * a⁻¹ = b :=
  (show Commute a b from ‹IsCommutative α Mul.mul›.comm a b).mul_inv_cancel

@[to_additive AddCommGroup.add_conj_right_eq_of_comm]
def _root_.CommGroup.conj_right_eq_of_comm [Group α] [@IsCommutative α /- Mul.mul -/ (· * ·)]
    (a b : α)
    : a⁻¹ * b * a = b :=
  (show Commute a b from ‹IsCommutative α Mul.mul›.comm a b).inv_mul_cancel

variable [IsCommutative α /- Add.add -/ (· + ·)]

def WeakPositiveCone'.conj_nonneg_left_of_comm
    (P : WeakPositiveCone' α) {a : α} (h : P.nonneg a) (b : α)
    : P.nonneg (b + a + -b) :=
  AddCommGroup.add_conj_left_eq_of_comm b a |>.symm ▸ h

def WeakPositiveCone'.conj_nonneg_right_of_comm
    (P : WeakPositiveCone' α) {a : α} (h : P.nonneg a) (b : α)
    : P.nonneg (-b + a + b) :=
  AddCommGroup.add_conj_right_eq_of_comm b a |>.symm ▸ h

-- Having the first coercion available makes the others more concise.
open scoped ConeCoercions

namespace WeakPositiveCone

def ofWeakPositiveCone' (P : WeakPositiveCone' α)
    : WeakPositiveCone α :=
{ P with conj_nonneg_left := P.conj_nonneg_left_of_comm }

def equivWeakPositiveCone'_of_comm
    : WeakPositiveCone α ≃ WeakPositiveCone' α where
  toFun := toWeakPositiveCone'
  invFun := ofWeakPositiveCone'
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

end WeakPositiveCone

-- Dangerous?
namespace ConeCoercions
scoped instance : Coe (WeakPositiveCone' α) (WeakPositiveCone α) where
  coe := WeakPositiveCone.ofWeakPositiveCone'
end ConeCoercions

namespace PositiveCone

def ofPositiveCone' (P : PositiveCone' α) : PositiveCone α :=
  { P, (P : WeakPositiveCone α) with }

def equivPositiveCone'_of_comm : PositiveCone α ≃ PositiveCone' α where
  toFun := toPositiveCone'
  invFun := ofPositiveCone'
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

end PositiveCone

-- Dangerous?
namespace ConeCoercions
scoped instance : Coe (PositiveCone' α) (PositiveCone α) where
  coe := PositiveCone.ofPositiveCone'
end ConeCoercions

namespace TotalWeakPositiveCone

def ofTotalWeakPositiveCone' (P : TotalWeakPositiveCone' α)
    : TotalWeakPositiveCone α :=
  { P, (P : WeakPositiveCone α) with }

def equivTotalWeakPositiveCone'_of_comm
    : TotalWeakPositiveCone α ≃ TotalWeakPositiveCone' α where
  toFun := toTotalWeakPositiveCone'
  invFun := ofTotalWeakPositiveCone'
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

end TotalWeakPositiveCone

-- Dangerous?
namespace ConeCoercions
scoped instance : Coe (TotalWeakPositiveCone' α) (TotalWeakPositiveCone α) where
  coe := TotalWeakPositiveCone.ofTotalWeakPositiveCone'
end ConeCoercions

namespace TotalPositiveCone

def ofTotalPositiveCone' (P : TotalPositiveCone' α)
    : TotalPositiveCone α :=
  { P, (P : WeakPositiveCone α) with }

def equivTotalPositiveCone'_of_comm
    : TotalPositiveCone α ≃ TotalPositiveCone' α where
  toFun := toTotalPositiveCone'
  invFun := ofTotalPositiveCone'
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

end TotalPositiveCone

-- Dangerous?
namespace ConeCoercions
scoped instance : Coe (TotalPositiveCone' α) (TotalPositiveCone α) where
  coe := TotalPositiveCone.ofTotalPositiveCone'
end ConeCoercions

end AddGroup

/-! ### Relationship between mathlib's (Total)PositiveCone's and ours -/

namespace AddCommGroup
variable [AddCommGroup α]

namespace PositiveCone

def toAddGroupPositiveCone (P : PositiveCone α)
    : AddGroup.PositiveCone α :=
{ P with
  conj_nonneg_left := fun {a} h b =>
    add_conj_left_eq_of_comm b a |>.symm ▸ h }

def ofAddGroupPositiveCone (P : AddGroup.PositiveCone α)
    : PositiveCone α :=
  { P with }

def equivAddGroupPositiveCone
    : PositiveCone α ≃ AddGroup.PositiveCone α where
  toFun := toAddGroupPositiveCone
  invFun := ofAddGroupPositiveCone
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

end PositiveCone

namespace TotalPositiveCone

def toAddGroupTotalPositiveCone (P : TotalPositiveCone α)
    : AddGroup.TotalPositiveCone α :=
{ P, P.toPositiveCone.toAddGroupPositiveCone with }

def ofAddGroupTotalPositiveCone
    (P : AddGroup.TotalPositiveCone α) [DecidablePred P.nonneg]
    : TotalPositiveCone α :=
{ P with nonnegDecidable := ‹DecidablePred P.nonneg› }

def equivAddGroupTotalPositiveCone
    : TotalPositiveCone α
      ≃ Σ (P : AddGroup.TotalPositiveCone α), DecidablePred P.nonneg where
  toFun P := ⟨P.toAddGroupTotalPositiveCone, P.nonnegDecidable⟩
  invFun := Sigma.uncurry (@ofAddGroupTotalPositiveCone _ _)
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

end TotalPositiveCone

end AddCommGroup

namespace AddGroup.ConeCoercions
variable (α) [AddCommGroup α]

section open AddCommGroup.PositiveCone
scoped instance : Coe (PositiveCone α) (AddCommGroup.PositiveCone α) where
  coe := ofAddGroupPositiveCone
-- Dangerous?
scoped instance : Coe (AddCommGroup.PositiveCone α) (PositiveCone α) where
  coe := toAddGroupPositiveCone
end

section open AddCommGroup.TotalPositiveCone
scoped instance (P : TotalPositiveCone α) [DecidablePred P.nonneg]
    : CoeDep _ P (AddCommGroup.TotalPositiveCone α) where
  coe := ofAddGroupTotalPositiveCone P
-- Dangerous?
instance : Coe (AddCommGroup.TotalPositiveCone α) (TotalPositiveCone α) where
  coe := toAddGroupTotalPositiveCone
end

end AddGroup.ConeCoercions

/-! ## Relationship between cones and preordered group structures -/

section OfToPositiveCones namespace AddGroup
open scoped AddGroup.ConeCoercions

namespace WeakPositiveCone'

def toLeftPreorderedAddGroup [AddGroup α] (P : WeakPositiveCone' α)
    : LeftPreorderedAddGroup α where
  le a b := P.nonneg (-a + b)
  le_refl a := show P.nonneg (-a + a) from neg_add_self a ▸ P.zero_nonneg
  le_trans a b c h₁ h₂ :=
    show P.nonneg (-a + c) from
    show -a + c = (-a + b) + (-b + c) by
        rw [←add_assoc, add_neg_cancel_right]
      ▸ P.add_nonneg h₁ h₂
  add_le_add_left {a b} (h : P.nonneg (-a + b)) c :=
    show P.nonneg (-(c+a) + (c+b)) from
    show -(c+a) + (c+b) = -a + b by
        rw [neg_add_rev, add_assoc, neg_add_cancel_left]
      ▸ h

def ofLeftPreorderedAddGroup (inst : LeftPreorderedAddGroup α)
    : WeakPositiveCone' α where
  nonneg a := a ≥ 0
  zero_nonneg := inst.le_refl 0
  add_nonneg := Left.le_add_of_le_left_of_nonneg_right

/- We'll only do a few of these unless we redefine LeftPreorderedGroup
to be something like
`∑' (i₁ : AddGroup α) (i₂ : AddGroup α), add_le_add_left`. -/
/- def equivWeakPositiveCone' [inst : AddGroup α]
    : {inst : Preorder α // ∀ {a b : α}, a ≤ b → ∀ c : α, c + a ≤ c + b}
      ≃ WeakPositiveCone' α where
  toFun := fun ⟨inst', h⟩ => toWeakPositiveCone' { inst with add_le_add_left := h }
  invFun := fun P => let inst := ofWeakPositiveCone' P
                     ⟨inst.toPreorder, inst.add_le_add_left⟩
  left_inv inst := sorry
  right_inv P := sorry -/

def toRightPreorderedAddGroup [AddGroup α] (P : WeakPositiveCone' α)
    : RightPreorderedAddGroup α where
  le a b := P.nonneg (b + -a)
  le_refl a := show P.nonneg (a + -a) from add_neg_self a ▸ P.zero_nonneg
  le_trans a b c h₁ h₂ :=
    show P.nonneg (c + -a) from
    show c + -a = (c + -b) + (b  + -a) by
        rw [add_assoc, neg_add_cancel_left]
      ▸ P.add_nonneg h₂ h₁
  add_le_add_right {a b} (h : P.nonneg (b + -a)) c :=
    show P.nonneg ((b+c) + -(a+c)) from
    show (b+c) + -(a+c) = b + -a by
        rw [neg_add_rev, add_assoc, add_neg_cancel_left]
      ▸ h

def ofRightPreorderedAddGroup (inst : RightPreorderedAddGroup α)
    : WeakPositiveCone' α where
  nonneg a := a ≥ 0
  zero_nonneg := inst.le_refl 0
  add_nonneg := flip Right.le_add_of_le_right_of_nonneg_left

end WeakPositiveCone'

namespace WeakPositiveCone

theorem left_le_equiv_right_le [AddGroup α] (P : WeakPositiveCone α)
    (a b : α)
    : P.toLeftPreorderedAddGroup.le a b
      ↔ P.toRightPreorderedAddGroup.le a b :=
  ⟨(show P.nonneg (b + -a) from
     show a + (-a + b) + -a = b + -a by rw [add_neg_cancel_left]
       ▸ P.conj_nonneg_left · a),
   (show P.nonneg (-a + b) from
     show -a + (b + -a) + a = -a + b by rw [add_assoc, neg_add_cancel_right]
       ▸ P.conj_nonneg_right · a)⟩

def toPreorderedAddGroup [AddGroup α] (P : WeakPositiveCone α)
    : PreorderedAddGroup α where
  toLeftPreorderedAddGroup := P.toLeftPreorderedAddGroup
  add_le_add_right h c := by
    rewrite [P.left_le_equiv_right_le] at h ⊢
    exact P.toRightPreorderedAddGroup.add_le_add_right h c

def ofPreorderedAddGroup (inst : PreorderedAddGroup α)
    : WeakPositiveCone α where
  toWeakPositiveCone' := .ofLeftPreorderedAddGroup inst.1
  conj_nonneg_left {a} h b :=
    show 0 ≤ b + a + -b from
    show b + 0 + -b = 0 by rw [add_zero, add_neg_self]
      ▸ add_conj_le_add_conj_left' h b

end WeakPositiveCone

namespace PositiveCone'

def toLeftOrderedAddGroup [AddGroup α] (P : PositiveCone' α)
    : LeftOrderedAddGroup α where
  toLeftPreorderedAddGroup := P.toLeftPreorderedAddGroup
  le_antisymm a b (h₁ : P.nonneg (-a + b)) (h₂ : P.nonneg (-b + a)) :=
    neg_add_eq_zero.mp <| P.nonneg_antisymm
      h₁
      (show -b + a = -(-a + b) by rw [neg_add_rev, neg_neg]
        ▸ h₂)

def ofLeftOrderedAddGroup (inst : LeftOrderedAddGroup α)
    : PositiveCone' α where
  toWeakPositiveCone' := .ofLeftPreorderedAddGroup inst.1
  nonneg_antisymm {a} (h₁ : a ≥ 0) (h₂ : -a ≥ 0) :=
    le_antisymm (Left.nonneg_neg_iff.mp h₂) h₁

def toRightOrderedAddGroup [AddGroup α] (P : PositiveCone' α)
    : RightOrderedAddGroup α where
  toRightPreorderedAddGroup := P.toRightPreorderedAddGroup
  le_antisymm a b (h₁ : P.nonneg (b + -a)) (h₂ : P.nonneg (a + -b)) :=
    add_neg_eq_zero.mp <| P.nonneg_antisymm
      h₂
      (show -(a + -b) = b + -a by rw [neg_add_rev, neg_neg]
        ▸ h₁)

def ofRightOrderedAddGroup (inst : RightOrderedAddGroup α)
    : PositiveCone' α where
  toWeakPositiveCone' := .ofRightPreorderedAddGroup inst.1
  nonneg_antisymm {a} (h₁ : a ≥ 0) (h₂ : -a ≥ 0) :=
    le_antisymm (Right.nonneg_neg_iff.mp h₂) h₁

end PositiveCone'

namespace PositiveCone

def toOrderedAddGroup [AddGroup α] (P : PositiveCone α)
    : OrderedAddGroup α :=
  { WeakPositiveCone.toPreorderedAddGroup P,
    P.toLeftOrderedAddGroup with }

def ofOrderedAddGroup (inst : OrderedAddGroup α)
    : PositiveCone α :=
  { PositiveCone'.ofLeftOrderedAddGroup inferInstance,
    WeakPositiveCone.ofPreorderedAddGroup inst.1 with }

end PositiveCone

namespace TotalWeakPositiveCone'

def toLeftTotalPreorderedAddGroup [AddGroup α] (P : TotalWeakPositiveCone' α)
    : LeftTotalPreorderedAddGroup α where
  toLeftPreorderedAddGroup := P.toLeftPreorderedAddGroup
  le_total a b :=
    show P.nonneg (-a + b) ∨ P.nonneg (-b + a) from
    show -(-a + b) = -b + a by rw [neg_add_rev, neg_neg]
      ▸ P.nonneg_total (-a + b)

def ofLeftTotalPreorderedAddGroup (inst : LeftTotalPreorderedAddGroup α)
    : TotalWeakPositiveCone' α where
  toWeakPositiveCone' := .ofLeftPreorderedAddGroup inst.1
  nonneg_total a := inst.le_total 0 a |>.imp_right (Left.nonneg_neg_iff ..).mpr

def toRightTotalPreorderedAddGroup [AddGroup α] (P : TotalWeakPositiveCone' α)
    : RightTotalPreorderedAddGroup α where
  toRightPreorderedAddGroup := P.toRightPreorderedAddGroup
  le_total a b :=
    show P.nonneg (b + -a) ∨ P.nonneg (a + -b) from
    show -(b + -a) = a + -b by rw [neg_add_rev, neg_neg]
      ▸ P.nonneg_total (b + -a)

def ofRightTotalPreorderedAddGroup (inst : RightTotalPreorderedAddGroup α)
    : TotalWeakPositiveCone' α where
  toWeakPositiveCone' := .ofRightPreorderedAddGroup inst.1
  nonneg_total a := inst.le_total 0 a |>.imp_right (Right.nonneg_neg_iff ..).mpr

end TotalWeakPositiveCone'

namespace TotalWeakPositiveCone

def toTotalPreorderedAddGroup [AddGroup α] (P : TotalWeakPositiveCone α)
    : TotalPreorderedAddGroup α :=
  { WeakPositiveCone.toPreorderedAddGroup P,
    P.toLeftTotalPreorderedAddGroup with }

def ofTotalPreorderedAddGroup (inst : TotalPreorderedAddGroup α)
    : TotalWeakPositiveCone α :=
  { TotalWeakPositiveCone'.ofLeftTotalPreorderedAddGroup inferInstance,
    WeakPositiveCone.ofPreorderedAddGroup inst.1 with }

end TotalWeakPositiveCone

namespace TotalPositiveCone'

def toLeftTotalOrderedAddGroup [AddGroup α] (P : TotalPositiveCone' α)
    : LeftTotalOrderedAddGroup α :=
  { P.toLeftOrderedAddGroup,
    /- For unclear reasons,
    `TotalWeakPositiveCone'.toLeftTotalPreorderedAddGroup P` makes
    Lean forget that the arguments to le_total are of type `α`. -/
    P.toTotalWeakPositiveCone'.toLeftTotalPreorderedAddGroup with }

def ofLeftTotalOrderedAddGroup (inst : LeftTotalOrderedAddGroup α)
    : TotalPositiveCone' α :=
  { PositiveCone'.ofLeftOrderedAddGroup inst.1,
    TotalWeakPositiveCone'.ofLeftTotalPreorderedAddGroup inferInstance with }

def toTotalRightOrderedAddGroup [AddGroup α] (P : TotalPositiveCone' α)
    : RightTotalOrderedAddGroup α :=
  { P.toRightOrderedAddGroup,
    /- For unclear reasons,
    `TotalWeakPositiveCone'.toRightTotalPreorderedAddGroup P` makes
    Lean forget that the arguments to le_total are of type `α`. -/
    P.toTotalWeakPositiveCone'.toRightTotalPreorderedAddGroup with }

def ofRightTotalOrderedAddGroup (inst : RightTotalOrderedAddGroup α)
    : TotalPositiveCone' α :=
  { PositiveCone'.ofRightOrderedAddGroup inst.1,
    TotalWeakPositiveCone'.ofRightTotalPreorderedAddGroup inferInstance with }

end TotalPositiveCone'

namespace TotalPositiveCone

def toTotalOrderedAddGroup [AddGroup α] (P : TotalPositiveCone α)
    : TotalOrderedAddGroup α :=
  { PositiveCone.toOrderedAddGroup P,
    /- For unclear reasons,
    `TotalWeakPositiveCone.toTotalPreorderedAddGroup P` makes
    Lean forget that the arguments to le_total are of type `α`. -/
    P.toTotalWeakPositiveCone.toTotalPreorderedAddGroup with }

def ofTotalOrderedAddGroup (inst : TotalOrderedAddGroup α)
    : TotalPositiveCone α :=
  { TotalPositiveCone'.ofLeftTotalOrderedAddGroup inferInstance,
    WeakPositiveCone.ofPreorderedAddGroup inst.1.1 with }

end TotalPositiveCone

end AddGroup end OfToPositiveCones
