import RealsQuasiMorphisms.Field

import Mathlib.Order.Bounds.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace EudoxusReal

/-- The Eudoxus reals form a (linearly) ordered field. -/
noncomputable instance : LinearOrderedField EudoxusReal :=
  { inferInstanceAs <| Field EudoxusReal,
    inferInstanceAs <| LinearOrderedAddCommGroup EudoxusReal with
    zero_le_one :=
      ⟨0, fun {n} (h : n ≥ 0) =>
            show n - 0 ≥ 0 from Int.sub_zero n |>.symm ▸ h⟩
    mul_pos := fun a b h_a h_b => sorry }

/-- The supremum of a bounded-above set of Eudoxus real numbers. -/
def sup_of_bddAbove {s : Set EudoxusReal} (h₁ : BddAbove s) (h₂ : s.Nonempty)
    : { f : EudoxusReal // IsLUB s f } :=
  ⟨                 /- bound -/ sorry,
               /- is a bound -/ sorry,
   /- smaller than any bound -/ sorry⟩

noncomputable instance : ConditionallyCompleteLinearOrder EudoxusReal :=
  have : SupSet EudoxusReal :=
    ⟨fun s => open Classical in if h : BddAbove s ∧ s.Nonempty then
       (sup_of_bddAbove h.1 h.2).1
     else
       0⟩
  have := conditionallyCompleteLatticeOfSupₛ EudoxusReal
    (fun a b => ⟨max a b,
       fun _ h => h.elim (· ▸ le_max_left ..) (· ▸ le_max_right ..)⟩)
    (fun a b => ⟨min a b,
       fun _ h => h.elim (· ▸ min_le_left ..) (· ▸ min_le_right ..)⟩)
    (fun s h₁ h₂ => sorry /- (dif_pos (And.intro h₁ h₂)).symm.rec (motive := fun x _ => IsLUB s x) (sup_of_bddAbove h₁ h₂).2 -/)
  sorry /- { inferInstanceAs <| LinearOrder EudoxusReal, this with } -/

end EudoxusReal
