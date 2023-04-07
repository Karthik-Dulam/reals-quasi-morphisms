import Mathlib.Data.Set.Image
/-! # Extra lemmas about `Set` -/

namespace Set
variable {α : Type _} {p : α → Prop}

/-- This is Set.mem_image_elim with the changed binder ⦃y⦄. -/
abbrev mem_image_elim' {α β f s C} h ⦃y⦄ h' :=
  @Set.mem_image_elim α β f s C h y h'
/-- This is Set.mem_image_elim with the changed binder (y). -/
abbrev mem_image_elim'' {α β f s C} h y h' :=
  @Set.mem_image_elim α β f s C h y h'

end Set
