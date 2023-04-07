import Mathlib.Data.Set.Image

/-! # Extra lemmas about `Set` -/

namespace Set
variable {α : Type _} {p : α → Prop}

-- In this file, we'll only use ∅ for the empty set.
-- So save on typing (∅ : Set α)
local notation (priority := high) "∅" => (∅ : Set _)

/-- This is Set.mem_image_elim with the changed binder ⦃y⦄. -/
abbrev mem_image_elim' {α β f s C} h ⦃y⦄ h' :=
  @Set.mem_image_elim α β f s C h y h'
/-- This is Set.mem_image_elim with the changed binder (y). -/
abbrev mem_image_elim'' {α β f s C} h y h' :=
  @Set.mem_image_elim α β f s C h y h'

/-! ## Quantifiers on Subsets -/

lemma ball_of_forall {s : Set α} : (∀ a, p a) → ∀ a ∈ s, p a :=
  fun h a _ => h a

lemma ball_univ_iff : (∀ a ∈ univ, p a) ↔ (∀ a, p a) :=
  ⟨fun h a => h a (mem_univ a), ball_of_forall⟩

lemma exists_of_bex {s : Set α} : (∃ a ∈ s, p a) → ∃ a, p a :=
  fun ⟨a, _, h⟩ => ⟨a, h⟩

lemma bex_univ_iff : (∃ a ∈ univ, p a) ↔ (∃ a, p a) :=
  ⟨exists_of_bex, fun ⟨a, h⟩ => ⟨a, mem_univ a, h⟩⟩

lemma ball_empty : ∀ a ∈ ∅, p a :=
  (not_mem_empty · |> absurd ·)

lemma not_bex_empty : ¬∃ a ∈ ∅, p a :=
  fun ⟨a, h, _⟩ => (not_mem_empty a) h

lemma ball_mono {s t : Set α} (h : s ⊆ t)
    : (∀ a ∈ t, p a) → ∀ a ∈ s, p a :=
  fun hₜ _ => (hₜ _ ∘ @h _)

lemma bex_mono {s t : Set α} (h : s ⊆ t)
    : (∃ a ∈ s, p a) → ∃ a ∈ t, p a :=
  Exists.imp <| fun _a => And.imp_left (@h _a)

end Set
