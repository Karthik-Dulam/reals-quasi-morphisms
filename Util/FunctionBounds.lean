import Util.Set
import Mathlib.Order.Bounds.Basic

namespace Function
variable {α β} [Preorder β] (f : α → β) (s : Set α) (b : β)

def BddAboveBy (b : β) := ∀ a, f a ≤ b
def BddAboveOnBy (b : β) := ∀ {a}, a ∈ s → f a ≤ b

def BddBelowBy (b : β) := ∀ a, f a ≥ b
def BddBelowOnBy (b : β) := ∀ {a}, a ∈ s → f a ≥ b

def BddAbove := Exists f.BddAboveBy
def BddAboveOn := Exists <| f.BddAboveOnBy s
def BddBelow := Exists f.BddBelowBy
def BddBelowOn := Exists <| f.BddBelowOnBy s

section Relationships

section SpecificBound

lemma bddAboveBy_iff_bddAboveOnBy_univ
    : f.BddAboveBy b ↔ f.BddAboveOnBy Set.univ b :=
  Set.ball_univ_iff.symm

lemma bddBelowBy_iff_bddBelowOnBy_univ
    : f.BddBelowBy b ↔ f.BddBelowOnBy Set.univ b :=
  bddAboveBy_iff_bddAboveOnBy_univ (β := βᵒᵈ) ..

lemma bddAboveOnBy_iff_upperBound_of_image
    : f.BddAboveOnBy s b ↔ b ∈ upperBounds (f '' s) :=
  ⟨Set.mem_image_elim'' (C := (· ≤ b)),
   (· (a := f _) ∘ s.mem_image_of_mem f)⟩

lemma bddBelowOnBy_iff_upperBound_of_image
    : f.BddBelowOnBy s b ↔ b ∈ lowerBounds (f '' s) :=
  bddAboveOnBy_iff_upperBound_of_image (β := βᵒᵈ) ..

lemma bddAboveBy_iff_upperBound_of_range
    : f.BddAboveBy b ↔ b ∈ upperBounds (Set.range f) :=
  bddAboveBy_iff_bddAboveOnBy_univ f b
  |>.trans <|
  Set.image_univ ▸ bddAboveOnBy_iff_upperBound_of_image f Set.univ b

lemma bddBelowBy_iff_upperBound_of_range
    : f.BddBelowBy b ↔ b ∈ lowerBounds (Set.range f) :=
  bddAboveBy_iff_upperBound_of_range (β := βᵒᵈ) ..

variable {f s b}

lemma bddAboveOnBy_of_bddAboveBy : f.BddAboveBy b → f.BddAboveOnBy s b :=
 Set.ball_of_forall

lemma bddBelowOnBy_of_bddBelowBy : f.BddBelowBy b → f.BddBelowOnBy s b :=
 bddAboveOnBy_of_bddAboveBy (β := βᵒᵈ)

lemma bddAboveOnBy_mono {s₁ s₂} {b} (h : s₁ ⊆ s₂)
    : f.BddAboveOnBy s₂ b → f.BddAboveOnBy s₁ b :=
  Set.ball_mono h

end SpecificBound

end Relationships

end Function
