import Std.Logic
import Mathlib.Logic.Equiv.Defs

theorem Exists.imp'' {α β} {p : α → Prop} {q : β → Prop} {f : α → β}
    : (∀ {a : α}, p a → q (f a)) → (∃ a, p a) → ∃ b, q b :=
  @Exists.imp' α p β q f

def Equiv.quotientEquivQuotient {α : Sort u} {s₁ s₂ : Setoid α}
    (h : ∀ a b : α, s₁.r a b ↔ s₂.r a b)
    : Quotient s₁ ≃ Quotient s₂ where
  toFun  := @Quotient.map α α s₁ s₂ id fun a b => h a b |>.mp
  invFun := @Quotient.map α α s₂ s₁ id fun a b => h a b |>.mpr
  left_inv  := Quotient.ind fun _ => rfl
  right_inv := Quotient.ind fun _ => rfl
