import Std.Logic

theorem Exists.imp'' {α β} {p : α → Prop} {q : β → Prop} {f : α → β}
    : (∀ {a : α}, p a → q (f a)) → (∃ a, p a) → ∃ b, q b :=
  @Exists.imp' α p β q f
