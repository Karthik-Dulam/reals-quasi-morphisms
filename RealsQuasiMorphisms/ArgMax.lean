import Mathlib

/- variable [LE  α] (α : Type u) -/
def largest (l : List ℤ)(_: l ≠ []) : ℤ :=
  match l with
  | head :: tail =>
      if c:tail = [] then head
      else
       max head (largest tail c)


/- #eval largest [7, 28, 111,2,3,4,5] (by decide) -/

/-- the result of `largest` applied to a list is a member of that list -/
theorem largest_in_list
  (l : List ℤ)(hyp : l ≠ []) :
    largest l hyp ∈ l := by
  match l with
  | head :: tail =>
      by_cases c:tail = []
      · simp [largest, c]
      · simp [largest, c]
        by_cases c':head ≥ largest tail (by simp [c])
        · left
          assumption
        · right
          have lem :
            max head (largest tail (by simp [c])) = largest tail (by simp [c]) := by
              apply max_eq_right
              apply le_of_not_le
              assumption
          rw [lem]
          simp [largest_in_list]

#check Nat.min_eq_right -- Nat.min_eq_right {a b : ℤ} (h : b ≤ a) : min a b = b


/--
`largest` is less than or equal to each element in the list
-/
theorem largest_le (l : List ℤ) (hyp : l ≠ []) :
  ∀ m : ℤ, m ∈ l → largest l hyp ≥ m  := match l with
  | head :: tail => by
    simp [largest, hyp]
    apply And.intro
    · split <;> simp
    · intro a hyp'
      have c'' : tail ≠ [] := by
        intro contra
        rw [contra] at hyp'
        contradiction
      simp [c'']
      right
      exact largest_le tail c'' a hyp'

def ArgMax (l : List ℤ) (_ : l ≠ []) (f : ℤ → ℤ) : ℤ :=
  match l with
  | head :: tail =>
      if c:tail = [] then head
      else
       if (f head) > f (ArgMax tail c f) then head
       else ArgMax tail c f


/- theorem classical_left (p q : Prop) (hpq : p ∨ q) : (¬p ∧ q) ∨ (p ∧ ¬ q) := by simp; -/

/-! This proof is very BAD. I'm not sure how to do it better. -/
def ArgMax_in_list  (l : List ℤ) (hyp : l ≠ []) (f : ℤ → ℤ) :
    (ArgMax l hyp f) ∈ l := by
  cases l
  case nil => contradiction
  case cons h t  =>
    simp [ArgMax]; split
    case inl ht => left; intro _; contradiction
    case inr ht =>
      by_cases c:(if f (ArgMax t (ht : ¬t = []) f) <
          f h then h else ArgMax t (ht : ¬t = []) f) ∈ t
      case pos =>  right; assumption
      case neg =>
        left; intro _ hh; split at c
        case h.inl hhh => exfalso; linarith
        case h.inr hhh => simp [ArgMax_in_list] at c





#eval ArgMax [7, 28, 111,2,3,4,5] (by decide) (λ x => x + 19)

/-! This proof is probably WORSE, and I have no idea how I proved it. -/
theorem le_ArgMax (l : List ℤ) (hyp : l ≠ []) (f : ℤ → ℤ) :
    ∀ i ∈ l, f i ≤ f (ArgMax l hyp f) := by
  intro i hi; cases l; contradiction
  case cons h t =>
    simp [ArgMax]; split
    case inl ht => simp [ht] at hi; simp [hi]
    case inr ht =>
      split
      case inl ht' =>
        cases hi; linarith
        case tail hi => linarith [le_ArgMax t ht f i hi]
      case inr ht' =>
        cases hi
        case head => linarith
        case tail hi => linarith [le_ArgMax t ht f i hi]

