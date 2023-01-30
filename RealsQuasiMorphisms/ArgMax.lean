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
    · split  <;> simp 
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

#eval ArgMax [7, 28, 111,2,3,4,5] (by decide) (λ x => x + 19)

theorem ArgMax_ge (l : List ℤ) (hyp : l ≠ []) (f : ℤ → ℤ) :
  
#check List.mem_cons
