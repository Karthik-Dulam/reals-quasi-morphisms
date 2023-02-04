/-- `try_solve t` either solves the goal using `t` or does not change the proof state. -/
macro "try_solve " t:tacticSeq : tactic =>
  `(tactic| first | (solve | $t) | skip)

-- example : True ∨ False := by (try_solve apply Or.inr); trivial

/-- `lax_exact h` completes the goal using `h`, adding a subgoal to
rewrite the goal to the type of `h`.

It tries to automatically prove this subgoal using `trivial`.

The disadvantage is that no inference is possible at all in `h`. -/
macro "lax_exact " t:term : tactic =>
  /- `Eq.subst (Eq.symm ?_) $t` seems to get the motive wrong, so use
  `cast` and `congr` afterwards instead. -/
  `(tactic| focus refine cast (Eq.symm ?_) $t; congr; try_solve trivial)

/-- `lax_apply h` is essentially the same as `lax_exact (h ..)`.

As a result, it is currently useless (see end of docstring of `lax_exact`). -/
-- In fact, currently, it _is_ the same.
macro "lax_apply" t:term : tactic =>
  `(tactic| lax_exact $t ..)

/- example (a b : Nat) : a + b - b ≤ a + b := by
  lax_exact Nat.le_add_right a b
  apply Nat.add_sub_cancel -/
