import Game.Metadata
-- The closing level imports every world, so the ported worlds' theorems are in scope.
import Game.Levels.Outro

/-!
Replays the moves a player makes in the game's levels with Visual Lean's own tactics, to
check the levels are solvable the way the hints describe. Paths count from the root of
one side: `1` is a left operand (or a function's argument), `2` a right operand. Run with
`lake env lean test/VisualMoves.lean`.
-/

/-! ## Rewrite World -/

-- Level 0: substitute, then the check mark.
example (x y : ℕ) (hypothesis_1 : x = 1) (hypothesis_2 : y = 2) : x + y = 1 + 2 := by
  drag_rw_lhs_at [hypothesis_1] [1]
  drag_rw_lhs_at [hypothesis_2] [2]
  click_goal

-- Level 1: many substitutions; each rewrite only touches the chosen `0 + 0`.
example (x y z : ℕ) (hypothesis_x : x = 0) (hypothesis_y : y = 0) (hypothesis_z : z = 0)
    (zero_add_zero : (0 : ℕ) + 0 = 0) :
    (x + y) + z = 0 := by
  drag_rw_lhs_at [hypothesis_x] [1, 1]
  drag_rw_lhs_at [hypothesis_y] [1, 2]
  drag_rw_lhs_at [hypothesis_z] [2]
  drag_rw_lhs_at [zero_add_zero] [1]
  drag_rw_lhs [zero_add_zero]
  click_goal

-- Level 2: backwards substitutions.
example (x y : ℕ) (hypothesis_x : 0 = x) (hypothesis_y : 0 = y)
    (zero_add_zero : (0 : ℕ) + 0 = 0) : x + y = 0 := by
  drag_rw_lhs_at [← hypothesis_x] [1]
  drag_rw_lhs_at [← hypothesis_y] [2]
  drag_rw_lhs [zero_add_zero]
  click_goal

-- Level 3: a ∀-hypothesis used at two different places.
example (a b c : ℕ) (hx : a = 1) (hy : b = 2) (hz : c = 3)
    (add_comm : ∀ x y : ℕ, x + y = y + x) : (a + b) + c = 3 + (2 + 1) := by
  drag_rw_lhs_at [hx] [1, 1]
  drag_rw_lhs_at [hy] [1, 2]
  drag_rw_lhs_at [hz] [2]
  drag_rw_lhs [add_comm]
  drag_rw_lhs_at [add_comm] [2]
  click_goal

-- Level 4: fractions; associate, add up the fourths and the halves, then associate
-- the other way round to meet `h_three`.
example (frac1over2 frac1over4 : ℚ)
    (h_fourths : frac1over2 = frac1over4 + frac1over4)
    (h_halves : (1 : ℚ) = frac1over2 + frac1over2)
    (h_three : ((1 : ℚ) + 1) + 1 = 3)
    (add_assoc : ∀ x y z : ℚ, (x + y) + z = x + (y + z)) :
    ((frac1over2 + frac1over4) + frac1over4) + (1 + 1) = 3 := by
  drag_rw_lhs_at [add_assoc] [1]
  drag_rw_lhs_at [← h_fourths] [1, 2]
  drag_rw_lhs_at [← h_halves] [1]
  drag_rw_lhs [← add_assoc]
  drag_rw_lhs [h_three]
  click_goal

-- Level 5, the boss.
example (add_comm : ∀ x y : ℕ, x + y = y + x)
    (add_assoc : ∀ x y z : ℕ, (x + y) + z = x + (y + z))
    (h_two : (1 : ℕ) + 1 = 2) (h_three : (1 : ℕ) + 2 = 3) :
    (1 : ℕ) + 1 + 1 + 1 + 1 + 1 = 1 + 2 + 3 := by
  drag_rw_lhs_at [h_two] [1, 1, 1, 1]
  drag_rw_lhs_at [add_comm] [1, 1, 1]
  drag_rw_lhs_at [h_three] [1, 1, 1]
  drag_rw_rhs_at [h_three] [1]
  drag_rw_lhs_at [add_assoc] [1]
  drag_rw_lhs_at [h_two] [1, 2]
  drag_rw_lhs [add_assoc]
  drag_rw_lhs_at [add_comm] [2]
  drag_rw_lhs_at [h_three] [2]
  click_goal

/-! ## Rewrite World bonus levels -/

-- A1: each click on `zero_add_zero` rewrites the first `0 + 0`, reading left to right.
example (zero_add_zero : (0 : ℕ) + 0 = 0) :
    (0 : ℕ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 0 := by
  drag_rw_lhs_at [zero_add_zero] [1, 1, 1, 1, 1, 1]
  drag_rw_lhs_at [zero_add_zero] [1, 1, 1, 1, 1]
  drag_rw_lhs_at [zero_add_zero] [1, 1, 1, 1]
  drag_rw_lhs_at [zero_add_zero] [1, 1, 1]
  drag_rw_lhs_at [zero_add_zero] [1, 1]
  drag_rw_lhs_at [zero_add_zero] [1]
  drag_rw_lhs [zero_add_zero]
  click_goal

-- A2: forwards and backwards in turn; each click takes the first match.
example (a b : ℕ) (a_plus_b : a + b = b) (b_plus_a : a = b + a) :
    a + b + a + b + a = a := by
  drag_rw_lhs_at [a_plus_b] [1, 1, 1]
  drag_rw_lhs_at [← b_plus_a] [1, 1]
  drag_rw_lhs_at [a_plus_b] [1]
  drag_rw_lhs [← b_plus_a]
  click_goal

-- B1: unfold `x` into `f x` twice, then follow the chain.
example (f : ℕ → ℕ) (x a b c : ℕ) (fixed_point : f x = x) (hx : x = a)
    (fa : f a = b) (fb : f b = c) (fc : f c = 0) : f x = 0 := by
  drag_rw_lhs_at [← fixed_point] [1]
  drag_rw_lhs_at [← fixed_point] [1, 1]
  drag_rw_lhs_at [hx] [1, 1, 1]
  drag_rw_lhs_at [fa] [1, 1]
  drag_rw_lhs_at [fb] [1]
  drag_rw_lhs [fc]
  click_goal

/-! ## Rewrite Mode: a rule whose source side is a lone variable -/

-- `add_zero` backwards (`n ⇐ n + 0` on its card) rewrites exactly the chosen term, on a
-- goal or a hypothesis, with no Mathlib tactic.
example (a b : ℕ) (h : a + 0 + b = b + a) : a + b = b + a := by
  drag_rw_lhs_at [← MyNat.add_zero] [1]
  drag_goal h

example (a b : ℕ) (h : a + b + 0 = b + a) : a + b = b + a := by
  drag_rw_lhs [← MyNat.add_zero]
  drag_goal h

example (a b : ℕ) (h : a + b = b + a) : a + b = b + (a + 0) := by
  drag_rw_hyp_rhs_at h [← MyNat.add_zero] [2]
  drag_goal h

/-! ## Proposition World -/

-- Level 4: drag `(A → B) → C` onto the goal `C` to prove it backwards.
example (A B C : Prop) (hB : B) (hABC : (A → B) → C) : C := by
  drag_goal hABC
  intro _
  drag_goal hB

-- Level 7: the `↔` goal separates into its two directions with a click.
example (A B C : Prop) : ((A ∧ B) ∧ C) ↔ (A ∧ (B ∧ C)) := by
  click_goal
  · intro h
    click_prop h
    click_prop left
    click_goal
    · drag_goal left1
    · click_goal
      · drag_goal right1
      · drag_goal right
  · intro h
    click_prop h
    click_prop right
    click_goal
    · click_goal
      · drag_goal left
      · drag_goal left1
    · drag_goal right1

/-! ## Proposition World: the levels past the fork -/

-- Level 8: the right side, then the left side of that.
example (A B C : Prop) (hB : B) : A ∨ (B ∨ C) := by
  click_goal_right
  click_goal_left
  drag_goal hB

-- Level 9: split the `∨` hypothesis before the `∨` goal.
example (A B : Prop) : (A ∨ B) → (B ∨ A) := by
  intro h
  click_prop h
  · click_goal_right
    drag_goal left
  · click_goal_left
    drag_goal right

-- Level 10: both directions, splitting each `∨` hypothesis before choosing a side.
example (A B C : Prop) : ((A ∨ B) ∨ C) ↔ (A ∨ (B ∨ C)) := by
  click_goal
  · intro h
    click_prop h
    · click_prop left
      · click_goal_left
        drag_goal left1
      · click_goal_right
        click_goal_left
        drag_goal right
    · click_goal_right
      click_goal_right
      drag_goal right
  · intro h
    click_prop h
    · click_goal_left
      click_goal_left
      drag_goal left
    · click_prop right
      · click_goal_left
        click_goal_right
        drag_goal left
      · click_goal_right
        drag_goal right1

-- Level 11: a proof of `False` proves anything.
example (h : False) : (1 : ℕ) = 2 := by
  drag_goal_exfalso h

-- Level 12: `¬` goals introduce like implications, and `¬` cards apply like them.
example (A : Prop) (hA : A) : ¬¬A := by
  click_goal
  drag_to hA h
  drag_goal h1

-- Level 12 again, proving the `False` goal backwards.
example (A : Prop) (hA : A) : ¬¬A := by
  click_goal
  drag_goal h
  drag_goal hA

-- Level 13: get `B` from `A → B`, then `False` from `¬B`.
example (A B : Prop) : A → ¬B → ¬(A → B) := by
  click_goal
  click_goal
  click_goal
  drag_to h h2
  drag_to h3 h1
  drag_goal h4

-- Level 13: premises go in order, so `¬B`'s card takes `B` and nothing else.
example (A B : Prop) : A → ¬B → ¬(A → B) := by
  click_goal
  click_goal
  click_goal
  fail_if_success drag_to h h1
  fail_if_success drag_to h2 h1
  drag_goal h1
  drag_goal h2
  drag_goal h

-- Level 14: prove the `False` goal backwards with `¬(A ∧ B)`, as the hint says.
example (A B : Prop) : A → ¬(A ∧ B) → ¬B := by
  click_goal
  click_goal
  click_goal
  drag_goal h1
  click_goal
  · drag_goal h
  · drag_goal h2

-- Level 15, the boss.
example (A B : Prop) : ¬(A ∨ B) ↔ (¬A ∧ ¬B) := by
  click_goal
  · click_goal
    click_goal
    · click_goal
      drag_goal h
      click_goal_left
      drag_goal h1
    · click_goal
      drag_goal h
      click_goal_right
      drag_goal h1
  · click_goal
    click_prop h
    click_goal
    click_prop h
    · drag_to left1 left
      drag_goal h
    · drag_to right1 right
      drag_goal h

/-! ## Proposition World bonus levels -/

-- A1: split both hypotheses, and in each case either prove the left side or show `C`.
example (A B C : Prop) :
    (A ∨ (B → C)) → ((B ∨ (A → C)) → ((A ∧ B) ∨ ((A ∨ B) → C))) := by
  intro h1
  intro h2
  click_prop h1
  · click_prop h2
    · click_goal_left
      click_goal
      · drag_goal left
      · drag_goal left1
    · click_goal_right
      intro _
      drag_goal right
      drag_goal left
  · click_prop h2
    · click_goal_right
      intro _
      drag_goal right
      drag_goal left
    · click_goal_right
      intro h3
      click_prop h3
      · drag_goal right1
        drag_goal left
      · drag_goal right
        drag_goal right2

-- B1: `¬(P ∨ ¬P)` proves the `False` goal backwards, twice: once to get to `¬P`, and
-- once more with the `P` that gives.
example : ∀ P : Prop, ¬¬(P ∨ ¬P) := by
  click_goal
  click_goal
  drag_goal h
  click_goal_right
  click_goal
  drag_goal h
  click_goal_left
  drag_goal h1

-- C1: the valid direction of the other law.
example (A B : Prop) : (¬A ∨ ¬B) → ¬(A ∧ B) := by
  click_goal
  click_goal
  click_prop h1
  click_prop h
  · drag_to left left1
    drag_goal h
  · drag_to right1 right
    drag_goal h

-- C2: with the Law of Excluded Middle for both.
example (A B : Prop) (hA : A ∨ ¬A) (hB : B ∨ ¬B) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  click_goal
  click_prop hA
  · click_prop hB
    · click_goal_left
      click_goal
      drag_goal h
      click_goal
      · drag_goal left
      · drag_goal left1
    · click_goal_right
      drag_goal right
  · click_goal_left
    drag_goal right

-- C3: with the Weak Law of Excluded Middle, the `False` goal needs both `¬¬` hypotheses.
example (A B : Prop) (hA : ¬A ∨ ¬¬A) (hB : ¬B ∨ ¬¬B) : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  click_goal
  click_prop hA
  · click_goal_left
    drag_goal left
  · click_prop hB
    · click_goal_right
      drag_goal left
    · click_goal_left
      click_goal
      drag_goal right1
      click_goal
      drag_goal h
      click_goal
      · drag_goal h1
      · drag_goal h2

/-! ## The specialization view on a `∀ P : Prop` hypothesis -/

-- A proposition built from the context's propositions, `False` and the connectives is
-- sent bracketed, as the view shows it (bonus levels B2 and B3 use it).
example (A : Prop) (dne : ∀ P : Prop, ¬¬P → P) : A ∨ ¬A := by
  specialize_forall_as dne1 dne P (A ∨ (¬A))
  drag_goal dne1
  click_goal
  drag_goal h
  click_goal_right
  click_goal
  drag_goal h
  click_goal_left
  drag_goal h1

example (A B : Prop) (h : ∀ P : Prop, P → P) (hAB : (A ∧ B) → (False ↔ A)) : (A ∧ B) → (False ↔ A) := by
  specialize_forall_as h1 h P ((A ∧ B) → (False ↔ A))
  drag_to hAB h1
  exact h2

/-! ## Dragging a hypothesis onto an identical one merges the two -/

-- The dragged card goes and the one it was dropped on stays. Variables of one type
-- are not propositions, so they never merge.
set_option linter.unusedVariables false in
example (A B : Prop) (x y : ℕ) (h1 : A → B) (h2 : A → B) (hx : x = y) (hy : x = y) : A → B := by
  drag_to h1 h2
  fail_if_success exact h1
  drag_to hy hx
  fail_if_success exact absurd hy
  fail_if_success drag_to x y
  drag_goal h2

/-! ## Successor World -/

namespace MyNat

-- Level 1: fold the successors back into numerals.
example : S (S 0) = 2 := by
  drag_rw_lhs_at [← one_eq_succ_zero] [1]
  drag_rw_lhs [← two_eq_succ_one]
  click_goal

-- Level 2: a theorem, proved with the axioms.
example (a : ℕ) : a + 1 = S a := by
  drag_rw_lhs_at [one_eq_succ_zero] [2]
  drag_rw_lhs [add_succ]
  drag_rw_lhs_at [add_zero] [1]
  click_goal

-- Level 3, the boss: level 2's theorem saves time.
theorem add_one' (a : ℕ) : a + 1 = S a := by
  rw [one_eq_succ_zero, add_succ, add_zero]

example : (1 : ℕ) + 1 + 1 + 1 = 4 := by
  drag_rw_lhs [add_one']
  drag_rw_lhs_at [add_one'] [1]
  drag_rw_lhs_at [add_one'] [1, 1]
  drag_rw_rhs [four_eq_succ_three]
  drag_rw_rhs_at [three_eq_succ_two] [1]
  drag_rw_rhs_at [two_eq_succ_one] [1, 1]
  click_goal

-- Level 4, Crossing the Beams (0): the goal is opened in Rewriting Mode, where `hx` is
-- a rule; the check mark closes it.
example (x : ℕ) (hx : x = 1) : x + 1 = 2 := by
  drag_rw_lhs_at [hx] [1]
  drag_rw_lhs [add_one']
  drag_rw_lhs [← two_eq_succ_one]
  click_goal

-- Level 5, Crossing the Beams (1): rewrite `hx` into `x = 2` in Rewriting Mode, go back,
-- and drag it onto `hy`.
example (x y : ℕ) (hx : x = 1 + 1) (hy : x = 2 → y = 0) : y = 0 := by
  drag_rw_hyp_rhs hx [add_one']
  drag_rw_hyp_rhs hx [← two_eq_succ_one]
  drag_to hx hy
  drag_goal h

-- Level 6, the boss: tidy up the hypotheses, as the hint says, then the goal.
example (a b c : ℕ) (ha : a = 0 + 0 + 0) (hb : S (0 + 0) = b) (hc : c = b + (a + a) + 0) :
    c + c + c + c = 4 := by
  drag_rw_hyp_rhs ha [add_zero]
  drag_rw_hyp_rhs ha [add_zero]
  drag_rw_hyp_lhs_at hb [add_zero] [1]
  drag_rw_hyp_lhs hb [← one_eq_succ_zero]
  drag_rw_hyp_rhs hc [add_zero]
  drag_rw_hyp_rhs_at hc [ha] [2, 1]
  drag_rw_hyp_rhs_at hc [ha] [2, 2]
  drag_rw_hyp_rhs_at hc [add_zero] [2]
  drag_rw_hyp_rhs hc [add_zero]
  drag_rw_hyp_rhs hc [← hb]
  drag_rw_lhs_at [hc] [1, 1, 1]
  drag_rw_lhs_at [hc] [1, 1, 2]
  drag_rw_lhs_at [hc] [1, 2]
  drag_rw_lhs_at [hc] [2]
  drag_rw_lhs [add_one']
  drag_rw_lhs_at [add_one'] [1]
  drag_rw_lhs_at [add_one'] [1, 1]
  drag_rw_rhs [four_eq_succ_three]
  drag_rw_rhs_at [three_eq_succ_two] [1]
  drag_rw_rhs_at [two_eq_succ_one] [1, 1]
  click_goal

/-! ## Induction World -/

-- Level 0, `zero_add`: click the goal to fix `n`, then induct on it.
example : ∀ n : ℕ, 0 + n = n := by
  click_goal
  induction n with d hd
  · drag_rw_lhs [add_zero]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_lhs_at [hd] [1]
    click_goal

theorem zero_add' : ∀ n : ℕ, 0 + n = n := by
  intro n
  induction n with d hd
  · rw [add_zero]
  · rw [add_succ, hd]

-- Level 1, `succ_add`.
example : ∀ a b : ℕ, S a + b = S (a + b) := by
  click_goal
  click_goal
  induction b with d hd
  · drag_rw_lhs [add_zero]
    drag_rw_rhs_at [add_zero] [1]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_rhs_at [add_succ] [1]
    drag_rw_lhs_at [hd] [1]
    click_goal

theorem succ_add' : ∀ a b : ℕ, S a + b = S (a + b) := by
  intro a b
  induction b with d hd
  · rw [add_zero, add_zero]
  · rw [add_succ, add_succ, hd]

-- Level 2, commutativity.
example : ∀ a b : ℕ, a + b = b + a := by
  click_goal
  click_goal
  induction b with d hd
  · drag_rw_lhs [add_zero]
    drag_rw_rhs [zero_add']
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_rhs [succ_add']
    drag_rw_lhs_at [hd] [1]
    click_goal

-- Level 3, associativity.
example : ∀ a b c : ℕ, a + b + c = a + (b + c) := by
  click_goal
  click_goal
  click_goal
  induction c with d hd
  · drag_rw_lhs [add_zero]
    drag_rw_rhs_at [add_zero] [2]
    click_goal
  · drag_rw_lhs [add_succ]
    drag_rw_rhs_at [add_succ] [2]
    drag_rw_rhs [add_succ]
    drag_rw_lhs_at [hd] [1]
    click_goal

/-! ## ≠ World -/

-- Level 0: an equality hypothesis proves the matching goal by dragging; Rewriting Mode
-- on the goal is off. From Induction World's level 0 on in the spec, a goal's
-- variables are fixed by clicking it.
example : ∀ x : ℕ, x = 1 → x = 1 := by
  click_goal
  click_goal
  drag_goal h

-- Level 1: swap `1 = x` round in Rewriting Mode, feed it to the implication, swap the
-- result round the same way, and drag it to the goal.
example (x y : ℕ) (hx : 1 = x) (hy : x = 1 → y = 2) : 2 = y := by
  symm at hx
  drag_to hx hy
  symm at h
  drag_goal h

-- Level 2: an equality hypothesis proves the matching goal by dragging.
example : ∀ x : ℕ, x = 1 → (x = 1 ∧ (S x = 2 ∨ (1 : ℕ) = 0)) := by
  click_goal
  click_goal
  click_goal
  · drag_goal h
  · click_goal_left
    drag_rw_lhs_at [h] [1]
    drag_rw_rhs [two_eq_succ_one]
    click_goal

-- Level 3, The Third Mode?: specialize `reflection` to `3 + 3` in Specialization Mode,
-- which is what `hy` asks for.
example (y : ℕ) (hy : (3 : ℕ) + 3 = 3 + 3 → y = 0) : y = 0 := by
  specialize_forall_as thm_h reflection n ((3 : ℕ) + 3)
  drag_to thm_h hy
  drag_goal thm_h

-- Level 4, `succ_inj`: rewrite `h` into `S x = S 3`, then drag it onto `succ_inj`.
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  drag_rw_hyp_rhs h [four_eq_succ_three]
  drag_rw_hyp_lhs h [add_one']
  drag_apply succ_inj h
  drag_goal thm_succ_inj

-- Level 5, Pattern Matching: `succ_inj` dragged onto `S a = S b` specializes itself.
example (x y : ℕ) (h : S (S (S x)) = S (S (S y))) : x = y := by
  drag_apply succ_inj h
  drag_apply succ_inj thm_succ_inj
  drag_apply succ_inj thm_succ_inj1
  drag_goal thm_succ_inj2

-- Level 6: `x ≠ y` applies to `x = y` like an implication.
example : ∀ x y : ℕ, (S x = S y ∧ x ≠ y) → False := by
  click_goal
  click_goal
  click_goal
  click_prop h
  drag_apply succ_inj left
  drag_to thm_succ_inj right
  drag_goal thm_succ_inj

-- Level 7, `one_ne_zero`: swap `S 0 = 0` round in Rewriting Mode for `zero_ne_succ`.
example : (1 : ℕ) ≠ 0 := by
  click_goal
  drag_rw_hyp_lhs h [one_eq_succ_zero]
  symm at h
  drag_apply zero_ne_succ h
  drag_goal thm_zero_ne_succ

-- Level 8: `2 ≠ 3`, peeling off successors with `succ_inj`.
example : (2 : ℕ) ≠ 3 := by
  click_goal
  drag_rw_hyp_lhs h [two_eq_succ_one]
  drag_rw_hyp_rhs h [three_eq_succ_two]
  drag_apply succ_inj h
  drag_rw_hyp_lhs thm_succ_inj [one_eq_succ_zero]
  drag_rw_hyp_rhs thm_succ_inj [two_eq_succ_one]
  drag_apply succ_inj thm_succ_inj
  drag_rw_hyp_rhs thm_succ_inj1 [one_eq_succ_zero]
  drag_apply zero_ne_succ thm_succ_inj1
  drag_goal thm_zero_ne_succ

-- Level 9, Zero or No Zero, the boss: by induction. Splitting `n` names the new
-- number `n1` and the inductive hypothesis `hn1` (`VisualNumberedSplits`).
example : ∀ n : ℕ, n = 0 ∨ n ≠ 0 := by
  click_goal
  induction n with n1 hn1
  · click_goal_left
    click_goal
  · click_goal_right
    click_goal
    specialize_forall_as thm_z zero_ne_succ a n1
    drag_rw_hyp_lhs thm_z [← h]
    specialize_forall_as thm_r reflection n (S n1)
    drag_to thm_r thm_z
    drag_goal thm_z1

/-! ## Induction World, past the ≠ World -/

-- Level 4, `add_right_cancel`: induct on `n`; the step takes `succ_inj`, then the
-- inductive hypothesis.
example : ∀ a b n : ℕ, a + n = b + n → a = b := by
  click_goal
  click_goal
  click_goal
  induction n with n1 hn1
  · click_goal
    drag_rw_hyp_lhs h [add_zero]
    drag_rw_hyp_rhs h [add_zero]
    drag_goal h
  · click_goal
    drag_rw_hyp_lhs h [add_succ]
    drag_rw_hyp_rhs h [add_succ]
    drag_apply succ_inj h
    drag_to thm_succ_inj hn1
    drag_goal thm_succ_inj

-- Level 5, `add_right_eq_self`: induct on `a`.
example : ∀ a b : ℕ, a + b = a → b = 0 := by
  click_goal
  click_goal
  induction a with a1 ha1
  · click_goal
    drag_rw_hyp_lhs h [zero_add]
    drag_goal h
  · click_goal
    drag_rw_hyp_lhs h [succ_add]
    drag_apply succ_inj h
    drag_to thm_succ_inj ha1
    drag_goal thm_succ_inj

-- Level 6, Zero or No Zero?: the same goal with the cases card. The swap button is
-- back past the barrier, so `S n1 = 0` is turned round for `zero_ne_succ`.
example : ∀ n : ℕ, n = 0 ∨ n ≠ 0 := by
  click_goal
  cases n with n1
  · click_goal_left
    click_goal
  · click_goal_right
    click_goal
    symm at h
    drag_apply zero_ne_succ h
    drag_goal thm_zero_ne_succ

-- Level 7, `add_right_eq_zero`: split `b` with the cases card; in the successor case
-- `h : S (a + b1) = 0` turns `0 ≠ S (a + b1)` into `0 ≠ 0`, with no swap.
example : ∀ a b : ℕ, a + b = 0 → a = 0 := by
  click_goal
  click_goal
  cases b with b1
  · click_goal
    drag_rw_hyp_lhs h [add_zero]
    drag_goal h
  · click_goal
    drag_rw_hyp_lhs h [add_succ]
    specialize_forall_as thm zero_ne_succ a (a + b1)
    drag_rw_hyp_rhs thm [h]
    click_prop thm
    drag_goal_exfalso thm

-- Level 7 again, splitting `a`: the successor case's goal `S a1 = 0` can't be true,
-- which is what the level's hint is for. A `False` hypothesis closes it all the same.
example : ∀ a b : ℕ, a + b = 0 → a = 0 := by
  click_goal
  click_goal
  cases a with a1
  · click_goal
    click_goal
  · click_goal
    drag_rw_hyp_lhs h [succ_add]
    symm at h
    drag_apply zero_ne_succ h
    drag_goal_exfalso thm_zero_ne_succ

-- Level 8, Double Induction: induct on `a` while `b` is still under its `∀`, so that
-- the inductive hypothesis holds for every `b`; then fix `b` and induct on it.
example : ∀ a b : ℕ, a + a = b + b → a = b := by
  click_goal
  induction a with a1 ha1
  · click_goal
    induction b with b1 hb1
    · click_goal
      click_goal
    · click_goal
      drag_rw_hyp_lhs h [add_zero]
      drag_rw_hyp_rhs h [add_succ]
      drag_apply zero_ne_succ h
      drag_goal_exfalso thm_zero_ne_succ
  · click_goal
    induction b with b1 hb1
    · click_goal
      drag_rw_hyp_rhs h [add_zero]
      drag_rw_hyp_lhs h [add_succ]
      specialize_forall_as thm zero_ne_succ a (S a1 + a1)
      drag_rw_hyp_rhs thm [h]
      click_prop thm
      drag_goal_exfalso thm
    · click_goal
      drag_rw_hyp_lhs h [add_succ]
      drag_rw_hyp_rhs h [add_succ]
      drag_rw_hyp_lhs_at h [succ_add] [1]
      drag_rw_hyp_rhs_at h [succ_add] [1]
      drag_apply succ_inj h
      drag_apply succ_inj thm_succ_inj
      specialize_forall_as thm_e ha1 b b1
      drag_to thm_succ_inj1 thm_e
      drag_rw_lhs_at [thm_e1] [1]
      click_goal

-- Level 9, the boss: induction on `a`, and inside each case, induction on `b`.
example : ∀ a b : ℕ, a = b ∨ a ≠ b := by
  click_goal
  induction a with a1 ha1
  · click_goal
    induction b with b1 hb1
    · click_goal_left
      click_goal
    · click_goal_right
      drag_goal zero_ne_succ
  · click_goal
    induction b with b1 hb1
    · click_goal_right
      click_goal
      specialize_forall_as thm_z zero_ne_succ a a1
      drag_rw_hyp_lhs thm_z [← h]
      specialize_forall_as thm_r reflection n (S a1)
      drag_to thm_r thm_z
      drag_goal thm_z1
    · specialize_forall_as thm_e ha1 b b1
      click_prop thm_e
      · click_goal_left
        drag_rw_lhs_at [thm_left] [1]
        click_goal
      · click_goal_right
        click_goal
        drag_apply succ_inj h
        drag_to thm_succ_inj thm_right
        drag_goal thm_right1

/-! ## Multiplication and Exponentiation World -/

-- Level 0: `1` is a successor, so the two axioms apply.
example : ∀ m : ℕ, m * 1 = m := by
  click_goal
  drag_rw_lhs_at [one_eq_succ_zero] [2]
  drag_rw_lhs [mul_succ]
  drag_rw_lhs_at [mul_zero] [1]
  drag_rw_lhs [zero_add]
  click_goal

-- Level 7, the miniboss: induction on `c`.
example : ∀ a b c : ℕ, (a * b) * c = a * (b * c) := by
  click_goal
  click_goal
  click_goal
  induction c with c1 hc1
  · drag_rw_lhs [mul_zero]
    drag_rw_rhs_at [mul_zero] [2]
    drag_rw_rhs [mul_zero]
    click_goal
  · drag_rw_lhs [mul_succ]
    drag_rw_rhs_at [mul_succ] [2]
    drag_rw_rhs [mul_add]
    drag_rw_lhs_at [hc1] [1]
    click_goal

-- Level 12: `2` is `S 1`, then the axiom and `pow_one`.
example : ∀ a : ℕ, a ^ 2 = a * a := by
  click_goal
  drag_rw_lhs_at [two_eq_succ_one] [2]
  drag_rw_lhs [pow_succ]
  drag_rw_lhs_at [pow_one] [1]
  click_goal

-- Bonus A1, Refute Fermat's Last Theorem?: without positive numbers the statement fails
-- at `0 ^ 3 + 0 ^ 3 = 0 ^ 3`. Specialized there it proves `False` backwards, leaving
-- `3 > 2`, which is `¬ 3 ≤ 2` and introduces like any `¬`, and the equation.
example : (∀ a b c n : ℕ, n > 2 → a ^ n + b ^ n ≠ c ^ n) → False := by
  click_goal
  specialize_forall_as thm_a h a (0)
  specialize_forall_as thm_b thm_a b (0)
  specialize_forall_as thm_c thm_b c (0)
  specialize_forall_as thm_n thm_c n (3)
  drag_goal thm_n
  · click_goal
    click_prop h1
    drag_rw_hyp_rhs_at h2 [three_eq_succ_two] [1]
    drag_rw_hyp_rhs h2 [succ_add]
    drag_rw_hyp_lhs h2 [two_eq_succ_one]
    drag_apply succ_inj h2
    drag_rw_hyp_rhs_at thm_succ_inj [two_eq_succ_one] [1]
    drag_rw_hyp_rhs thm_succ_inj [succ_add]
    drag_rw_hyp_lhs thm_succ_inj [one_eq_succ_zero]
    drag_apply succ_inj thm_succ_inj
    drag_rw_hyp_rhs_at thm_succ_inj1 [one_eq_succ_zero] [1]
    drag_rw_hyp_rhs thm_succ_inj1 [succ_add]
    drag_apply zero_ne_succ thm_succ_inj1
    drag_goal thm_zero_ne_succ
  · drag_rw_lhs_at [three_eq_succ_two] [1, 2]
    drag_rw_lhs_at [zero_pow_succ] [1]
    drag_rw_lhs_at [three_eq_succ_two] [2, 2]
    drag_rw_lhs_at [zero_pow_succ] [2]
    drag_rw_lhs [add_zero]
    drag_rw_rhs_at [three_eq_succ_two] [2]
    drag_rw_rhs [zero_pow_succ]
    click_goal

/-! ## ≤ World -/

-- Level 0: build the `0` in the construction view, then rewrite.
example : ∃ n : ℕ, n + n = 0 := by
  refine Exists.intro (0) ?_
  drag_rw_lhs [add_zero]
  click_goal

-- Level 1: `n ≤ n` is `∃ c, n = n + c`, and `0` is the number.
example : ∀ n : ℕ, n ≤ n := by
  click_goal
  refine Exists.intro (0) ?_
  drag_rw_rhs [add_zero]
  click_goal

-- Level 4: clicking a `≤` hypothesis names its number, `c1`, and its equation.
example (a b : ℕ) (h : a ≤ b) : a ≤ S b := by
  click_prop h
  refine Exists.intro (S c1) ?_
  drag_rw_rhs [add_succ]
  drag_rw_lhs_at [h1] [1]
  click_goal

-- Level 5: the numbers of two `≤` hypotheses are `c1` and `c2`, never plain `c`.
example (a b c : ℕ) (hxy : a ≤ b) (hyz : b ≤ c) : a ≤ c := by
  click_prop hxy
  click_prop hyz
  refine Exists.intro (c1 + c2) ?_
  drag_rw_lhs [h1]
  drag_rw_lhs_at [h] [1]
  drag_rw_rhs [← add_assoc]
  click_goal

-- Level 6: Induction World's `add_right_eq_zero`, once the equation is turned round.
example (n : ℕ) (hn : n ≤ 0) : n = 0 := by
  click_prop hn
  symm at h
  drag_apply add_right_eq_zero h
  drag_goal thm_add_right_eq_zero

-- Level 7, `≤` Add Right Cancel: move `n` to the end of the sum and cancel it.
example : ∀ a b n : ℕ, a + n ≤ b + n → a ≤ b := by
  click_goal
  click_goal
  click_goal
  click_goal
  click_prop h
  refine Exists.intro (c1) ?_
  drag_rw_hyp_rhs h1 [add_assoc]
  drag_rw_hyp_rhs_at h1 [add_comm] [2]
  drag_rw_hyp_rhs h1 [← add_assoc]
  drag_apply add_right_cancel h1
  drag_goal thm_add_right_cancel

-- A hypothesis that shows its `∃` still gives the bound variable's own name first.
example (x : ℕ) (h : ∃ c, x + c = 0) : x = 0 := by
  click_prop h
  drag_rw_hyp_lhs h1 [add_comm]
  exact add_left_eq_zero c x h1

/-! ## ≤ World's bonus levels: `>` -/

-- A0, `S n > n`: `>` is `¬ (… ≤ …)`, so a click assumes `S n ≤ n`, and that gives a
-- number like any `≤`. The equation turns into `n + S c1 = n`, which no sum allows.
example : ∀ n : ℕ, S n > n := by
  click_goal
  click_goal
  click_prop h
  drag_rw_hyp_rhs h1 [succ_add]
  drag_rw_hyp_rhs h1 [← add_succ]
  symm at h1
  drag_apply add_right_eq_self h1
  symm at thm_add_right_eq_self
  drag_apply zero_ne_succ thm_add_right_eq_self
  drag_goal thm_zero_ne_succ

-- A1, irreflexivity: `n ≤ n` dropped on `n > n` proves `False`.
example : ∀ n : ℕ, ¬ (n > n) := by
  click_goal
  click_goal
  specialize_forall_as thm_r leq_refl n n
  drag_to thm_r h
  drag_goal thm_r

-- A2, transitivity: assume `a ≤ c` and compare `b` and `c` with `le_total`. `leq_trans`
-- is specialized by hand: dropped on a card it would leave its last number open.
example : ∀ a b c : ℕ, a > b → b > c → a > c := by
  click_goal
  click_goal
  click_goal
  click_goal
  click_goal
  click_goal
  specialize_forall_as thm_t le_total a b
  specialize_forall_as thm_t1 thm_t b c
  click_prop thm_t1
  · drag_to thm_left h1
    drag_goal thm_left
  · specialize_forall_as thm_x leq_trans a a
    specialize_forall_as thm_y thm_x b c
    specialize_forall_as thm_z thm_y c b
    drag_to h2 thm_z
    drag_to thm_right thm_z
    drag_to thm_z1 h
    drag_goal thm_z1

/-! ## Advanced Multiplication World -/

-- Level 0: `h` gives `b = a + c1`, and `c1 * t` is the number for the goal.
example (a b : ℕ) (h : a ≤ b) : ∀ t : ℕ, a * t ≤ b * t := by
  click_goal
  click_prop h
  refine Exists.intro (c1 * t) ?_
  drag_rw_lhs_at [h1] [1]
  drag_rw_lhs [add_mul]
  click_goal

-- Level 2: no `cases` in this world; `peano_cases a` gives the two forms of `a`. In the
-- zero case `a = 0` dropped on `ha` proves `False`.
example (a : ℕ) (ha : a ≠ 0) : ∃ n, a = S n := by
  specialize_forall_as thm_p peano_cases a a
  click_prop thm_p
  · drag_to thm_left ha
    drag_goal_exfalso thm_left
  · drag_goal thm_right

end MyNat
