import Game.Levels.NeqJoined

World "LessOrEqual"
Level 1

Title "`∃`"

VisualLevelNumber "0"

-- Experimental (V13.2): the screen before the level.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "∃" "There Exists" "When we say `∃ n : ℕ, P(n)`, we just mean that we can pick some natural number `n` for which the condition `P(n)` is true. We call the specific `n` that works the *witness*."

-- The witness is built in Construction Mode. `0` is the one that works, and the hint
-- for it stays up while the goal is rewritten; with any other, no hint here matches the
-- goal, which is when the last one shows.
VisualGoalInfoOnGoal above false "∃ n, n + n = 0" show
  "To prove a `∃` (there-exists) goal, we must propose some ‘witness’ which allows the expression to be fulfilled.
{pc: Click | mobile: Tap} `∃` goals to propose a witness in Construction Mode!"
VisualGoalInfoOnGoal above false "0 + 0 = 0" show "Now we can just finish the level as usual."
VisualGoalInfoOnGoal above false "0 = 0" show "Now we can just finish the level as usual."
VisualGoalInfoOtherwise above false
  "We won’t be able to solve the goal with that witness.
Use the undo button in the lower left."

namespace MyNat

Introduction
"
`∃ n, n + n = 0` says that there exists a number `n` with `n + n = 0`.

To *prove* an \"exists\" statement, {pc: click | mobile: tap} the goal and build the
number that works.
"

Statement : ∃ n : ℕ, n + n = 0 := by
  exact (⟨0, by rw [add_zero]⟩ : ∃ n : ℕ, n + n = 0)
