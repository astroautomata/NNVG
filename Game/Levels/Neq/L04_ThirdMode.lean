import Game.Levels.Neq.L03_EqualitiesArePropositions3

World "Neq"
Level 4

Title "The Third Mode?"

VisualLevelNumber "3"

namespace MyNat

/-- `reflection n` is a proof of `n = n`: every natural number is equal to itself. -/
TheoremDoc MyNat.reflection as "reflection" in "Peano"

NewTheorem MyNat.reflection

Statement (y : ℕ) (hy : (3 : ℕ) + 3 = 3 + 3 → y = 0) : y = 0 := by
  exact hy (reflection _)

-- Specializing `reflection` by hand, in Specialization Mode, to what `hy` asks for.
VisualTheoremInfoOnGoalWithoutHyp MyNat.reflection "y = 0" "3 + 3 = 3 + 3" show
  "We've unlocked a new proposition we can use in any level.
{pc: Click | mobile: Tap} `reflection` to specialize it to match the goal."

VisualSpecializeBrickInfo "_ + _" "?" onGoal "y = 0" show
  "We've now entered Specialization Mode.
Our goal is `3 + 3 = 3 + 3`, so let's drag `_ + _` into the workspace."

VisualSpecializeInfo "? + ?" onGoal "y = 0" show
  "Now we can slot in the `3` terms!"

VisualSpecializeInfo "3 + ?" onGoal "y = 0" show
  "Now we can slot in the `3` terms!"

VisualSpecializeDoneInfo "3 + 3" onGoal "y = 0" show
  "Finally, we can {pc: click | mobile: tap} ‘Done’ to return to Proposition Mode."

-- Back on the canvas with `3 + 3 = 3 + 3`: the opening hint is cleared.
VisualGoalInfoOnGoalWithHyp above false "y = 0" "3 + 3 = 3 + 3" show ""
