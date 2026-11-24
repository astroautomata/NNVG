import Game.Levels.InductionJoined.L02_AddRightEqSelf

World "InductionJoined"
Level 3

Title "Zero or No Zero?"

VisualLevelNumber "6"

-- The ≠ World's boss again, this time with the new card, and with that card alone.
VisualTacticUses cases 1

VisualGoalInfo above false "`cases` is like `induction`’s weaker cousin.
(Some day we’ll meet `induction`’s stronger cousin too!)
`cases` is more general, but it does not give you an inductive hypothesis."

namespace MyNat

Introduction
"
## A new tactic: `cases`

The `cases` tactic will split an object or hypothesis up into the possible ways
that it could have been created.

For example, sometimes you want to deal with the two cases `n = 0` and `n = S n1` separately,
but don't need the inductive hypothesis that comes with induction on `n`.
In this situation you can drag `cases` onto `n` instead. There are two ways to make
a number: it's either zero or a successor. So you will end up with two goals, one
with `n = 0` and one with `n = S n1`.
"

/--
## Summary

If `n` is a number, then dragging `cases` onto `n` will break the goal into two goals,
one with `n = 0` and the other with `n = S n1`.

If `h` is a proof (for example a hypothesis), then dragging `cases` onto `h` will break
the proof up into the pieces used to prove it.

## Example

If `n : ℕ` is a number, then dragging `cases` onto `n` will break the goal into two goals,
one with `n` replaced by 0 and the other with `n` replaced by `S n1`. This
corresponds to the mathematical idea that every natural number is either `0`
or a successor.

## Example

If `h : a ≤ b` is a hypothesis, then dragging `cases` onto `h` will create a new number `c1`
and a proof `h : b = a + c1`. This is because the *definition* of `a ≤ b` is
`∃ c, b = a + c`.
-/
TacticDoc cases

NewTactic cases

-- Unlocked by completing `add_right_eq_self` (the level before).
NewTheorem MyNat.add_left_eq_self

Statement : ∀ n : ℕ, n = 0 ∨ n ≠ 0 := by
  exact fun n => by
    cases n with d
    · exact .inl (reflection 0)
    · exact .inr (fun h => zero_ne_succ d h.symm)
