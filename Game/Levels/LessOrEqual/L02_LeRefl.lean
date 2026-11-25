import Game.Levels.LessOrEqual.L01_Exists

World "LessOrEqual"
Level 2

Title "`le_refl`"

VisualLevelNumber "1"

VisualGoalInfo below false "We define `x ≤ y` to mean `∃ c, y = x + c`."

namespace MyNat

Introduction
"
`a ≤ b` is *notation* for `∃ c, b = a + c`. This \"backwards E\"
means \"there exists\". So `a ≤ b` means that there exists
a number `c` such that `b = a + c`. This definition works
because there are no negative numbers in this game.
"

/--
`a ≤ b` is *notation* for `∃ c, b = a + c`.

Because this game doesn't have negative numbers, this definition
is mathematically valid.

This means that if you have a goal of the form `a ≤ b` you can
make progress by {pc: clicking | mobile: tapping} it and building the number `c`, and if
you have a hypothesis `h : a ≤ b`, you can make progress by {pc: clicking | mobile: tapping}
it to get a number `c1` and the proof that `b = a + c1`.
-/
DefinitionDoc LE as "≤"

NewDefinition LE

/--  A proof that $a+b=0 \implies b=0$. -/
TheoremDoc MyNat.add_left_eq_zero as "add_left_eq_zero" in "+"

-- Given from here on. It is the mirror image of Induction World's `add_right_eq_zero`,
-- which this part of ≤ World doesn't wait for, so it is proved here from scratch.
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  induction b with d _hd
  · exact fun _ => rfl
  · exact fun h => (zero_ne_succ (a + d) (by rw [add_succ] at h; exact h.symm)).elim

NewTheorem MyNat.add_left_eq_zero

/--
`leq_refl n` is a proof of `n ≤ n`.

The reason for the name is that this lemma is "reflexivity of $\le$"
-/
TheoremDoc MyNat.leq_refl as "leq_refl" in "≤"

Statement leq_refl : ∀ n : ℕ, n ≤ n := by
  exact fun n => (⟨0, by rw [add_zero]⟩ : ∃ c, n = n + c)

/-- `eq_implies_leq a b` is a proof that if `a = b` then `a ≤ b`. -/
TheoremDoc MyNat.eq_implies_leq as "eq_implies_leq" in "≤"

-- Unlocked by finishing this level, with no level of its own (`NewTheorem` in the next).
theorem eq_implies_leq (a b : ℕ) : a = b → a ≤ b := by
  exact fun h => by rw [h]; exact leq_refl b

Conclusion
"
Equal numbers are a special case: if `a = b` then `a ≤ b`. That is `eq_implies_leq`,
and you have it from now on.
"
