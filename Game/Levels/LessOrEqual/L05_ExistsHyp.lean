import Game.Levels.LessOrEqual.L04_LeSuccSelf

World "LessOrEqual"
Level 5

Title "`∃` Hypotheses"

VisualLevelNumber "4"

-- With an arrow to `h`, for as long as it is still a `≤`.
VisualHypInfoOnHyp h "x ≤ y" show "You can {pc: click | mobile: tap} a `∃` (there-exists) hypothesis to create a witness."

namespace MyNat

Introduction
"
In this level, we see an inequality as a *hypothesis*. {pc: Click | mobile: Tap} `h` to
take it apart into a number and its equation.
"

Statement (x y : ℕ) (h : x ≤ y) : x ≤ S y := by
  rw [← add_one_eq_succ]
  exact (h : ∃ c, y = x + c).elim (fun c hc => (⟨c + 1, by rw [hc, add_assoc]⟩ : ∃ c', y + 1 = x + c'))
