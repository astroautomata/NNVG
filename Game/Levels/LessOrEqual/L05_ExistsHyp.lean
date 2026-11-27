import Game.Levels.LessOrEqual.L04_LeRightAddSelf

World "LessOrEqual"
Level 5

Title "`∃` Hypotheses"

VisualLevelNumber "4"

-- With an arrow to `h`, for as long as it is still a `≤`.
VisualHypInfoOnHyp h "a ≤ b" show "You can {pc: click | mobile: tap} a `∃` (there-exists) hypothesis to create a witness."

namespace MyNat

Introduction
"
In this level, we see an inequality as a *hypothesis*. {pc: Click | mobile: Tap} `h` to
take it apart into a number and its equation.
"

Statement (a b : ℕ) (h : a ≤ b) : a ≤ S b := by
  rw [← add_one]
  exact (h : ∃ c, b = a + c).elim (fun c hc => (⟨c + 1, by rw [hc, add_assoc]⟩ : ∃ c', b + 1 = a + c'))
