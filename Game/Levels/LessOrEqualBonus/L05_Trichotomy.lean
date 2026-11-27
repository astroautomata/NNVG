import Game.Levels.LessOrEqualBonus.L04_LeqLe

World "LessOrEqualBonus"
Level 5

Title "Trichotomy"

VisualLevelNumber "A4"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock trichotomy "Trichotomy just means ‘three cases’."

namespace MyNat

Introduction
"
Two numbers are equal, or one of them is greater than the other.
"

/-- `trichotomy a b` is a proof that `a = b`, `a > b` or `b > a`. -/
TheoremDoc MyNat.trichotomy as "trichotomy" in ">"

-- `leq_total` compares the two numbers, and `leq_le` says what either answer means.
Statement trichotomy : ∀ a b : ℕ, a = b ∨ (a > b ∨ b > a) := by
  exact fun a b => (leq_total a b).elim
    (fun hab => (leq_le a b hab).elim (fun h => .inl h) (fun h => .inr (.inr h)))
    (fun hba => (leq_le b a hba).elim (fun h => .inl h.symm) (fun h => .inr (.inl h)))
