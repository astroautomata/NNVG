import Game.Levels.LessOrEqual.L06_LeTrans

World "LessOrEqual"
Level 7

Title "Eliminating Addition is Decreasing"

VisualLevelNumber "6"

VisualTacticUses induction 1

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock right_add_leq "Getting rid of additions can only make them smaller."

namespace MyNat

Introduction
"
If `a + n` is at most `b`, then so is `a` alone. {pc: Click | mobile: Tap} the goal to
assume `a + n ≤ b`, and take that apart.
"

/-- `right_add_leq a b n` is a proof that if `a + n ≤ b` then `a ≤ b`. -/
TheoremDoc MyNat.right_add_leq as "right_add_leq" in "≤"

Statement right_add_leq : ∀ a b n : ℕ, a + n ≤ b → a ≤ b := by
  exact fun a b n h => (h : ∃ c, b = a + n + c).elim (fun c hc =>
    (⟨n + c, by rw [← add_assoc]; exact hc⟩ : ∃ d, b = a + d))
