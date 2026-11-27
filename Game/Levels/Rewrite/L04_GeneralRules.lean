import Game.Metadata

World "Rewrite"
Level 4

Title "General Rewriting (Commutativity)"

VisualLevelNumber "3"

-- Experimental (V13.2): the screen before the level.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "∀" "For All" "`∀ n : ℕ, …` just means that for any natural number `n` you pick, the subsequent condition involving `n` is always true. We can use this to express equalities that work for any natural numbers!"
VisualRewriteOnly
VisualEmphasizeForall add_comm

Statement (a b c : ℕ) (hx : a = 1) (hy : b = 2) (hz : c = 3)
    (add_comm : ∀ x y : ℕ, x + y = y + x) : (a + b) + c = 3 + (2 + 1) := by
  rw [hx, hy, hz, add_comm (1 + 2) 3, add_comm 1 2]

VisualTransformText "Some hypotheses are more general than others.
Here, `add_comm` can swap any pair of numbers, not just the particular `x` and `y` it's stated with!"
