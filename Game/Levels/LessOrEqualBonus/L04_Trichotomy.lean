import Game.Levels.LessOrEqualBonus.L03_GtTrans

World "LessOrEqualBonus"
Level 4

Title "Trichotomy"

VisualLevelNumber "A3"

namespace MyNat

Introduction
"
Two numbers are equal, or one of them is greater than the other.
"

-- With no `cases` here, `le_total` compares the two numbers and `le_one` says whether
-- the difference is `0`.
Statement : ∀ a b : ℕ, a = b ∨ (a > b ∨ b > a) := by
  exact fun a b =>
    (fun (key : ∀ x y d : ℕ, y = x + (1 + d) → ¬ y ≤ x) => (le_total a b).elim
      (fun hab => (hab : ∃ c, b = a + c).elim (fun c hc => (le_total 1 c).elim
        (fun h1c => (h1c : ∃ d, c = 1 + d).elim (fun d hd => .inr (.inr (key a b d (by rw [hc, hd])))))
        (fun hc1 => (le_one c hc1).elim
          (fun h0 => .inl (by rw [hc, h0, add_zero]))
          (fun h1 => .inr (.inr (key a b 0 (by rw [hc, h1, add_zero])))))))
      (fun hba => (hba : ∃ c, a = b + c).elim (fun c hc => (le_total 1 c).elim
        (fun h1c => (h1c : ∃ d, c = 1 + d).elim (fun d hd => .inr (.inl (key b a d (by rw [hc, hd])))))
        (fun hc1 => (le_one c hc1).elim
          (fun h0 => .inl (by rw [hc, h0, add_zero]))
          (fun h1 => .inr (.inl (key b a 0 (by rw [hc, h1, add_zero]))))))))
    (fun x y d hy hle => (hle : ∃ e, x = y + e).elim (fun e he =>
      one_ne_zero (add_right_eq_zero 1 d (add_right_eq_zero (1 + d) e
        (add_right_eq_self x (1 + d + e) (by rw [← add_assoc, ← hy]; exact he.symm))))))
