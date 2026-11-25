# Theorems

Written by `tools/list_theorems.py` from the built game. A number in a statement
is any number: a theorem is about all of them. “after” a level: proved there, and
yours once it is done. “from” a level: handed out there.

## Rewrite Mode (33 rules)

### Tab `+`

| Theorem | Statement | Yours |
|---|---|---|
| `add_one` | `a + 1 = S(a)` | after Successor World 1 |
| `add_succ` (axiom) | `a + S(b) = S(a + b)` | from Successor World 1 |
| `add_zero` (axiom) | `n + 0 = n` | from Successor World 1 |
| `zero_add` | `0 + n = n` | after Induction World 0 |
| `succ_add` | `S(a) + b = S(a + b)` | after Induction World 1 |
| `add_comm` | `a + b = b + a` | after Induction World 2 |
| `add_assoc` | `a + b + c = a + (b + c)` | after Induction World 3 |

### Tab `*`

| Theorem | Statement | Yours |
|---|---|---|
| `mul_one` | `m * 1 = m` | after Multiplication and Exponentiation World 0 |
| `mul_succ` (axiom) | `a * S(b) = a * b + a` | from Multiplication and Exponentiation World 0 |
| `mul_zero` (axiom) | `m * 0 = 0` | from Multiplication and Exponentiation World 0 |
| `zero_mul` | `0 * m = 0` | after Multiplication and Exponentiation World 1 |
| `succ_mul` | `S(a) * b = a * b + b` | after Multiplication and Exponentiation World 2 |
| `mul_comm` | `a * b = b * a` | after Multiplication and Exponentiation World 3 |
| `one_mul` | `1 * m = m` | after Multiplication and Exponentiation World 4 |
| `two_mul` | `2 * m = m + m` | after Multiplication and Exponentiation World 5 |
| `mul_add` | `a * (b + c) = a * b + a * c` | after Multiplication and Exponentiation World 6 |
| `add_mul` | `(a + b) * c = a * c + b * c` | from Multiplication and Exponentiation World 7 |
| `mul_assoc` | `a * b * c = a * (b * c)` | after Multiplication and Exponentiation World 7 |

### Tab `^`

| Theorem | Statement | Yours |
|---|---|---|
| `pow_zero` (axiom) | `a ^ 0 = 1` | from Multiplication and Exponentiation World 8 |
| `zero_pow_zero` | `0 ^ 0 = 1` | after Multiplication and Exponentiation World 8 |
| `pow_succ` (axiom) | `a ^ S(b) = a ^ b * a` | from Multiplication and Exponentiation World 9 |
| `zero_pow_succ` | `0 ^ S(m) = 0` | after Multiplication and Exponentiation World 9 |
| `pow_one` | `a ^ 1 = a` | after Multiplication and Exponentiation World 10 |
| `one_pow` | `1 ^ m = 1` | after Multiplication and Exponentiation World 11 |
| `pow_two` | `a ^ 2 = a * a` | after Multiplication and Exponentiation World 12 |
| `pow_add` | `a ^ (m + n) = a ^ m * a ^ n` | after Multiplication and Exponentiation World 13 |
| `mul_pow` | `(a * b) ^ n = a ^ n * b ^ n` | after Multiplication and Exponentiation World 14 |
| `pow_pow` | `(a ^ m) ^ n = a ^ (m * n)` | after Multiplication and Exponentiation World 15 |
| `add_sq` | `(a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b` | after Multiplication and Exponentiation World 16 |

### Tab `012`

| Theorem | Statement | Yours |
|---|---|---|
| `four_eq_succ_three` (axiom) | `4 = S(3)` | from Successor World 0 |
| `one_eq_succ_zero` (axiom) | `1 = S(0)` | from Successor World 0 |
| `three_eq_succ_two` (axiom) | `3 = S(2)` | from Successor World 0 |
| `two_eq_succ_one` (axiom) | `2 = S(1)` | from Successor World 0 |

## Proposition Mode (34 cards)

### Tab `Peano`

| Theorem | Statement | Yours |
|---|---|---|
| `reflection` (axiom) | `n = n` | from ≠ World 3 |
| `peano_cases` (axiom) | `a = 0 ∨ ∃ b, a = S(b)` | from Advanced Multiplication World 1 |

### Tab `+`

| Theorem | Statement | Yours |
|---|---|---|
| `succ_inj` (axiom) | `S(a) = S(b) → a = b` | from ≠ World 4 |
| `add_right_cancel` | `a + n = b + n → a = b` | after Induction World 4 |
| `add_left_cancel` | `n + a = n + b → a = b` | from Induction World 5 |
| `add_right_eq_self` | `a + b = a → b = 0` | after Induction World 5 |
| `add_left_eq_self` | `a + b = b → a = 0` | from Induction World 6 |
| `add_right_eq_zero` | `a + b = 0 → a = 0` | after Induction World 7 |
| `add_left_eq_zero` | `a + b = 0 → b = 0` | from ≤ World 1 |

### Tab `≠`

| Theorem | Statement | Yours |
|---|---|---|
| `one_ne_zero` | `1 ≠ 0` | after ≠ World 7 |
| `zero_ne_succ` (axiom) | `0 ≠ S(a)` | from ≠ World 7 |
| `zero_ne_one` | `0 ≠ 1` | from ≠ World 8 |

### Tab `≤`

| Theorem | Statement | Yours |
|---|---|---|
| `leq_refl` | `n ≤ n` | after ≤ World 1 |
| `eq_implies_leq` | `a = b → a ≤ b` | from ≤ World 2 |
| `zero_leq` | `0 ≤ n` | after ≤ World 2 |
| `le_succ_self` | `n ≤ S(n)` | after ≤ World 3 |
| `leq_trans` | `a ≤ b → b ≤ c → a ≤ c` | after ≤ World 5 |
| `leq_zero` | `n ≤ 0 → n = 0` | after ≤ World 6 |
| `leq_add_right_cancel` | `a + n ≤ b + n → a ≤ b` | after ≤ World 7 |
| `leq_antisymm` | `a ≤ b → b ≤ a → a = b` | after ≤ World 8 |
| `leq_one` | `n ≤ 1 → n = 0 ∨ n = 1` | after ≤ World 9 |
| `le_total` | `a ≤ b ∨ b ≤ a` | after ≤ World 10 |
| `eq_succ_of_ne_zero` | `a ≠ 0 → ∃ n, a = S(n)` | after Advanced Multiplication World 2 |
| `one_le_of_ne_zero` | `a ≠ 0 → 1 ≤ a` | after Advanced Multiplication World 3 |
| `lt_succ_self` | `S(n) > n` | after ≤ World Bonus A0 |

### Tab `*`

| Theorem | Statement | Yours |
|---|---|---|
| `mul_le_mul_right` | `a ≤ b → a * t ≤ b * t` | after Advanced Multiplication World 0 |
| `mul_left_ne_zero` | `a * b ≠ 0 → b ≠ 0` | after Advanced Multiplication World 1 |
| `le_mul_right` | `a * b ≠ 0 → a ≤ a * b` | after Advanced Multiplication World 4 |
| `mul_right_eq_one` | `x * y = 1 → x = 1` | after Advanced Multiplication World 5 |
| `mul_ne_zero` | `a ≠ 0 → b ≠ 0 → a * b ≠ 0` | after Advanced Multiplication World 6 |
| `mul_eq_zero` | `a * b = 0 → a = 0 ∨ b = 0` | after Advanced Multiplication World 7 |
| `mul_right_eq_self` | `a ≠ 0 → a * b = a → b = 1` | after Advanced Multiplication World 8 |
| `mul_left_cancel` | `a ≠ 0 → a * b = a * c → b = c` | after Advanced Multiplication World 9 |

### Under `All` only

| Theorem | Statement | Yours |
|---|---|---|
| `lem_iff_double_elimination` | `(∀ (P : Prop), P ∨ ¬P) ↔ ∀ (P : Prop), ¬¬P → P` | after Logic World A0 |
