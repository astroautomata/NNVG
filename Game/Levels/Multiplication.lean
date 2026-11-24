import Game.Levels.Multiplication.L01_MulOne
import Game.Levels.Multiplication.L02_ZeroMul
import Game.Levels.Multiplication.L03_SuccMul
import Game.Levels.Multiplication.L04_MulComm
import Game.Levels.Multiplication.L05_OneMul
import Game.Levels.Multiplication.L06_TwoMul
import Game.Levels.Multiplication.L07_MulAdd
import Game.Levels.Multiplication.L08_MulAssoc

World "Multiplication"
Title "Multiplication and Exponentiation World"

-- Levels 0 to 7, the ones about multiplication. The levels about powers are a Lean
-- world of their own (`Power`), because Advanced Multiplication World leaves from
-- level 7.
VisualWorldColor sandstone
VisualMapColumn -2

-- Rewrite Mode's swap-sides button is hidden throughout this world.
VisualHideSwapSides

-- One induction per branch of a proof, in every level.
VisualTacticUses induction 1

Introduction
"
How should we define `37 * x`? Just like addition, we need to give definitions
when $x=0$ and when $x$ is a successor.

The zero case is easy: we define `37 * 0` to be `0`. Now say we know
`37 * d`. What should `37 * S d` be? Well, that's $(d+1)$ $37$s,
so it should be `37 * d + 37`.

Here are the definitions in Lean.

  * `mul_zero m : m * 0 = 0`
  * `mul_succ a b : a * S b = a * b + a`

In this world, we must not only prove facts about multiplication like `a * b = b * a`,
we must also prove facts about how multiplication interacts with addition, like `a * (b + c) = a * b + a * c`.
Then come powers. Let's get started.
"
