import Game.Levels.Intro
import Game.Levels.Rewrite
import Game.Levels.RewriteBonus
import Game.Levels.RewriteBonusB
import Game.Levels.Proposition
import Game.Levels.PropositionRight
import Game.Levels.PropositionBonus
import Game.Levels.PropositionBonusB
import Game.Levels.PropositionBonusC
import Game.Levels.Successor
import Game.Levels.SuccessorJoined
import Game.Levels.Induction
import Game.Levels.Neq
import Game.Levels.NeqJoined
import Game.Levels.InductionJoined
import Game.Levels.InductionDouble
import Game.Levels.Multiplication
import Game.Levels.Power
import Game.Levels.PowerBonusA
import Game.Levels.PowerBonus
import Game.Levels.LessOrEqual
import Game.Levels.LessOrEqualJoined
import Game.Levels.LessOrEqualBoss
import Game.Levels.LessOrEqualBonus
import Game.Levels.AdvMultiplication
import Game.Levels.Logic
import Game.Levels.Outro

Title "Natural Numbers Video Game"

Introduction
"
Welcome to the Natural Numbers Video Game! It is played in Visual Lean: you build
proofs by dragging and clicking, and a Lean server checks every move.
"

Info "
The Natural Numbers Video Game is a version of the Natural Number Game made for
Visual Lean's drag-and-drop interface.
"

Languages "English"
CaptionShort "Prove things about the natural numbers by dragging and clicking."
CaptionLong "A Natural Number Game built for Visual Lean. Start with substitutions and
propositions, then go wherever the map leads."

-- After the welcome text, the map splits: Rewrite World on the left and
-- Proposition World on the right. Either can be played first.
Dependency Intro → Rewrite
Dependency Intro → Proposition

-- Rewrite World leads to Successor World.
Dependency Rewrite → Successor

-- Proposition World forks: its left branch joins the middle of Successor World, which
-- can't continue until both are finished, and its right branch carries on alone.
Dependency Successor → SuccessorJoined
Dependency Proposition → SuccessorJoined
Dependency Proposition → PropositionRight

-- Successor World leads to Induction World, and with all of Proposition World to the
-- ≠ World, whose boss also waits for Induction World's levels 0 to 3.
Dependency SuccessorJoined → Induction
Dependency SuccessorJoined → Neq
Dependency PropositionRight → Neq
Dependency Neq → NeqJoined
Dependency Induction → NeqJoined

-- Induction World carries on once the ≠ World is finished (levels 4 to 7, then 8 and 9).
Dependency Induction → InductionJoined
Dependency NeqJoined → InductionJoined
Dependency InductionJoined → InductionDouble

-- Multiplication and Exponentiation World hangs off Induction World's level 3, on the
-- far left: levels 0 to 6 (`Multiplication`), then the ones about powers (`Power`, 7
-- to 15).
Dependency Induction → Multiplication
Dependency Multiplication → Power

-- ≤ World follows the ≠ World on the right. Its level 7 waits for all of Induction
-- World. Advanced Multiplication World
-- carries on below it and also needs Multiplication and Exponentiation World's level
-- 6, whose path comes across from the far left. (MakeGame drops any edge a path
-- already implies.)
Dependency NeqJoined → LessOrEqual
Dependency LessOrEqual → LessOrEqualJoined
Dependency InductionDouble → LessOrEqualJoined
Dependency LessOrEqualJoined → LessOrEqualBoss
Dependency LessOrEqualBoss → AdvMultiplication
Dependency Multiplication → AdvMultiplication

-- Bonus B off Multiplication and Exponentiation World's last level refutes a careless
-- Fermat's Last Theorem, stated with `>`, so it waits for ≤ World's bonus levels about
-- `>` too. (Bonus A, off level 14, ends at `0 = 1`, so its proofs use the ≠ World's
-- `zero_ne_one` and `one_ne_zero`, and MakeGame adds that edge itself.)
Dependency LessOrEqualBonus → PowerBonus

-- Bonus A waits for all of the ≠ World, its boss included (the spec says so; its proofs
-- only need `zero_ne_one` and `one_ne_zero`).
Dependency NeqJoined → PowerBonusA

-- Logic World needs both of Proposition World's last bonus branches and the ≠ World.
Dependency PropositionBonusB → Logic
Dependency PropositionBonusC → Logic
Dependency NeqJoined → Logic

-- The End, the closing text at the bottom of the map, follows the final bosses of
-- Multiplication and Exponentiation World and Advanced Multiplication World.
Dependency Power → Outro
Dependency AdvMultiplication → Outro

VisualPathMap

-- One look, with no light mode: a page and a few colours for each world
-- (`VisualWorldColor` in the world files, after the spec's reference images). The map
-- and the worlds without one are a blackboard's slate.
VisualNeutralPalette

-- Variables like `n : ℕ` and `A : Prop` sit in a column of their own.
VisualTypeColumn

-- The lower menus have no tab that lists everything ("All", "Everything").
VisualNoAllTab

-- In this game, a proof of `False` closes any goal, with no `exfalso` step.
VisualFastExfalso

-- Hints stay up as the proof moves on, until the next one replaces them.
VisualPersistentHints

-- The numbers that `≤` hypotheses give are named `c1`, `c2`, …, never plain `c`
-- (`VisualNumberedWitnesses` in `Game/Metadata.lean`, which every level imports).

-- Rewrite Mode on a goal shows the check mark once both sides match, in every level.
VisualRewriteCheck

-- The successor function is `S`, also in the specialization view's term builder.
VisualSuccessorName S

-- `cases` and `induction` are only for the levels that say so, as often as they say:
-- `VisualTacticUses` in a world or level file gives that count, and everywhere else
-- the cards show `x0`.
VisualTacticUses induction 0
VisualTacticUses cases 0

-- Splitting `a` with `cases` or `induction` names the new number `a1`, so the
-- successor case reads `S(a1)`; splitting `a1` gives `a2`.
VisualNumberedSplits

-- The inventory's tabs are NNG4's. The axioms sit among the theorems of their tab, in
-- their own colour.
VisualAxioms MyNat.one_eq_succ_zero MyNat.two_eq_succ_one MyNat.three_eq_succ_two
  MyNat.four_eq_succ_three MyNat.add_zero MyNat.add_succ MyNat.mul_zero MyNat.mul_succ
  MyNat.pow_zero MyNat.pow_succ MyNat.reflection MyNat.succ_inj MyNat.zero_ne_succ
  MyNat.peano_cases

-- The spec files `succ_inj` under Peano; by itself Proposition Mode's lower menu would
-- put it among the `+` theorems, as it does in NNG4.
VisualPeanoTab MyNat.succ_inj

MakeGame
