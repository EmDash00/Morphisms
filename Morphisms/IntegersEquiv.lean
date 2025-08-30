import Morphisms.Integers
import Mathlib

open Lean Elab Tactic

def digit (base n : Nat) (k : Nat) : ℕ := (n / base^k) % base

def binDigit (n k : Nat) : ℕ := digit 2 n k

def lsb (n : Nat) : ℕ := digit 2 n 0

def numeric_map (x : ℕ) : String := by
  mod_cases h : x % 10
  . exact ""
  . exact "I"
  . exact "oo"
  . exact "ana"
  . exact "swap"
  . exact "straw"
  . exact "redder"
  . exact "rotator"
  . exact "starrats"
  . exact "birchcrab"



theorem lsb_add_zero_one (x y : ℕ) (hx : lsb x = 0) (hy : lsb y = 1) : lsb (x + y) = 1 := by
  revert hx hy
  unfold lsb digit
  simp
  intro hx hy




-- Metaprogram to lift all ZMod 2 variables to Bool
def recast_tac (src tgt : Syntax) : TacticM Unit := do
  let srcExpr ← elabTerm src none
  let tgtTerm : TSyntax `term := ⟨tgt⟩

  let ctx ← getLCtx

  evalTactic (← `(tactic| try rw [eqCast $tgtTerm]))

  -- Lift each variable of the source type to the target type
  for decl_option in ctx.decls do
    match decl_option with
    | some decl =>
      if ←Meta.isDefEq decl.type srcExpr then
        evalTactic (← `(tactic| lift $(mkIdent decl.userName) to $tgtTerm using (by trivial)))
    | none => continue

  evalTactic (← `(tactic| simp only[BooleanEquiv.map_and, BooleanEquiv.map_or, booleanEquivInv]))

