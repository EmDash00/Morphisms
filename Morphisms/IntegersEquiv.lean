import Morphisms.Integers
import Mathlib

open Lean Elab Tactic

@[ext]
structure IntLike where
  val : ℤ

instance : Add IntLike where
  add a b := ⟨a.val + b.val⟩

instance : Mul IntLike where
  mul a b := ⟨a.val * b.val⟩

instance : Zero IntLike where
  zero := ⟨0⟩

instance : One IntLike where
  one := ⟨1⟩

instance a : IsInteger IntLike where
  add_assoc := by
    intros
    simp only[HAdd.hAdd, Add.add]; simp only [Int.add_def, IntLike.mk.injEq]
    exact add_assoc _ _ _
  add_comm := by
    intros
    simp only[HAdd.hAdd, Add.add]; simp only [Int.add_def, IntLike.mk.injEq]
    exact add_comm _ _
  zero_add := by
    intro a
    simp only[HAdd.hAdd, Add.add]; ext; simp; rfl
  add_zero := by
    intro a
    simp only[HAdd.hAdd, Add.add]; ext; simp; rfl

  nsmul := fun a b ↦ IntLike.mk a * b
  zsmul := fun a b ↦ IntLike.mk a * b
  neg := fun a ↦ ⟨-a.val⟩

  neg_add_cancel := by
    intro
    simp only[HAdd.hAdd, Add.add]; ext; simp; rfl

  mul_assoc := by
    intros
    simp only[HMul.hMul, Mul.mul]; simp only [Int.mul_def, IntLike.mk.injEq]
    exact mul_assoc _ _ _
  mul_comm := by
    intros
    simp only[HMul.hMul, Mul.mul]; simp only [Int.mul_def, IntLike.mk.injEq]
    exact mul_comm _ _
  zero_mul := by
    intro a
    simp only[HMul.hMul, Mul.mul]; ext; simp;
    change 0 * a.val = 0
    simp only[zero_mul]
  mul_zero := by
    intro a
    simp only[HMul.hMul, Mul.mul]; ext; simp;
    change a.val * 0 = 0
    simp only[mul_zero]
  one_mul := by
    intro a
    simp only[HMul.hMul, Mul.mul]; ext; simp;
    change 1 * a.val = a.val
    simp only[one_mul]
  mul_one:= by
    intro a
    simp only[HMul.hMul, Mul.mul]; ext; simp;
    change a.val * 1 = a.val
    simp only[mul_one]
  left_distrib := by
    intros
    simp only[HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]; ext; simp;
    exact left_distrib _ _ _
  right_distrib := by
    intros
    simp only[HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]; ext; simp;
    exact right_distrib _ _ _

  le := fun a b ↦ a.val ≤ b.val
  le_refl := by simp only [le_refl, implies_true]
  le_trans := by  intro _ _ _; exact Int.le_trans
  le_antisymm := by intro _ _ ha hb; ext; exact Int.le_antisymm ha hb
  le_total := by intro a b; exact Int.le_total a.val b.val
  toDecidableLE := fun a b ↦ if h : a.val ≤ b.val then isTrue (h) else isFalse (h)






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

