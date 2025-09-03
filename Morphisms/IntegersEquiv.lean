import Morphisms.Integers
import Morphisms.Palindrome
import Mathlib
import Mathlib.Algebra.Order.Hom.Ring
open Lean Elab Tactic

/-
The following are useful lemmas for simplifying casts.
-/
@[simp]
lemma ofInt_intCast (Z : Type*) [is_int : IsInteger Z] (z : Z) : ((z : ℤ) : Z) = z := by
    change EquivLike.inv is_int.intEquiv (is_int.intEquiv z) = z
    rw[EquivLike.inv_apply_eq (e := IsInteger.intEquiv) (b := IsInteger.intEquiv z) (a := z)]

@[simp]
lemma intCast_ofInt (Z : Type*) [is_int : IsInteger Z] (z : ℤ) : ((z : Z) : ℤ) = z := by
    change is_int.intEquiv (EquivLike.inv is_int.intEquiv z) = z
    symm
    rw[←EquivLike.inv_apply_eq (e := IsInteger.intEquiv) (b := z) (a := EquivLike.inv IsInteger.intEquiv z)]

@[simp]
lemma intCastInt (z : ℤ) : toInt z = z := by rfl

instance (α β : Type*) [IsInteger α] [IsInteger β] : CanLift β α (fun a ↦ (a : β)) (fun _ ↦ True) where
  prf := by
    intro b
    simp only [forall_const]
    use (b : α)
    simp only [intCast_ofInt, ofInt_intCast]

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

  -- The final version of this tactic should use metaprogramming to see which simplifications can be used.
  evalTactic (← `(tactic| simp only[map_mul, map_add, OrderRingIso.map_le_map_iff', ofInt_intCast, ofInt_intCast, intCast_ofInt, intCastInt]))


elab "recast" src:term "as" tgt:term : tactic => do
  recast_tac src tgt

example (z : QuotientInt) : isPalindrome (String.mk ((palindrome_map_int z).data ++ (palindrome_map_int (-z)).data)) := by
  recast QuotientInt as ℤ
  exact neg_concat_isPalindrome z
