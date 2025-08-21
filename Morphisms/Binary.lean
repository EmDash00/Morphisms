import Mathlib
import Mathlib.Data.Finset.Defs
import Mathlib.Tactic

open Lean Elab Tactic


class BinaryType (α : Type*) extends Zero α, One α, Nontrivial α, Fintype α, Insert α (Finset α) where
  elems := {zero, one}
  decidable_eq : DecidableEq α  -- You can't synthesize this at the typeclass level sadly...
  exhaustive : ∀ (x : α), x = zero ∨ x = one

-- Hack.
instance (α : Type*) [B : BinaryType α] : DecidableEq α := by exact B.decidable_eq

class BooleanType (α : Type*) extends BinaryType α, AndOp α, Complement α where
  absorbing : ∀ x : α, zero &&& x = zero
  identity : ∀ x : α, one &&& x = x
  not_identity : ∀ x : α, ~~~x ≠ x
  and_assoc : ∀ x y z : α, (x &&& y) &&& z = x &&& (y &&& z)

instance (α : Type*) [BooleanType α] : OrOp α where
  or := fun x y => ~~~((~~~x) &&& (~~~y))


class BooleanEquiv (α β : Type*) [BooleanType α] [BooleanType β] extends α ≃ β where
  map_one : toFun One.one = One.one
  map_zero: toFun Zero.zero = Zero.zero
  map_and : ∀ x y : α, toFun (x &&& y) = toFun x &&& toFun y
  map_not : ∀ x : α, toFun (~~~x) = ~~~toFun x
  map_or: ∀ x y : α, toFun (x ||| y) = toFun x ||| toFun y

instance (α β : Type*) [BooleanType α] [BooleanType β] : CoeFun (BooleanEquiv α β) (λ _ => α → β) where
  coe e := e.toEquiv.toFun


infixr:25 " ≃~& " => BooleanEquiv

@[simp] theorem one_neq_zero {α : Type*} [a : BooleanType α] : (One.one : α) ≠ (Zero.zero : α) := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := a.exists_pair_ne
  suffices h : ∀ x y : α, x = y by
    have := h x y
    contradiction
  exfalso
  cases a.exhaustive x
  <;> cases a.exhaustive y
  <;> subst_vars
  <;> simp_all only [ne_eq, not_true_eq_false]

@[simp] theorem one_and_zero {α : Type*} [BooleanType α] : (One.one : α) &&& (Zero.zero : α) = Zero.zero := by
  exact BooleanType.identity 0

@[simp] theorem zero_and_one {α : Type*} [BooleanType α] : (Zero.zero : α) &&& (One.one : α) = Zero.zero := by
  exact BooleanType.absorbing 1

@[simp] theorem zero_and_zero {α : Type*} [BooleanType α] : (Zero.zero : α) &&& (Zero.zero : α) = Zero.zero := by
  exact BooleanType.absorbing 0

@[simp] theorem one_and_one {α : Type*} [BooleanType α] : (One.one : α) &&& (One.one : α) = One.one := by
  exact BooleanType.identity 1

theorem and_comm' {α : Type*} [BooleanType α] : ∀ x y : α, x &&& y = y &&& x := by
  intro x y
  cases BinaryType.exhaustive x
  <;> cases BinaryType.exhaustive y
  <;> subst_vars
  <;> simp

theorem and_assoc' {α : Type*} [BooleanType α] : ∀ x y z : α, (x &&& y) &&& z = x &&& (y &&& z) := by
  intro x y z
  cases BinaryType.exhaustive x
  <;> cases BinaryType.exhaustive y
  <;> cases BinaryType.exhaustive z
  <;> subst_vars
  <;> simp

@[simp] theorem not_one {α : Type*} [BooleanType α] : ~~~(One.one : α) = Zero.zero := by
  cases BinaryType.exhaustive (~~~(1 : α)) with
  | inl h => exact h
  | inr h =>
    suffices ~~~(1 : α) ≠ (1 : α)
      by contradiction
    exact BooleanType.not_identity 1

@[simp] theorem not_zero {α : Type*} [BooleanType α] : ~~~(Zero.zero : α) = One.one := by
  cases BinaryType.exhaustive (~~~(0 : α)) with
  | inr h => exact h
  | inl h =>
    suffices ~~~(0 : α) ≠ (0 : α)
      by contradiction
    exact BooleanType.not_identity 0

@[simp] theorem not_not' {α : Type*} [BooleanType α] : ∀ x : α, ~~~(~~~x) = x := by
  intro x
  cases BinaryType.exhaustive x with
  | inl h | inr h =>
    subst h
    simp

theorem or_apply {α : Type*} [a : BooleanType α] (x y : α) : x ||| y = ~~~((~~~x) &&& (~~~y)) := by
  rfl

@[simp] theorem zero_or_zero {α : Type*} [a : BooleanType α] : (Zero.zero : α) ||| (Zero.zero : α) = Zero.zero := by
  simp[or_apply]

@[simp] theorem one_or_zero {α : Type*} [a : BooleanType α] : (One.one : α) ||| (Zero.zero : α) = One.one := by
  simp[or_apply]

@[simp] theorem zero_or_one {α : Type*} [a : BooleanType α] : (Zero.zero : α) ||| (One.one : α)  = One.one := by
  simp[or_apply]

@[simp] theorem one_or_one {α : Type*} [a : BooleanType α] : (One.one : α) ||| (One.one : α) = One.one := by
  simp[or_apply]

@[simp] theorem zero_or  {α : Type*} [a : BooleanType α] (x : α) : (Zero.zero : α) ||| x = x := by
  cases BinaryType.exhaustive x
  <;> subst_vars
  <;> simp

@[simp] theorem or_zero  {α : Type*} [a : BooleanType α] (x : α) : x ||| (Zero.zero : α) = x := by
  cases BinaryType.exhaustive x
  <;> subst_vars
  <;> simp

@[simp] theorem one_or  {α : Type*} [a : BooleanType α] (x : α) : (One.one : α) ||| x = One.one := by
  cases BinaryType.exhaustive x
  <;> subst_vars
  <;> simp

@[simp] theorem or_one  {α : Type*} [a : BooleanType α] (x : α) : x ||| (One.one : α) = One.one := by
  cases BinaryType.exhaustive x
  <;> subst_vars
  <;> simp

theorem nand_dist {α : Type*} [BooleanType α] (x y : α) : ~~~(x &&& y) = ~~~x ||| ~~~y := by
  simp[or_apply]

theorem nor_dist {α : Type*} [BooleanType α] (x y : α) : ~~~(x ||| y) = ~~~x &&& ~~~y := by
  simp[or_apply]

def mkBooleanEquiv (α β : Type*) [a : BooleanType α] [b : BooleanType β] : α ≃~& β := {
  toFun := fun x =>  if x = (a.zero : α) then b.zero else b.one
  invFun := fun x => if x = (b.zero : β) then a.zero else a.one
  left_inv := by
    refine Function.leftInverse_iff_comp.mpr ?_
    ext x
    cases a.exhaustive x
    <;> subst_vars
    <;> simp

  right_inv := by
    refine Function.rightInverse_iff_comp.mpr ?_
    ext x
    cases b.exhaustive x
    <;> subst_vars
    <;> simp

  map_one := by simp
  map_zero := by simp
  map_and := by
    intro x y
    cases a.exhaustive x
    <;> cases a.exhaustive y
    <;> subst_vars
    <;> simp
  map_not := by
    intro x
    cases a.exhaustive x
    <;> subst_vars
    <;> simp
  map_or := by
    intro x y
    cases a.exhaustive x
    <;> cases a.exhaustive y
    <;> subst_vars
    <;> simp
}

class EquivCoe (α β : Type*) [a : BooleanType α] [b : BooleanType β] extends Coe α β where
  equiv : α ≃ β
  coe := equiv
  co_eqquiv : coe = equiv := by rfl


instance (α β : Type*) [BooleanType α] [BooleanType β] : CanLift α β (mkBooleanEquiv β α) (fun _ => True) where
  prf := by intros; exact (mkBooleanEquiv β α).surjective _

-- Bool is a BinaryType
instance : BooleanType Bool where
  zero := false
  one := true
  decidable_eq := by exact instDecidableEqBool
  exists_pair_ne := by trivial
  exhaustive := by
    intro x
    cases x <;> simp only [Bool.false_eq_true, or_false, or_true]
  and := Bool.and
  and_assoc := by convert Bool.and_assoc
  complement := Bool.not
  absorbing := by intros; rfl;
  identity := by intros; rfl;
  not_identity := by simp

-- ℤ / 2ℤ is a BinaryType
instance : BooleanType (ZMod 2) where
  exhaustive := by trivial
  decidable_eq := by exact instDecidableEqFin 2
  and := fun x y ↦ x * y
  complement := fun x ↦ x + 1
  and_assoc := by convert mul_assoc
  absorbing := by convert zero_mul
  identity := by convert one_mul
  not_identity := by exact succ_ne_self

instance : EquivCoe (ZMod 2) Bool where
  equiv := (mkBooleanEquiv _ _).toEquiv


theorem booleanEquivInv (β : Type*) (α : Type*) [a : BooleanType α] [BooleanType β] (x : α) :
    mkBooleanEquiv β α (mkBooleanEquiv α β x) = x := by
      simp[mkBooleanEquiv]
      cases a.exhaustive x
      <;> subst_vars
      <;> simp


lemma eqCast (β : Type*) (α : Type*) [BooleanType α] [BooleanType β] (x y : α) : x = y ↔ mkBooleanEquiv α β x = mkBooleanEquiv α β y := by
  simp_all only [Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq]


theorem or_and (a b c : Bool) : a ||| (b &&& c) = (a ||| b) &&& (a ||| c) := by
  cases BinaryType.exhaustive a
  <;> subst_vars
  <;> simp

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


elab "recast" src:term "as" tgt:term : tactic => do
  recast_tac src tgt

theorem zmod2_or_and (a b c : ZMod 2) : a ||| (b &&& c) = (a ||| b) &&& (a ||| c) := by
  recast ZMod 2 as Bool
  exact or_and a b c

