import Mathlib
import Mathlib.Data.Vector.Basic

open Classical

variable (α β : Type*)

def Operation := Σ (n : ℕ), (Vector α n → β)  -- Polymorphic in arity `n`
def Operator := Operation α α
def Relation := Operation α Prop

def unaryOp {α : Type*} (f : α → α) : (Operator α) := ⟨1, fun args ↦ f args[0]⟩
def binaryOp  {α : Type*} (f : α → α → α) : (Operator α) := ⟨2, fun args ↦ f args[0] args[1]⟩
def ternaryOp  {α : Type*} (f : α → α → α → α) : (Operator α) := ⟨3, fun args ↦ f args[0] args[1] args[2]⟩

def unaryRel  {α : Type*} (f : α → Prop) : (Relation α) := ⟨1, fun args ↦ f args[0]⟩
def binaryRel  {α : Type*} (f : α → α → Prop) : (Relation α) := ⟨2, fun args ↦ f args[0] args[1]⟩
def ternaryRel  {α : Type*} (f : α → α → α → Prop) : (Relation α) := ⟨3, fun args ↦ f args[0] args[1] args[2]⟩


structure AlgebraicSignature where
  operations : List (Operator α)
  relations : List (Relation α)

structure AlgebraicStructure extends AlgebraicSignature α where
  -- A tuple of the properties the algebraic structure has and proofs of those properties
  -- Written as: ⟨property, proof of property⟩
  axioms : List (PSigma (fun (p : Prop) => p))

def isCommutative {α : Type*} (f : α → α → α) : Prop := ∀ x y : α, f x y = f y x
def isAntiCommutative {α : Type*} [Neg α] (f : α → α → α) : Prop := ∀ x y : α, f x y = -f y x
def isAssociative {α : Type*} (f : α → α → α) : Prop := ∀ x y z : α, f (f x y) z = f x (f y z)
def hasIdentity  {α : Type*} (f : α → α → α) : Prop := ∃ id : α, ∀ x : α, f x id = x ∧ f id x = x
def hasInverse {α : Type*} (f : α → α → α) (h_id : hasIdentity f) : Prop :=
  let id := Classical.choose h_id
  ∀ (x : α), ∃ (x_inv : α), f x x_inv = id ∧ f x_inv x = id


def isReflexive {α : Type*} (R : α → α → Prop) : Prop := ∀ x : α, R x x
def isSymmetric {α : Type*} (R : α → α → Prop) : Prop := ∀ x y : α, R x y → R y x
def isAntiSymmetric {α : Type*} (R : α → α → Prop) : Prop := ∀ x y : α, R x y ∧ R y x → x = y
def isConnected {α : Type*} (R : α → α → Prop) : Prop := ∀ x y : α, x ≠ y → R x y ∨ R y x
def isStronglyConnected {α : Type*} (R : α → α → Prop) : Prop := ∀ x y : α, R x y ∨ R y x
def isTransitive {α : Type*} (R : α → α → Prop) : Prop := ∀ x y z : α, R x y ∧ R y z → R x z
def isLeftTotal {α : Type*} (R : α → α → Prop) : Prop := ∀ x : α, ∃ y : α, R x y
def isRightTotal {α : Type*} (R : α → α → Prop) : Prop := ∀ y : α, ∃ x : α, R x y
def isDense {α : Type*} (R : α → α → Prop) : Prop := ∀ x y : α, R x y → ∃ z : α, R x z ∧ R z y

def isWellFounded  {α : Type*} (R : α → α → Prop) : Prop := ∃ m : α, ∀ x : α, R m x
def isWellOrdering {α : Type*} (R : α → α → Prop) : Prop := isWellFounded R ∧ isConnected R

def isPartialOrder {α : Type*} (R : α → α → Prop) := isReflexive R ∧ isAntiSymmetric R ∧ isTransitive R
def isStrictPartialOrder {α : Type*} (R : α → α → Prop) := ¬isReflexive R ∧ isAntiSymmetric R ∧ isTransitive R
def isTotalOrder {α : Type*} (R : α → α → Prop) := isPartialOrder R ∧ isConnected R
def isStrictTotalOrder {α : Type*} (R : α → α → Prop) := isStrictPartialOrder R ∧ isConnected R
def isEquivalenceRelation {α : Type*} (R : α → α → Prop) := isReflexive R ∧ isSymmetric R ∧ isTransitive R
def isLeftDistributive {α : Type*} (f g : α → α → α) := ∀ x y z : α, f z (g x y) = g (f z x) (f z y)
def isRightDistributive {α : Type*} (f g : α → α → α) := ∀ x y z : α, f (g x y) z = g (f x z) (f y z)


def intAdd {α : Type*} [Add α] (x y : α) := x + y
def intMul {α : Type*} [Mul α] (x y : α) := x * y
def intNeg {α : Type*} [Neg α] (x : α) := -x

def intLt {α : Type*} [LT α] := fun (x y : α) ↦ x < y
def intEq {α : Type*} (x y : α) := x = y

∃
def IntegerStructure (α : Type*) [Add α] [Mul α] [Neg α] [LT α] : AlgebraicStructure α := {
  operations := [
    unaryOp intNeg,
    binaryOp intAdd,
    binaryOp intMul
  ]
  relations := [
    binaryRel intLt,
    binaryRel intEq,
  ]
  axioms := [
    ⟨isCommutative intAdd, sorry⟩,
    ⟨isAssociative intAdd, sorry⟩,
    ⟨hasInverse intAdd, sorry⟩,
    ⟨isCommutative intMul, sorry⟩,
    ⟨isAssociative intMul, sorry⟩,
    ⟨hasInverse intMul, sorry⟩,
    ⟨isLeftDistributive intMul intAdd, sorry⟩,
    ⟨isEquivalenceRelation intEq, sorry⟩,
    ⟨isStrictTotalOrder intLt, sorry⟩,
  ]
}
