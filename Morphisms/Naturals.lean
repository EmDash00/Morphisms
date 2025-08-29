import Mathlib

class IsNatural (N : Type*) extends Semiring N, LinearOrder N, IsStrictOrderedRing N, IsWellOrder N (· < ·) where
  toSucc : N → N
  succInj: Function.Injective toSucc
  zeroNotSucc : ∀ n : N, zero ≠ toSucc n
  induction : ∀ n : N, n ≠ zero → ∃ m : N, toSucc m = n
