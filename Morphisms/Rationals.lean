import Mathlib

class IsRational (Q : Type) extends Field Q, CharZero Q, LinearOrder Q, IsStrictOrderedRing Q where
  minimal : ∀ x : Q, ∃ (a b : ℤ), (algebraMap ℤ Q) b ≠ 0 ∧ x = (algebraMap ℤ Q) a / (algebraMap ℤ Q) b
