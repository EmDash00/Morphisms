import Mathlib.Algebra.Order.Field.Defs
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.WellFounded
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib


-- The subring of non-negative elements
def nonneg_subring (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] : Subsemiring R where
  carrier := {x : R | x ≥ 0}
  zero_mem' := by simp only [ge_iff_le, Set.mem_setOf_eq, le_refl]
  one_mem' := by simp only [ge_iff_le, Set.mem_setOf_eq, zero_le_one]
  add_mem' := by
    intro _ _ ha hb
    exact add_nonneg ha hb
  mul_mem' := by
    intro _ _ ha hb
    exact mul_nonneg ha hb

class IsNatural (N : Type) extends CommSemiring N, LinearOrder N, IsStrictOrderedRing N, IsWellOrder N (· < ·) where
  unique_hom : ∀ (R : Type) [Semiring R] [Preorder R], Subsingleton (N →+*o R)


class IsInteger (Z : Type) extends CommRing Z, LinearOrder Z, IsStrictOrderedRing Z where
  nat_inj : nonneg_subring Z ≃+*o ℕ


class IsRational (Q : Type) [Field Q] [LinearOrder Q] [IsStrictOrderedRing Q] where
  minimal : ∀ (f : Q →+* Q), Function.Injective f → Function.Surjective f


class IsReal (R : Type) [Field R] [ConditionallyCompleteLinearOrder R]

instance : IsInteger Int where
  nat_inj := {
    toFun := fun x ↦ (x : Int).toNat
    invFun := fun n ↦ ⟨Int.ofNat n, by simp⟩
    left_inv := by
      simp
      refine Function.leftInverse_of_surjective_of_rightInverse ?_ (congrFun rfl)
      intro x
      use (x : Int).toNat
      simp
      ext : 1
      simp_all only [Nonneg.coe_natCast, Int.ofNat_toNat, sup_eq_left]
      exact x.mem
    map_mul' := by
      intro x y
      exact Int.toNat_mul x.mem y.mem
    map_add' := by
      intro x y
      exact Int.toNat_add x.mem y.mem
    map_le_map_iff' := by
      intro x y
      simp
      intro h
      refine Subtype.coe_le_coe.mp ?_
      by_cases h_zero : x = 0
      . subst_vars
        exact y.mem
      . change x ≠ 0 at h_zero
        have x_neg : x < 0 := by exact lt_of_le_of_ne h h_zero
        have x_nonneg : x >= 0 := by exact x.mem
        exact le_imp_le_of_lt_imp_lt (fun a ↦ x_neg) x_nonneg
  }
