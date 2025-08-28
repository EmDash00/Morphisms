import Mathlib.Algebra.Order.Field.Defs
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.WellFounded
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.UniformSpace.Cauchy

import Mathlib

class IsInteger (Z : Type*) extends CommRing Z, LinearOrder Z, IsStrictOrderedRing Z where
  ofNat : ℕ → Z
  intEquiv : Z ≃+*o ℤ
  nonneg_well_ordered : IsWellOrder {z : Z | z ≥ 0} (· < ·)

instance IsIntOfNat (Z : Type*) [is_int : IsInteger Z] (n : ℕ) : OfNat Z n := ⟨is_int.ofNat n⟩

class IsReal (R : Type) extends Field R, ConditionallyCompleteLinearOrder R, IsStrictOrderedRing R


instance : IsInteger Int where
  ofNat := Int.ofNat
  intEquiv := by exact OrderRingIso.refl ℤ
  nonneg_well_ordered := by
    refine {
      toIsTrichotomous := instIsTrichotomousLt,
      toIsTrans := instIsTransLt,
      toIsWellFounded := {
        wf := WellFounded.intro fun a => ?_
      }
    }

    apply (measure fun (z : {z : ℤ | z ≥ 0}) ↦ z.val.natAbs).wf.induction

    intro ⟨x, hx⟩ hI
    constructor
    intro ⟨y, hy⟩
    convert hI ⟨y, hy⟩ using 1

    change x ≥ 0 at hx
    change y ≥ 0 at hy
    change y < x ↔ y.natAbs < x.natAbs
    zify
    simp only[abs_of_nonneg, hx, hy]


@[ext]
structure NatPair where
  p : Nat
  q : Nat
deriving DecidableEq

@[simp]
def nat_pair_eq (x y: NatPair) : Prop := x.p + y.q = x.q + y.p

instance nat_pair_eq_equiv : Equivalence nat_pair_eq where
  refl := by
    intro x
    exact Nat.add_comm x.p x.q
  symm := by
    intro x y hx
    simp_all only[nat_pair_eq]
    linarith
  trans := by
    intro x y z hx hy
    simp_all only [nat_pair_eq]
    linarith

instance PreIntSetoid : Setoid NatPair := ⟨nat_pair_eq, nat_pair_eq_equiv⟩
def QuotientInt := Quotient PreIntSetoid

def mkQuotientInt (w : NatPair) : QuotientInt := Quotient.mk PreIntSetoid w

instance int_of_nat {n: ℕ} : OfNat QuotientInt n where
  ofNat := mkQuotientInt ⟨n, 0⟩

-- (a - b) ≤ (c - d)
-- (a + d) ≤ (c + b)
def le_nat_pair (x y : NatPair) : Prop := x.p + y.q ≤ y.p + x.q

def lt_nat_pair (x y : NatPair) : Prop := x.p + y.q < y.p + x.q

def lt_quotient_int (x y : QuotientInt) : Prop := by
  refine x.lift₂ lt_nat_pair ?_ y
  intro ⟨a, b⟩ ⟨p, q⟩ ⟨c, d⟩ ⟨r, s⟩ ha hb
  simp only [eq_iff_iff]
  change a + d = b + c at ha
  change p + s = q + r at hb
  constructor
  <;> simp[lt_nat_pair]
  <;> intros <;> linarith

def le_quotient_int (x y : QuotientInt) : Prop := by
  refine x.lift₂ le_nat_pair ?_ y
  intro ⟨a, b⟩ ⟨p, q⟩ ⟨c, d⟩ ⟨r, s⟩ ha hb
  simp only [eq_iff_iff]
  change a + d = b + c at ha
  change p + s = q + r at hb
  constructor
  <;> simp[le_nat_pair]
  <;> intros <;> linarith

def neg_quotient_int (x : QuotientInt) : QuotientInt := by
  refine x.map (fun a : NatPair ↦ NatPair.mk a.q a.p) ?_
  intro ⟨a, b⟩ ⟨c, d⟩ hab
  simp only
  change a + d = b + c at hab
  change b + c = a + d
  exact hab.symm

def add_nat_pair (x y : NatPair) : NatPair :=
    NatPair.mk (x.p + y.p) (x.q + y.q)

def add_nat_pair_comm (x y : NatPair) : add_nat_pair x y = add_nat_pair y x := by
  simp[add_nat_pair]
  constructor
  <;> rw[add_comm]

def add_nat_pair_assoc (x y z : NatPair) : add_nat_pair (add_nat_pair x y) z = add_nat_pair x (add_nat_pair y z) := by
  simp[add_nat_pair]
  constructor
  <;> rw[add_assoc]

def add_quotient_int (x y : QuotientInt) : QuotientInt := by
  refine x.map₂ add_nat_pair ?_ y
  intro a1 a2 ha b1 b2 hb
  simp[add_nat_pair]
  change a1.p + a2.q = a1.q + a2.p at ha
  change b1.p + b2.q = b1.q + b2.p at hb
  change a1.p + b1.p + (a2.q + b2.q) = a1.q + b1.q + (a2.p + b2.p)
  linarith

 def mul_nat_pair (x y : NatPair) : NatPair :=
    NatPair.mk (x.p * y.p + x.q * y.q) (x.p * y.q + x.q * y.p)

 --refine x.lift₂ (fun a b : NatPair ↦ add_nat_pair a b = add_nat_pair b a) ?_ y

def mul_quotient_int (x y : QuotientInt) : QuotientInt := by
  refine x.map₂ mul_nat_pair ?_ y
  intro ⟨a, b⟩ ⟨p, q⟩ ha ⟨c, d⟩ ⟨r, s⟩ hb
  simp[mul_nat_pair]

  change a + q = b + p at ha
  change c + s = d + r at hb
  change a * c + b * d + (p * s + q * r) = a * d + b * c + (p * r + q * s)

  suffices (a * c + b * d + p * s + q * r) + (p * c + q * c + p * d + q * d) =
    (a * d + b * c + p * r + q * s) + (p * c + q * c + p * d + q * d) by
        rw [Nat.add_right_cancel_iff] at this
        convert this using 0
        ac_nf
  calc
    _ = (a * c + q * c) + (b * d + p * d) + (p * c + p * s) + (q * d + q * r) := by
      ac_rfl

    _ = (a + q) * c + (b + p) * d + p * (c + s) + q * (d + r) := by
      simp only[←left_distrib, ←right_distrib]

    _ = (b + p) * c + (a + q) * d + p * (d + r) + q * (c + s) := by
      simp only[ha, hb]

    _ = (b * c + p * c) + (a * d + q * d) + (p * d + p * r) + (q * c + q * s) := by
      simp only[left_distrib, right_distrib]

    _ = (a * d + b * c + p * r + q * s) + (p * c + q * c + p * d + q * d) := by
      ac_rfl

def quotient_int_add_comm (x y : QuotientInt) : add_quotient_int x y = add_quotient_int y x := by
    simp[add_quotient_int]
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩
    simp only [Quotient.map₂_mk, add_nat_pair]
    conv => rhs; simp[add_comm]

def quotient_int_mul_comm (x y: QuotientInt) : mul_quotient_int x y = mul_quotient_int y x := by
    simp[mul_quotient_int]
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩
    simp only [Quotient.map₂_mk, mul_nat_pair]
    congr 2
    <;> ac_rfl

def quotient_int_add_zero (x : QuotientInt) : add_quotient_int x 0 = x := by
    change add_quotient_int x ⟦⟨0, 0⟩⟧ = x
    simp[add_quotient_int]
    refine Quotient.inductionOn x ?_
    intro ⟨a, b⟩
    simp only [Quotient.map₂_mk, add_nat_pair, add_zero]

def quotient_int_mul_one (x : QuotientInt) : mul_quotient_int x 1 = x := by
    change mul_quotient_int x ⟦⟨1, 0⟩⟧ = x
    simp[mul_quotient_int]
    refine Quotient.inductionOn x ?_
    intro ⟨a, b⟩
    simp [Quotient.map₂_mk, mul_nat_pair]

def quotient_int_mul_zero (x : QuotientInt) : mul_quotient_int x 0 = 0 := by
    change mul_quotient_int x ⟦⟨0, 0⟩⟧ = ⟦⟨0, 0⟩⟧
    simp[mul_quotient_int]
    refine Quotient.inductionOn x ?_
    intro ⟨a, b⟩
    simp [Quotient.map₂_mk, mul_nat_pair]

def quotient_int_left_distrib (x y z : QuotientInt) :
    mul_quotient_int x (add_quotient_int y z) =
    add_quotient_int (mul_quotient_int x y) (mul_quotient_int x z) := by
      simp[mul_quotient_int, add_quotient_int]
      refine Quotient.inductionOn₃ x y z ?_
      intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
      simp[mul_nat_pair, add_nat_pair]
      congr 2
      <;> ring

def quotient_int_right_distrib (x y z : QuotientInt) :
    mul_quotient_int (add_quotient_int x y) z =
    add_quotient_int (mul_quotient_int x z) (mul_quotient_int y z) := by
      convert quotient_int_left_distrib z x y using 1
      <;> simp[quotient_int_mul_comm]


def quotient_int_ofNat (n : ℕ) : QuotientInt := ⟦⟨n, 0⟩⟧

lemma lt_and_le_iff_lt (a b : ℕ) : a ≤ b ∧ a < b ↔ a < b := by
  constructor
  . intro h
    exact h.right
  . intro hmpr
    constructor
    . exact Nat.le_of_succ_le hmpr
    . exact hmpr

lemma gt_def {a b : ℕ} (h : a < b) : ∃ k : ℕ, a + k = b ∧ k > 0 := by
  use b - a
  constructor
  . refine Nat.add_sub_of_le ?_
    exact Nat.le_of_succ_le h
  . exact Nat.zero_lt_sub_of_lt h

def abs_nat_pair (x : NatPair) : ℕ :=
  if x.p ≥ x.q then
    x.p - x.q
  else
    x.q - x.p

def int_nat_pair (x : NatPair) : ℤ := Int.ofNat x.p - Int.ofNat x.q

def quotient_int_natAbs (x : QuotientInt) : ℕ := by
  refine x.lift abs_nat_pair ?_
  intro ⟨a, b⟩ ⟨c, d⟩ hab
  change a + d = b + c at hab
  simp[abs_nat_pair]
  have h_ineq : b ≤ a ↔ d ≤ c := by
    constructor
    . intro hmp
      rw[←Nat.add_le_add_iff_left (n := a), hab, Nat.add_le_add_iff_right]
      exact hmp
    . intro hmpr
      rw[←Nat.add_le_add_iff_right (n := c), ←hab, Nat.add_le_add_iff_left]
      exact hmpr

  refine ite_congr ?_ ?_ ?_
  . simp; exact h_ineq
  . intro h
    have : b ≤ a := by exact h_ineq.mpr h
    rw[←Nat.add_right_cancel_iff (n := b + d)]
    ac_change a - b + b + d = c - d + d + b
    simp[Nat.sub_add_cancel, this, h]
    convert hab using 1
    ac_rfl
  . intro h
    simp at h
    have h' : c ≤ d := by exact Nat.le_of_succ_le h
    have h2' : a ≤ b := by exact Nat.le_of_succ_le ((lt_iff_lt_of_le_iff_le (id (Iff.symm h_ineq))).mp h)

    rw[←Nat.add_right_cancel_iff (n := a + c)]
    ac_change b - a + a + c = d - c + c + a
    simp[Nat.sub_add_cancel, h', h2']
    convert hab.symm using 1
    ac_rfl


theorem quotient_int_mul_lt_of_pos_right (x y z : QuotientInt) :
  lt_quotient_int x y → lt_quotient_int 0 z → lt_quotient_int (mul_quotient_int x z) (mul_quotient_int y z) := by
        change _ → lt_quotient_int ⟦⟨0, 0⟩⟧ z → _
        refine Quotient.inductionOn₃ x y z ?_
        intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
        simp_all [lt_quotient_int, lt_nat_pair, Quotient.lift_mk,  Quotient.map₂_mk, mul_quotient_int, mul_nat_pair]
        intro hxy hz
        have ⟨k, ⟨hk_eq, hk_pos⟩⟩  : ∃ k : ℕ, f + k = e ∧ k > 0 := by exact gt_def hz

        ac_change (a * e + d * e) + (c * f + b * f) < (c * e + b * e) + (a * f + d * f)
        simp[←right_distrib]
        rw[←hk_eq]
        simp [left_distrib]
        ac_change (a + d) * f + (c + b) * f + (a + d) * k < (a + d) * f + (c + b) * f + (c + b) * k
        simp[←right_distrib]
        exact Nat.mul_lt_mul_of_pos_right hxy hk_pos

@[simp]
def coeZQuotientInt : ℤ → QuotientInt
    | Int.ofNat n => ⟦⟨n, 0⟩⟧
    | Int.negSucc n => ⟦⟨0, n + 1⟩⟧

instance : Coe ℤ QuotientInt where
  coe := coeZQuotientInt


instance : LinearOrder QuotientInt where
  le := le_quotient_int
  lt := lt_quotient_int

  toDecidableLE := fun x y : QuotientInt ↦
    Quotient.recOnSubsingleton₂ x y fun a b ↦
      if h : a.p + b.q ≤ b.p + a.q then
        isTrue (by
          change le_quotient_int ⟦a⟧ ⟦b⟧
          simp[le_quotient_int, le_nat_pair]
          exact h
        )
      else
        isFalse (by
          change ¬le_quotient_int ⟦a⟧ ⟦b⟧
          simp[le_quotient_int, le_nat_pair]
          simp at h
          exact h
        )

  le_refl := by
    intro x
    simp[le_quotient_int]
    refine Quotient.inductionOn x ?_
    intro ⟨a, b⟩
    simp[le_nat_pair]

  le_trans := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    simp[le_quotient_int, le_nat_pair]
    intro hxy hyz
    linarith

  le_antisymm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩
    simp[le_quotient_int, le_nat_pair]
    intro ha hb
    apply Quotient.eq_iff_equiv.mpr
    change a + d = b + c
    linarith

  le_total := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩
    simp[le_quotient_int, le_nat_pair]
    exact Nat.le_total (a + d) (c + b)

  lt_iff_le_not_ge := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩
    simp[lt_quotient_int, le_quotient_int, lt_nat_pair, le_nat_pair]
    intro h
    exact Nat.le_of_succ_le h


lemma quotient_int_of_natAbs (x : QuotientInt) (h : 0 ≤ x) :
    quotient_int_ofNat (quotient_int_natAbs x) = x := by
      revert h
      refine Quotient.inductionOn x ?_
      intro ⟨a, b⟩ hx
      change le_quotient_int ⟦⟨0, 0⟩⟧ ⟦⟨a, b⟩⟧ at hx
      simp[le_quotient_int, le_nat_pair] at hx

      apply Quotient.eq_iff_equiv.mpr
      simp [abs_nat_pair, quotient_int_natAbs, hx]
      change a - b + b = 0 + a
      simp[Nat.sub_add_cancel, hx]

instance : CommRing QuotientInt where
  zero := ⟦⟨0, 0⟩⟧
  one := ⟦⟨1, 0⟩⟧

  nsmul := fun n x ↦ mul_quotient_int (quotient_int_ofNat n) x
  nsmul_zero := by
    intro x
    simp[mul_quotient_int, quotient_int_ofNat]
    refine Quotient.inductionOn x  ?_
    intro ⟨a, b⟩
    simp[mul_nat_pair]
    rfl

  nsmul_succ := by
    intro n x
    simp[mul_quotient_int, quotient_int_ofNat]
    refine Quotient.inductionOn x  ?_
    intro ⟨a, b⟩
    simp[mul_nat_pair]
    change _ = add_quotient_int ⟦⟨n * a, n * b⟩⟧ ⟦⟨a, b⟩⟧
    simp[add_quotient_int, add_nat_pair]
    congr
    <;> simp[right_distrib]

  zsmul := fun z x ↦ mul_quotient_int z x
  zsmul_zero' := by
    intro x
    simp
    change mul_quotient_int 0 x = 0
    convert quotient_int_mul_zero x using 1
    exact quotient_int_mul_comm _ _
  zsmul_succ' := by
    intro n x
    simp[mul_quotient_int]
    refine Quotient.inductionOn x  ?_
    intro ⟨a, b⟩
    simp[mul_nat_pair]
    change _ = add_quotient_int ⟦⟨n * a, n * b⟩⟧ ⟦⟨a, b⟩⟧
    simp[add_quotient_int, add_nat_pair]
    congr
    <;> simp[right_distrib]
  zsmul_neg' := by
    intro a x
    simp[mul_quotient_int, neg_quotient_int]
    refine Quotient.inductionOn x  ?_
    intro ⟨a, b⟩
    simp[mul_nat_pair]



  add := add_quotient_int
  add_comm := quotient_int_add_comm


  add_assoc := by
    intro x y z
    change add_quotient_int (add_quotient_int x y) z = add_quotient_int x (add_quotient_int y z)
    simp[add_quotient_int]
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    simp[add_nat_pair]
    conv => lhs; simp[add_assoc]

  add_zero := quotient_int_add_zero

  zero_add := by
    convert quotient_int_add_zero using 2
    exact quotient_int_add_comm _ _

  mul := mul_quotient_int
  mul_comm := quotient_int_mul_comm
  mul_one := quotient_int_mul_one
  mul_zero := quotient_int_mul_zero

  zero_mul := by
    convert quotient_int_mul_zero using 2
    exact quotient_int_mul_comm _ _

  one_mul := by
    convert quotient_int_mul_one using 2
    exact quotient_int_mul_comm _ _


  mul_assoc := by
    intro x y z
    change mul_quotient_int (mul_quotient_int x y) z = mul_quotient_int x (mul_quotient_int y z)
    simp[mul_quotient_int]
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    simp only [Quotient.map₂_mk, mul_nat_pair]
    congr 2
    <;> ring

  left_distrib := quotient_int_left_distrib
  right_distrib := quotient_int_right_distrib

  neg := neg_quotient_int

  neg_add_cancel := by
    intro x
    change add_quotient_int (neg_quotient_int x) x = ⟦⟨0, 0⟩⟧
    simp[neg_quotient_int, add_quotient_int]
    refine Quotient.inductionOn x ?_
    intro ⟨a, b⟩
    simp[add_nat_pair]
    apply Quotient.eq_iff_equiv.mpr
    change b + a + 0 = a + b + 0
    ring

instance : IsStrictOrderedRing QuotientInt where
  exists_pair_ne := by
    use mkQuotientInt ⟨0, 0⟩
    use mkQuotientInt ⟨1, 0⟩
    simp[mkQuotientInt]
    intro h
    have := by exact Quotient.eq_iff_equiv.mp h
    change 0 + 0 = 1 + 0 at this
    linarith

  add_le_add_left := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a, b⟩ ⟨c, d⟩
    intro hxy z
    refine Quotient.inductionOn z ?_
    intro ⟨e, f⟩
    change le_quotient_int ⟦⟨a, b⟩⟧ ⟦⟨c, d⟩⟧ at hxy
    change le_quotient_int (add_quotient_int ⟦⟨e, f⟩⟧  ⟦⟨a, b⟩⟧) (add_quotient_int ⟦⟨e, f⟩⟧ ⟦⟨c, d⟩⟧)
    simp_all [le_quotient_int, add_quotient_int, le_nat_pair, add_nat_pair]
    linarith

  zero_le_one := by
    change le_quotient_int ⟦⟨0, 0⟩⟧ ⟦⟨1, 0⟩⟧
    simp[le_quotient_int, le_nat_pair]

  le_of_add_le_add_left := by
    intro x y z
    change le_quotient_int (add_quotient_int x y) (add_quotient_int x z) → le_quotient_int y z
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    simp[le_quotient_int, le_nat_pair, add_quotient_int, add_nat_pair]
    intro h
    linarith

  mul_lt_mul_of_pos_right := quotient_int_mul_lt_of_pos_right

  mul_lt_mul_of_pos_left := by
    intro x y z
    convert quotient_int_mul_lt_of_pos_right x y z using 3
    . change mul_quotient_int z x = _
      rw[quotient_int_mul_comm]
    . change mul_quotient_int z y = _
      rw[quotient_int_mul_comm]

def QuotientIntEquivInt : QuotientInt ≃+*o ℤ := {
    toFun := by
      intro x
      refine x.lift int_nat_pair ?_
      intro ⟨a, b⟩ ⟨c, d⟩
      intro hab
      simp[int_nat_pair]
      change a + d = b + c at hab
      linarith

    invFun := coeZQuotientInt
    right_inv := by
      intro x
      match h : x with
      | Int.ofNat n | Int.negSucc n =>
        simp[int_nat_pair, Int.negSucc_eq]

    left_inv := by
      intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a, b⟩
      simp[int_nat_pair]
      match h : (↑a - ↑b : ℤ) with
      | Int.ofNat n =>
        simp[h]
        apply Quotient.eq_iff_equiv.mpr
        change n + b = 0 + a
        zify
        simp at h
        rw[←h]
        ring
      | Int.negSucc n =>
        simp[h]
        apply Quotient.eq_iff_equiv.mpr
        change 0 + b = n + 1 + a
        zify
        simp[Int.negSucc_eq] at h
        linarith

    map_mul' := by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro ⟨a, b⟩ ⟨c, d⟩
      change Quotient.lift int_nat_pair _ (mul_quotient_int ⟦⟨a, b⟩⟧ ⟦⟨c, d⟩⟧) = _
      simp[int_nat_pair, mul_quotient_int, mul_nat_pair]
      ring

    map_add' := by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro ⟨a, b⟩ ⟨c, d⟩
      change Quotient.lift int_nat_pair _ (add_quotient_int ⟦⟨a, b⟩⟧ ⟦⟨c, d⟩⟧) = _
      simp[int_nat_pair, add_quotient_int, add_nat_pair]
      ring

    map_le_map_iff' := by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro ⟨a, b⟩ ⟨c, d⟩
      change _ ↔ le_quotient_int ⟦⟨a, b⟩⟧ ⟦⟨c, d⟩⟧
      simp[int_nat_pair, le_quotient_int, le_nat_pair]
      rw[←Int.add_le_add_iff_right (c := d)]
      ring_nf
      zify
}


instance : IsInteger QuotientInt where
  ofNat := quotient_int_ofNat
  intEquiv := QuotientIntEquivInt

  nonneg_well_ordered := by
    refine {
      toIsTrichotomous := instIsTrichotomousLt,
      toIsTrans := instIsTransLt,
      toIsWellFounded := {
        wf := WellFounded.intro fun a => ?_
      }
    }

    apply (measure fun (z : {z : QuotientInt | z ≥ 0}) ↦ quotient_int_natAbs z.val).wf.induction

    intro ⟨x, hx⟩ hI
    constructor
    intro ⟨y, hy⟩
    convert hI ⟨y, hy⟩ using 1
    change x ≥ 0 at hx
    change y ≥ 0 at hy

    change y < x ↔ quotient_int_natAbs y < quotient_int_natAbs x
    revert hx
    revert hy
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨c, d⟩ ⟨a, b⟩
    intro hx hy _
    clear * - hx hy

    change le_quotient_int ⟦⟨0, 0⟩⟧ ⟦⟨a, b⟩⟧ at hx
    change le_quotient_int ⟦⟨0, 0⟩⟧ ⟦⟨c, d⟩⟧ at hy
    change lt_quotient_int ⟦⟨a, b⟩⟧ ⟦⟨c, d⟩⟧ ↔ _

    simp_all[quotient_int_natAbs, abs_nat_pair, le_quotient_int, le_nat_pair, lt_quotient_int, lt_nat_pair]
    constructor
    . intro hmp
      rw[←Nat.add_lt_add_iff_right (n := a - b) (m := c - d) (k := b + d)]
      ac_change a - b + b + d < c - d + d + b
      simp[hx, hy]
      exact hmp
    . intro hmpr
      rw[←Nat.add_lt_add_iff_right (n := a - b) (m := c - d) (k := b + d)] at hmpr
      convert hmpr using 1
      . ac_change _ = a - b + b + d
        simp[hx]
      . ac_change _ = c - d + d + b
        simp[hy]
