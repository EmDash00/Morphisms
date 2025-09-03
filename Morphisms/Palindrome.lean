import Mathlib

/-
Maps a Nat `n` to a palindrome with the number of characters equal to `n % 10`.
-/
def palindrome_map (x : ℕ) : String := by
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
  . exact "deleveled"

/-
Maps an Int `z` to a palindrome with the number of characters equal to `|z| % 10`.
Negative inputs are reversed.
-/
def palindrome_map_int : (x : ℤ) → String
| Int.ofNat n => palindrome_map n
| Int.negSucc n => String.mk (palindrome_map (Nat.succ n)).data.reverse

def isPalindrome (str: String) : Prop := str.data = str.data.reverse

@[simp]
lemma palindrome_map_zero : palindrome_map 0 = "" := by
  unfold palindrome_map
  simp [Mathlib.Tactic.ModCases.NatMod.onModCases_succ, Mathlib.Tactic.ModCases.NatMod.onModCases_start]
  split
  rfl

/-
Negating the input reverses the output.
-/
theorem neg_reverse (z : ℤ) : (palindrome_map_int z).data = (palindrome_map_int (-z)).data.reverse := by
  unfold palindrome_map_int
  match z with
  | Int.ofNat n =>
    match n with
    | Nat.zero =>
      simp only [Nat.zero_eq, Int.ofNat_eq_coe, CharP.cast_eq_zero, neg_zero]
      simp only [palindrome_map_zero, List.reverse_nil]
    | Nat.succ n =>
      simp only[←Int.negOfNat_eq, Int.negOfNat, List.reverse_reverse]
  | Int.negSucc n =>
    match n with
    | _ => norm_cast

/-
If you concatenate palindrome_map_int (z) with palindrome_map_int (-z), you will always get a palindrome.
-/
theorem neg_concat_isPalindrome (z : ℤ) : isPalindrome (String.mk ((palindrome_map_int z).data ++ (palindrome_map_int (-z)).data)) := by
  unfold isPalindrome

  match h : z with
  | Int.ofNat n =>
    match n with
    | Nat.zero =>
      unfold palindrome_map_int
      simp only [Nat.zero_eq, palindrome_map_zero, Int.ofNat_eq_coe, CharP.cast_eq_zero, neg_zero,
        List.append_nil, List.reverse_nil]
    | Nat.succ n =>
      unfold palindrome_map_int
      simp only[←Int.negOfNat_eq, Int.negOfNat, List.reverse_append, List.reverse_reverse]
  | Int.negSucc n =>
    match n with
    | Nat.zero =>
      unfold palindrome_map_int
      simp only [Nat.zero_eq, Nat.succ_eq_add_one, zero_add, Int.reduceNegSucc, neg_neg,
        List.reverse_append, List.reverse_reverse]
      --simp only[List.reverse_append, List.reverse_reverse]
    | Nat.succ n =>
      unfold palindrome_map_int
      simp
      norm_cast
