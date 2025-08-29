import Morphisms.Integers
import Mathlib

open Lean Elab Tactic

def digitsWithFuel (base num fuel : Nat) : List Nat :=
  match num, fuel with
  | 0, _ => []
  | _, 0 => []
  | m + 1, n => n % base :: digitsWithFuel base m (n / base)


def digits (base n : Nat) : List Nat := (digitsWithFuel base n n).reverse

def hammingWeight (n : Nat) : Nat := (digits 2 n).sum

def fromDigits (base : Nat) (digits : List Nat) : Nat :=
  digits.foldl (λ acc digit => acc * base + digit) 0


def concat (x y : ℕ) : Nat :=
  fromDigits 10 ((digits 10 x) ++ (digits 10 y))

def signedConcat : (x y : ℤ) → ℤ
| Int.ofNat a, Int.ofNat b => Int.ofNat (fromDigits 10 ((digits 10 a) ++ (digits 10 b)))
| Int.negSucc a, Int.negSucc b => Int.ofNat (fromDigits 10 ((digits 10 (Nat.succ a)) ++ (digits 10 (Nat.succ b))))
| Int.negSucc a, Int.ofNat b => -Int.ofNat (fromDigits 10 ((digits 10 (Nat.succ a)) ++ (digits 10 (b))))
| Int.ofNat a, Int.negSucc b => -Int.ofNat (fromDigits 10 ((digits 10 (a)) ++ (digits 10 (Nat.succ b))))

def lastDigitWord (x : IntLike) : String :=
  match (digits 10 (x.val.natAbs)).getLast? with
  | some digit => match digit with
     | 0 => "zero" -- zero
     | 1 => "one" -- one
     | 2 => "two" -- two
     | 3 => "three" -- three
     | 4 => "four" -- four
     | 5 => "five" -- five
     | 6 => "six" -- six
     | 7 => "seven" -- seven
     | 8 => "eight" -- eight
     | 9 => "nine" -- nine
     | _ => "zero"
  | none => "zero"


def isEven (x : ℤ) : Prop := x % 2 = 0

theorem countDigits_add_of_lastDigitsOne (x y : IntLike)
   (hx : lastDigitWord x = "one") (hy : lastDigitWord y = "one") : lastDigitWord (x + y) = "two" := by
     simp_all [lastDigitWord]

     have : (digits 10 x.val.natAbs).getLast? = some 1 := by
       by_contra h
       have : lastDigitWord x ≠ "one" := by
        simp[lastDigitWord, h]



#eval lastDigitWordCount (34 : IntLike)
--theorem concatEven (x y : ℤ) (hy : isEven x) : isEven (signedConcat x y) := by
  --unfold signedConcat fromDigits



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

