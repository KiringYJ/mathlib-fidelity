/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module

public import Mathlib.Init
public import Lean.ToExpr

/-!
# Additional operations on Expr and rational numbers

This file defines some operations involving `Expr` and rational numbers.

## Main definitions

* `Lean.Expr.isExplicitNumber`: is an expression a number in normal form?
  This includes natural numbers, integers and rationals.
-/

public section

namespace Lean.Expr

/--
Check if an expression is a "rational in normal form",
i.e. either an integer number in normal form,
or `n / d` where `n` is an integer in normal form, `d` is a natural number in normal form,
`d ≠ 0`, `d ≠ 1`, and `n` and `d` are coprime (normalization preserves `d`).
If so returns the rational number.

This is syntactic recognition, including the generic `Div.div` syntax; it does not evaluate the
selected division instance. Proof-producing callers must validate that instance and certify the
recognized value.
-/
def rat? (e : Expr) : Option Rat := do
  let args := e.getAppArgs
  let fraction? :=
    if e.isAppOfArity ``Div.div 4 then some (args[2]!, args[3]!)
    else if e.isAppOfArity `Checked.div 5 then some (args[2]!, args[3]!)
    else none
  if let some (numerator, denominator) := fraction? then
    let d ← denominator.nat?
    guard (d ≠ 1)
    let n ← numerator.int?
    let q ← if hd : d ≠ 0 then pure (Rat.normalize n d hd) else none
    guard (q.den = d)
    pure q
  else
    e.int?

/--
Test if an expression represents an explicit number written in normal form:
* A "natural number in normal form" is an expression `OfNat.ofNat n`, even if it is not of type `ℕ`,
  as long as `n` is a literal.
* An "integer in normal form" is an expression which is either a natural number in number form,
  or `-n`, where `n` is a natural number in normal form.
* A "rational in normal form" is an expressions which is either an integer in normal form,
  or `n / d` where `n` is an integer in normal form, `d` is a natural number in normal form,
  `d ≠ 0`, `d ≠ 1`, and `n` and `d` are coprime (normalization preserves `d`).
-/
def isExplicitNumber : Expr → Bool
  | .lit _ => true
  | .mdata _ e => isExplicitNumber e
  | e => e.rat?.isSome

end Lean.Expr
