/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw, Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

public meta import Mathlib.Algebra.Field.Basic
public meta import Mathlib.Data.Ineq
public import Mathlib.Tactic.FieldSimp.Attr
public import Mathlib.Tactic.FieldSimp.Discharger
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Util.AtomM.Recurse
public import Mathlib.Util.SynthesizeUsing
public import Mathlib.Data.Ineq

/-!
# Clearing denominators with invertibility certificates

The normal form is a numerator and a unit denominator. Every recursive step produces an equality
certificate. An inverse transfers its original unit evidence to the normalized numerator before
reversing the fraction. Products of natural powers are collected in atom order. Factoring the two
sides exposes common factors in sums, fractions, and comparisons. A factor can be canceled from
an equality when it is a unit and from an inequality when it is positive.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.FieldSimp

initialize registerTraceClass `Tactic.field_simp

variable {level : Level} {M : Q(Type level)}

/-- A fraction together with the equality certifying its value. -/
structure Normalized (iM : Q(CommGroupWithZero $M)) (e : Q($M)) where
  /-- The numerator. -/
  numerator : Q($M)
  /-- An invertible denominator, carrying both inverse laws. -/
  denominator : Q($Mˣ)
  /-- The normalization certificate. -/
  eqProof : Q($e = $numerator /ₚ $denominator)
  /-- Whether the expression contains a quotient, inverse, or literal checked integer power. -/
  changed : Bool

private def atom (iM : Q(CommGroupWithZero $M)) (e : Q($M)) : Normalized iM e :=
  ⟨e, q(1), q(normalize_atom $e), false⟩

/-- Erase unit-witness bookkeeping from the displayed arithmetic while retaining its proof. -/
private def simplifyWitnesses (r : Simp.Result) : MetaM Simp.Result := do
  r.mkEqTrans (← simpOnlyNames [``Units.val_mul, ``Units.val_one,
    ``Units.val_pow_eq_pow_val, ``numeratorUnit_val, ``mul_one, ``one_mul, ``divp_one,
    ``div_one₀] r.expr)

/-- Preserve source atom order before cross multiplication interleaves the two fractions. -/
private partial def indexFactors (iM : Q(CommGroupWithZero $M)) (e : Q($M)) : AtomM Unit := do
  match e with
  | ~q($a * $b) => indexFactors iM a; indexFactors iM b
  | ~q($a ^ ($k : ℕ)) =>
    if (← getNatValue? k).isSome then indexFactors iM a else discard <| AtomM.addAtomQ e
  | _ =>
    if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
      indexFactors iM e.getAppArgs[4]!
      indexFactors iM e.getAppArgs[5]!
    discard <| AtomM.addAtomQ e

/-- Normalize a field expression while retaining the original denominator certificates. -/
partial def normalize (iM : Q(CommGroupWithZero $M)) (e : Q($M)) :
    AtomM (Normalized iM e) := do
  match e with
  | ~q(Checked.div $a $b $hb) =>
    -- Record the original numerator and denominator before cross multiplication reorders them.
    indexFactors iM a
    indexFactors iM b
    let ⟨na, u, pa, _⟩ ← normalize iM a
    let ⟨nb, v, pb, _⟩ ← normalize iM b
    return ⟨q($na * ($v : $M)), q($u * numeratorUnit $b $nb $v $hb $pb),
      q(normalize_div $hb $pa $pb), true⟩
  | ~q(Checked.inv $a $ha) =>
    let ⟨n, u, p, _⟩ ← normalize iM a
    return ⟨q(($u : $M)), q(numeratorUnit $a $n $u $ha $p),
      q(normalize_inv $ha $p), true⟩
  | ~q($a /ₚ $w) =>
    let ⟨na, u, pa, _⟩ ← normalize iM a
    have b : Q($M) := q(($w : $M))
    haveI' : $b =Q ($w : $M) := ⟨⟩
    let ⟨nb, v, pb, _⟩ ← normalize iM b
    return ⟨q($na * ($v : $M)), q($u * numeratorUnit $b $nb $v (Units.isUnit $w) $pb),
      q(normalize_divp $pa $pb), true⟩
  | ~q(Checked.zpow $a $r $ha) =>
    let some k := r.int? | return atom iM e
    let ⟨n, u, p, _⟩ ← normalize iM a
    match k with
    | .ofNat k =>
      have k : Q(ℕ) := mkRawNatLit k
      haveI' : $r =Q Int.ofNat $k := ⟨⟩
      return ⟨q($n ^ $k), q($u ^ $k),
        q(Eq.trans (zpow_natCast₀ $a $k) (normalize_pow $p $k)), true⟩
    | .negSucc k =>
      have j : Q(ℕ) := mkRawNatLit (k + 1)
      have k : Q(ℕ) := mkRawNatLit k
      haveI' : $r =Q Int.negSucc $k := ⟨⟩
      have hinv : Q(IsUnit $a) := q($ha (Int.negSucc_lt_zero $k))
      have ni : Q($M) := q(($u : $M))
      have ui : Q($Mˣ) := q(numeratorUnit $a $n $u $hinv $p)
      haveI' : $ni =Q ($u : $M) := ⟨⟩
      haveI' : $ui =Q numeratorUnit $a $n $u $hinv $p := ⟨⟩
      have pi : Q(Checked.inv $a $hinv = $ni /ₚ $ui) := q(normalize_inv $hinv $p)
      haveI' : $j =Q $k + 1 := ⟨⟩
      return ⟨q($ni ^ $j), q($ui ^ $j),
        q(Eq.trans (checked_zpow_negSucc $a $k $ha) (normalize_pow $pi $j)), true⟩
  | ~q($a * $b) =>
    let ⟨na, u, pa, ca⟩ ← normalize iM a
    let ⟨nb, v, pb, cb⟩ ← normalize iM b
    if !ca && !cb then return atom iM e
    return ⟨q($na * $nb), q($u * $v), q(normalize_mul $pa $pb), true⟩
  | ~q($a ^ ($k : ℕ)) =>
    let ⟨n, u, p, c⟩ ← normalize iM a
    if !c then return atom iM e
    return ⟨q($n ^ $k), q($u ^ $k), q(normalize_pow $p $k), true⟩
  | _ =>
    let args := e.getAppArgs
    let fn := e.getAppFn
    if fn.isConstOf ``HAdd.hAdd && args.size == 6 then
      -- Without a compatible commutative semiring structure, the sum is an atom.
      let .some _sM ← trySynthInstanceQ q(CommSemiring $M) | return atom iM e
      have a : Q($M) := args[4]!
      have b : Q($M) := args[5]!
      assertInstancesCommute
      unless ← isDefEq e q($a + $b) do return atom iM e
      haveI' : $e =Q $a + $b := ⟨⟩
      let ⟨na, u, pa, ca⟩ ← normalize iM a
      let ⟨nb, v, pb, cb⟩ ← normalize iM b
      if !ca && !cb then return atom iM e
      let p ← mkAppM ``normalize_add #[pa, pb]
      return ⟨q($na * ($v : $M) + $nb * ($u : $M)), q($u * $v),
        p, true⟩
    else if fn.isConstOf ``HSub.hSub && args.size == 6 then
      -- A subtraction that is not ring subtraction, such as truncated subtraction in `ℝ≥0`, is an
      -- atom.
      let .some _rM ← trySynthInstanceQ q(CommRing $M) | return atom iM e
      have a : Q($M) := args[4]!
      have b : Q($M) := args[5]!
      assertInstancesCommute
      unless ← isDefEq e q($a - $b) do return atom iM e
      haveI' : $e =Q $a - $b := ⟨⟩
      let ⟨na, u, pa, ca⟩ ← normalize iM a
      let ⟨nb, v, pb, cb⟩ ← normalize iM b
      if !ca && !cb then return atom iM e
      let p ← mkAppM ``normalize_sub #[pa, pb]
      return ⟨q($na * ($v : $M) - $nb * ($u : $M)), q($u * $v),
        p, true⟩
    else if fn.isConstOf ``Neg.neg && args.size == 3 then
      let .some _rM ← trySynthInstanceQ q(Ring $M) | return atom iM e
      have a : Q($M) := args[2]!
      assertInstancesCommute
      unless ← isDefEq e q(-$a) do return atom iM e
      haveI' : $e =Q -$a := ⟨⟩
      let ⟨n, u, p, c⟩ ← normalize iM a
      if !c then return atom iM e
      let p ← mkAppM ``normalize_neg #[p]
      return ⟨q(-$n), u, p, true⟩
    else
      return atom iM e

/-- A factor has a positive natural exponent and the index assigned to its base by `AtomM`. -/
private structure Power (M : Q(Type level)) where
  base : Q($M)
  index : Nat
  degree : Nat

private abbrev Factors (M : Q(Type level)) := List (Power M)

private def Power.expr (iM : Q(CommGroupWithZero $M)) (p : Power M) : Q($M) :=
  let base := p.base
  let k : Q(ℕ) := mkRawNatLit p.degree
  q($base ^ $k)

private def product (iM : Q(CommGroupWithZero $M)) : Factors M → Q($M)
  | [] => q(1)
  | p :: ps => q($(p.expr iM) * $(product iM ps))

/-- Merge two sorted factorizations and certify the multiplication. Matching indices have
definitionally equal bases, including when two terms use different unit proofs. -/
private partial def multiplyFactors (iM : Q(CommGroupWithZero $M)) (xs ys : Factors M) :
    MetaM (Factors M × Expr) := do
  match xs, ys with
  | [], _ => return (ys, q(one_mul $(product iM ys)))
  | _, [] => return (xs, q(mul_one $(product iM xs)))
  | x :: xt, y :: yt =>
    if x.index < y.index then
      let (zs, h) ← multiplyFactors iM xt ys
      return (x :: zs, ← mkAppM ``collect_mul_left #[x.expr iM, h])
    else if y.index < x.index then
      let (zs, h) ← multiplyFactors iM xs yt
      return (y :: zs, ← mkAppM ``collect_mul_right #[y.expr iM, h])
    else
      let (zs, h) ← multiplyFactors iM xt yt
      let p ← mkAppM ``collect_mul_pow #[x.base, mkRawNatLit x.degree, mkRawNatLit y.degree, h]
      return ({x with degree := x.degree + y.degree} :: zs, p)

private def raiseFactors (iM : Q(CommGroupWithZero $M)) (k : Nat) :
    Factors M → MetaM (Factors M × Expr)
  | [] => do
    have degree : Q(ℕ) := mkRawNatLit k
    return ([], q(one_pow $degree : (1 : $M) ^ $degree = 1))
  | x :: xt => do
    if k == 0 then return ([], q(pow_zero $(product iM (x :: xt))))
    let (zs, h) ← raiseFactors iM k xt
    let p ← mkAppM ``collect_pow #[x.base, mkRawNatLit x.degree, mkRawNatLit k, h]
    return ({x with degree := x.degree * k} :: zs, p)

/-- Split two products into their coprime remnants and common factors. -/
private partial def splitFactors : Factors M → Factors M → Factors M × Factors M × Factors M
  | [], ys => ([], ys, [])
  | xs, [] => (xs, [], [])
  | x :: xt, y :: yt =>
    if x.index < y.index then
      let (a, b, c) := splitFactors xt (y :: yt)
      (x :: a, b, c)
    else if y.index < x.index then
      let (a, b, c) := splitFactors (x :: xt) yt
      (a, y :: b, c)
    else
      let (a, b, c) := splitFactors xt yt
      let k := min x.degree y.degree
      (if k < x.degree then {x with degree := x.degree - k} :: a else a,
       if k < y.degree then {y with degree := y.degree - k} :: b else b,
       {x with degree := k} :: c)

private def collectAtom (iM : Q(CommGroupWithZero $M)) (e : Q($M)) (visit := true) :
    AtomM (Factors M × Expr) := do
  let r ← if visit then (← read).evalAtom e else pure { expr := e }
  have a : Q($M) := r.expr
  let (index, ⟨base, _⟩) ← AtomM.addAtomQ a
  have ha : Q($e = $base) := ← r.getProof
  return ([⟨base, index, 1⟩], q(($ha).trans (collect_atom $base)))

/-- Simplify the displayed product, preserving its equality to the collected factorization. -/
private def prettyProduct (iM : Q(CommGroupWithZero $M)) (xs : Factors M) : MetaM Simp.Result :=
  simpOnlyNames [``pow_one, ``mul_one, ``one_mul] (product iM xs)

private def factorProof (iM : Q(CommGroupWithZero $M)) (xs c : Factors M) (h : Expr) :
    MetaM Expr := do
  let (_, join) ← multiplyFactors iM xs c
  let h ← mkAppM ``Eq.trans #[h, ← mkAppM ``Eq.symm #[join]]
  let r ← prettyProduct iM xs
  have a : Q($M) := r.expr
  have ha : Q($(product iM xs) = $a) := ← r.getProof
  mkAppM ``Eq.trans #[h, q(congrArg (· * $(product iM c)) $ha)]

/-- Keep the residual sum as one atom after extracting the product common to both summands. -/
private def collectSum (iM : Q(CommGroupWithZero $M)) (xs ys : Factors M) (ha hb : Expr)
    (factorLemma : Name) : AtomM (Factors M × Expr) := do
  let (a, b, c) := splitFactors xs ys
  let ha ← factorProof iM a c ha
  let hb ← factorProof iM b c hb
  let p ← mkAppM factorLemma #[ha, hb]
  -- The right side is the residual sum multiplied by the common product.
  have rhs : Q($M) := (← inferType p).appArg!
  unless rhs.isAppOfArity ``HMul.hMul 6 do
    throwError "expected a product in the factorization certificate"
  have sum : Q($M) := rhs.getAppArgs[4]!
  let (terms, hsum) ← collectAtom iM sum false
  let (zs, hmul) ← multiplyFactors iM terms c
  have hsum : Q($sum = $(product iM terms)) := hsum
  let h ← mkAppM ``Eq.trans #[p, q(congrArg (· * $(product iM c)) $hsum)]
  return (zs, ← mkAppM ``Eq.trans #[h, hmul])

private partial def collectFactors (iM : Q(CommGroupWithZero $M)) (e : Q($M)) :
    AtomM (Factors M × Expr) := do
  match e with
  | ~q(1) => return ([], ← mkEqRefl e)
  | ~q($a * $b) =>
    let (xs, ha) ← collectFactors iM a
    let (ys, hb) ← collectFactors iM b
    let (zs, hm) ← multiplyFactors iM xs ys
    have ha : Q($a = $(product iM xs)) := ha
    have hb : Q($b = $(product iM ys)) := hb
    have hm : Q($(product iM xs) * $(product iM ys) = $(product iM zs)) := hm
    return (zs, q((congrArg₂ HMul.hMul $ha $hb).trans $hm))
  | ~q($a ^ ($k : ℕ)) =>
    if let some degree := (← getNatValue? k) then
      let (xs, ha) ← collectFactors iM a
      let (zs, hpow) ← raiseFactors iM degree xs
      have ha : Q($a = $(product iM xs)) := ha
      have hpow : Q($(product iM xs) ^ $k = $(product iM zs)) := hpow
      return (zs, q((congrArg (· ^ $k) $ha).trans $hpow))
    else
      collectAtom iM e
  | _ =>
    let args := e.getAppArgs
    if e.isAppOfArity ``HAdd.hAdd 6 then
      if let .some _sM ← trySynthInstanceQ q(CommSemiring $M) then
        have a : Q($M) := args[4]!
        have b : Q($M) := args[5]!
        assertInstancesCommute
        if ← isDefEq e q($a + $b) then
          let (xs, ha) ← collectFactors iM a
          let (ys, hb) ← collectFactors iM b
          return ← collectSum iM xs ys ha hb ``collect_add
    if e.isAppOfArity ``HSub.hSub 6 then
      if let .some _rM ← trySynthInstanceQ q(CommRing $M) then
        have a : Q($M) := args[4]!
        have b : Q($M) := args[5]!
        assertInstancesCommute
        if ← isDefEq e q($a - $b) then
          let (xs, ha) ← collectFactors iM a
          let (ys, hb) ← collectFactors iM b
          return ← collectSum iM xs ys ha hb ``collect_sub
    if e.isAppOfArity ``Neg.neg 3 then
      if let .some _rM ← trySynthInstanceQ q(CommRing $M) then
        have a : Q($M) := args[2]!
        assertInstancesCommute
        if ← isDefEq e q(-$a) then
          let (xs, ha) ← collectFactors iM a
          let (ys, hb) ← collectAtom iM q(-1) false
          let (zs, hmul) ← multiplyFactors iM ys xs
          have hb : Q((-1 : $M) = $(product iM ys)) := hb
          let p ← mkAppM ``collect_neg #[ha]
          let h ← mkAppM ``Eq.trans #[p, q(congrArg (· * $(product iM xs)) $hb)]
          return (zs, ← mkAppM ``Eq.trans #[h, hmul])
    collectAtom iM e

/-- Rewrite a field expression as a certified fraction. -/
def reduceExpr (_disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (e : Expr) : AtomM Simp.Result := do
  let ⟨_, M, e⟩ ← inferTypeQ' e
  let iM : Q(CommGroupWithZero $M) ← synthInstanceQ q(CommGroupWithZero $M)
  let ⟨n, d, p, changed⟩ ← normalize iM e
  let isProduct := e.isAppOf ``HMul.hMul || e.isAppOf ``HPow.hPow
  unless changed || isProduct || e.isAppOf ``HAdd.hAdd || e.isAppOf ``HSub.hSub ||
      e.isAppOf ``Neg.neg do failure
  let sn ← simplifyWitnesses { expr := n }
  have dv : Q($M) := q(($d : $M))
  let sd ← simplifyWitnesses { expr := dv }
  let (xs, hn) ← collectFactors iM sn.expr
  let (ys, hd) ← collectFactors iM sd.expr
  let (a, b, common) := splitFactors xs ys
  let hn ← factorProof iM a common (← mkAppM ``Eq.trans #[← sn.getProof, hn])
  let hd ← factorProof iM b common (← mkAppM ``Eq.trans #[← sd.getProof, hd])
  let proof ← mkAppM ``display_reduced #[p, hn, hd]
  let result ← simplifyWitnesses { expr := (← inferType proof).appArg!, proof? := some proof }
  let result ← result.mkEqTrans (← simpOnlyNames [``display_mul_assoc, ``neg_one_mul,
    ``mul_neg_one, ``neg_div₀, ``div_neg₀,
    ``neg_neg, ``neg_one_sq]
    result.expr)
  unless changed || isProduct || !e.isAppOf ``HAdd.hAdd ||
      !(← withReducible <| isDefEq result.expr e) do failure
  return result

/-- Extract the unit proofs for the atoms of a certified denominator. -/
private def denominatorUnits (iM : Q(CommGroupWithZero $M)) (u : Q($Mˣ)) :
    AtomM (List (Nat × Expr)) := do
  let r ← simplifyWitnesses { expr := q(($u : $M)) }
  let (xs, p) ← collectFactors iM r.expr
  let h ← mkAppM ``Eq.trans #[← r.getProof, p]
  have h : Q(($u : $M) = $(product iM xs)) := h
  let mut units := []
  let mut unitProof : Expr := q($h ▸ Units.isUnit $u)
  for tail in xs.tails do
    if let x :: rest := tail then
      let hx ← mkAppM ``unit_of_power_factor
        #[x.base, product iM rest, mkRawNatLit (x.degree - 1), unitProof]
      units := (x.index, hx) :: units
      unitProof ← mkAppM ``isUnit_of_mul_isUnit_right #[unitProof]
  return units

private def cancellablePower (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (x : Power M) (forEquality : Bool) (units : List (Nat × Expr)) :
    MetaM (Option (Nat × Expr)) := do
  let base := x.base
  let getUnit : MetaM Expr := do
    if let some h := units.lookup x.index then return h
    try disch q(IsUnit $base) catch _ =>
      let h ← disch q($base ≠ 0)
      return q(($h).isUnit)
  observing? do
    if forEquality then
      let h ← getUnit
      return (x.degree, ← mkAppM ``IsUnit.pow #[mkRawNatLit x.degree, h])
    let _poM ← synthInstanceQ q(PartialOrder $M)
    try
      let h ← disch q(0 < $(x.expr iM))
      return (x.degree, h)
    catch _ =>
      let k := x.degree / 2
      guard (k != 0)
      let h ← getUnit
      return (2 * k, ← mkAppM ``unit_even_power_pos #[h, mkRawNatLit k])

private def cancelComparisonFactors (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (t : Expr) (units : List (Nat × Expr)) : AtomM Simp.Result := do
  let ⟨rel, _, a, b⟩ ← t.ineq?
  let ⟨_, M, a⟩ ← inferTypeQ' a
  have b : Q($M) := b
  let iM : Q(CommGroupWithZero $M) ← synthInstanceQ q(CommGroupWithZero $M)
  let (xs, ha) ← collectFactors iM a
  let (ys, hb) ← collectFactors iM b
  let (left, right, common) := splitFactors xs ys
  let mut factors := []
  let mut retained := []
  let mut proofs := []
  for x in common do
    let factor? ← cancellablePower disch iM x (rel == .eq) units
    if let some (degree, proof) := factor? then
      factors := {x with degree} :: factors
      proofs := proof :: proofs
      if degree < x.degree then retained := {x with degree := x.degree - degree} :: retained
    else
      retained := x :: retained
  let plain : MetaM Simp.Result := do
    let left ← (← prettyProduct iM xs).getProof
    let right ← (← prettyProduct iM ys).getProof
    let hleft ← mkAppM ``Eq.trans #[ha, left]
    let hright ← mkAppM ``Eq.trans #[hb, right]
    let .app (.app comparison _) _ ← whnfR (← instantiateMVars t) | failure
    let p ← mkAppM ``congrArg₂ #[comparison, hleft, hright]
    let r : Simp.Result := { expr := (← inferType p).appArg!, proof? := some p }
    return ← r.mkEqTrans
      (← simpOnlyNames [``display_mul_assoc, ``neg_one_mul, ``mul_neg_one] r.expr)
  let last :: rest := proofs | return ← plain
  let lemmaName := match rel with
    | .eq => ``cancel_common_eq | .le => ``cancel_common_le | .lt => ``cancel_common_lt
  let hcommon ← if rel == .eq then do
    let tail ← mkAppM ``IsUnit.mul #[last, q(isUnit_one : IsUnit (1 : $M))]
    rest.foldlM (fun h x ↦ mkAppM ``IsUnit.mul #[x, h]) tail
  else do
    -- A partially ordered field-like carrier need not have an instance proving products positive.
    let h? ← liftM <| observing? do
      let tail ← mkAppM ``positive_mul_one #[last]
      rest.foldlM (fun h x ↦ mkAppM ``mul_pos #[x, h]) tail
    let some h := h? | return ← plain
    pure h
  let cancelled := factors.reverse
  let kept := retained.reverse
  let (left, _) ← multiplyFactors iM left kept
  let (right, _) ← multiplyFactors iM right kept
  let hleft ← factorProof iM left cancelled ha
  let hright ← factorProof iM right cancelled hb
  let p ← mkAppM lemmaName #[hcommon, hleft, hright]
  let r : Simp.Result := { expr := (← inferType p).appArg!, proof? := some p }
  r.mkEqTrans (← simpOnlyNames [``display_mul_assoc, ``neg_one_mul, ``mul_neg_one] r.expr)

/-- Clear the denominator of an equality or multiply an inequality by a proved positive factor. -/
private def reducePropCore (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (t : Expr) (onlyDenominators := false) : AtomM Simp.Result := do
  let ⟨rel, _, a, b⟩ ← t.ineq?
  let ⟨_, M, a⟩ ← inferTypeQ' a
  have b : Q($M) := b
  let iM : Q(CommGroupWithZero $M) ← synthInstanceQ q(CommGroupWithZero $M)
  let ⟨na, u, pa, ca⟩ ← normalize iM a
  let ⟨nb, v, pb, cb⟩ ← normalize iM b
  unless ca || cb do
    guard !onlyDenominators
    let isComposite (e : Expr) := e.isAppOf ``HMul.hMul || e.isAppOf ``HAdd.hAdd ||
      e.isAppOf ``HSub.hSub || e.isAppOf ``HPow.hPow
    guard (isComposite a || isComposite b)
    let r ← cancelComparisonFactors disch t []
    guard !(← withReducible <| isDefEq r.expr t)
    return r
  let units := (← denominatorUnits iM u) ++ (← denominatorUnits iM v)
  let finish (r : Simp.Result) : AtomM Simp.Result := do
    let r ← simplifyWitnesses r
    let cleaned ← cancelComparisonFactors disch r.expr units
    r.mkEqTrans cleaned
  if rel == .eq then
    return ← finish {
      expr := q($na * ($v : $M) = $nb * ($u : $M))
      proof? := some q(clear_eq $pa $pb) }
  let _poM : Q(PartialOrder $M) ← synthInstanceQ q(PartialOrder $M)
  have c : Q($M) := q((↑($u * $v) : $M))
  have left : Q($M) := q($na * ($v : $M))
  have right : Q($M) := q($nb * ($u : $M))
  haveI' : $c =Q (↑($u * $v) : $M) := ⟨⟩
  haveI' : $left =Q $na * ($v : $M) := ⟨⟩
  haveI' : $right =Q $nb * ($u : $M) := ⟨⟩
  have hl : Q($a * $c = $left) := q(common_denominator $pa $v)
  have hr : Q($b * $c = $right) := q(common_denominator_right $pb $u)
  let ⟨_c, left, right, hc, hl, hr⟩ :
      Σ (c left right : Q($M)), Q(0 < $c) × Q($a * $c = $left) × Q($b * $c = $right) ← do
    try
      let hc ← try disch q(0 < $c) catch _ => do
        let p ← mkAppM ``unit_mul_self_pos #[u]
        guard (← isDefEq (← inferType p) q(0 < $c))
        pure p
      pure ⟨c, left, right, hc, hl, hr⟩
    catch _ =>
      let hc ← try disch q(0 < $c ^ (2 : ℕ)) catch _ => do
        let p ← mkAppM ``unit_sq_pos #[q($u * $v)]
        guard (← isDefEq (← inferType p) q(0 < $c ^ (2 : ℕ)))
        pure p
      pure ⟨q($c ^ (2 : ℕ)), q($left * $c), q($right * $c), hc,
        q(square_denominator $hl), q(square_denominator $hr)⟩
  match rel with
  | .le =>
    let _mmM : Q(MulPosMono $M) ← synthInstanceQ q(MulPosMono $M)
    let _mrM : Q(MulPosReflectLE $M) ← synthInstanceQ q(MulPosReflectLE $M)
    return ← finish { expr := q($left ≤ $right), proof? := some q(clear_le $hc $hl $hr) }
  | .lt =>
    let _mmM : Q(MulPosStrictMono $M) ← synthInstanceQ q(MulPosStrictMono $M)
    let _mrM : Q(MulPosReflectLT $M) ← synthInstanceQ q(MulPosReflectLT $M)
    return ← finish { expr := q($left < $right), proof? := some q(clear_lt $hc $hl $hr) }
  | _ => failure

/-- Clear denominators and simplify the values of the certified unit witnesses. -/
def reduceProp (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (t : Expr) : AtomM Simp.Result := do
  simplifyWitnesses (← reducePropCore disch t)

open Elab Tactic Lean.Parser.Tactic

/-- Elaborate the requested discharger, or use the standard evidence discharger. -/
def parseDischarger (d : Option (TSyntax ``discharger)) (args : Option (TSyntax ``simpArgs)) :
    TacticM (∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) := do
  match d with
  | none =>
    let ctx ← Simp.Context.ofArgs (args.getD ⟨.missing⟩) { contextual := true }
    return fun e ↦ Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  | some d =>
    if args.isSome then
      logWarningAt args.get! "Custom field_simp dischargers do not use the arguments list"
    match d with
    | `(discharger| (discharger := $tac)) =>
      let tac := (evalTactic (← `(tactic| ($tac))) *> pruneSolvedGoals)
      return (synthesizeUsing' · tac)
    | _ => throwError "could not parse the provided discharger {d}"

/-- Clear unit denominators in expressions and equalities. Inequalities require a proved positive
multiplier; the default discharger also tries the square of the common denominator. The syntax
supports an explicit discharger, evidence arguments, and the usual tactic locations. -/
elab (name := fieldSimp) "field_simp" d:(discharger)? args:(simpArgs)? loc:(location)? :
    tactic => withMainContext do
  let disch ← parseDischarger d args
  let s ← IO.mkRef {}
  let cleanup r := simplifyWitnesses r
  let m := AtomM.recurse s { contextual := true } (wellBehavedDischarge := false)
    (fun e ↦ reduceProp disch e <|> reduceExpr disch e) cleanup
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  transformAtLocation (m ·) "field_simp" (ifUnchanged := .error) (mayCloseGoalFromHyp := true) loc

/-- Normalize the current conv expression to a fraction with a certified unit denominator. -/
elab "field_simp" d:(discharger)? args:(simpArgs)? : conv => do
  let x ← Conv.getLhs
  let disch ← parseDischarger d args
  let r ← AtomM.run .reducible <| reduceExpr disch x
  Conv.applySimpResult r

/-- The field simp set uses the same certified clearing procedure on comparisons. -/
def proc : Simp.Simproc := fun t ↦ do
  let ctx ← Simp.getContext
  let disch e : MetaM Expr := Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  try
    let r ← AtomM.run .reducible <| reducePropCore disch t (onlyDenominators := true)
    return .visit <| ← r.mkEqTrans (← simpOnlyNames [] r.expr)
  catch _ =>
    return .continue

end Mathlib.Tactic.FieldSimp

open Mathlib.Tactic

simproc_decl fieldEq (Eq _ _) := FieldSimp.proc
simproc_decl fieldLe (LE.le _ _) := FieldSimp.proc
simproc_decl fieldLt (LT.lt _ _) := FieldSimp.proc

attribute [field, inherit_doc FieldSimp.proc] fieldEq fieldLe fieldLt

register_hint 1000 field_simp
register_try?_tactic (priority := 1000) field_simp
