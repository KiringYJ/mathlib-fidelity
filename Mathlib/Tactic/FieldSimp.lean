/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw, Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

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
certificate; an inverse transfers its original unit evidence to the normalized numerator before
reversing the fraction. No total inverse or signed power of an arbitrary atom is used.
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
  /-- Whether normalization found any division or inverse. -/
  changed : Bool

private def atom (iM : Q(CommGroupWithZero $M)) (e : Q($M)) : Normalized iM e :=
  ⟨e, q(1), q(normalize_atom $e), false⟩

/-- Erase unit-witness bookkeeping from the displayed arithmetic while retaining its proof. -/
private def simplifyWitnesses (r : Simp.Result) : MetaM Simp.Result := do
  r.mkEqTrans (← simpOnlyNames [``Units.val_mul, ``Units.val_one,
    ``Units.val_pow_eq_pow_val, ``numeratorUnit_val, ``mul_one, ``one_mul, ``divp_one,
    ``div_one₀] r.expr)

/-- Normalize a field expression while retaining the original denominator certificates. -/
partial def normalize (iM : Q(CommGroupWithZero $M)) (e : Q($M)) :
    AtomM (Normalized iM e) := do
  match e with
  | ~q(Checked.div $a $b $hb) =>
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
      have k : Q(ℕ) := mkRawNatLit k
      haveI' : $r =Q Int.negSucc $k := ⟨⟩
      have hinv : Q(IsUnit $a) := q($ha (Int.negSucc_lt_zero $k))
      have ni : Q($M) := q(($u : $M))
      have ui : Q($Mˣ) := q(numeratorUnit $a $n $u $hinv $p)
      haveI' : $ni =Q ($u : $M) := ⟨⟩
      haveI' : $ui =Q numeratorUnit $a $n $u $hinv $p := ⟨⟩
      have pi : Q(Checked.inv $a $hinv = $ni /ₚ $ui) := q(normalize_inv $hinv $p)
      return ⟨q($ni ^ ($k + 1)), q($ui ^ ($k + 1)),
        q(Eq.trans (checked_zpow_negSucc $a $k $ha) (normalize_pow $pi ($k + 1))), true⟩
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

/-- Rewrite a field expression as a certified fraction. -/
def reduceExpr (_disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (e : Expr) : AtomM Simp.Result := do
  let ⟨_, M, e⟩ ← inferTypeQ' e
  let iM : Q(CommGroupWithZero $M) ← synthInstanceQ q(CommGroupWithZero $M)
  let ⟨n, d, p, changed⟩ ← normalize iM e
  guard changed
  -- The result is the ordinary quotient by the value of the denominator unit.
  let result : Simp.Result := {
    expr := q(Checked.div $n ($d : $M) (Units.isUnit $d))
    proof? := some q(($p).trans (divp_eq_div_val $n $d))
  }
  simplifyWitnesses result

/-- Clear the denominator of an equality or multiply an inequality by a proved positive factor. -/
private def reducePropCore (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (t : Expr) : AtomM Simp.Result := do
  let ⟨rel, _, a, b⟩ ← t.ineq?
  let ⟨_, M, a⟩ ← inferTypeQ' a
  have b : Q($M) := b
  let iM : Q(CommGroupWithZero $M) ← synthInstanceQ q(CommGroupWithZero $M)
  let ⟨na, u, pa, ca⟩ ← normalize iM a
  let ⟨nb, v, pb, cb⟩ ← normalize iM b
  guard (ca || cb)
  if rel == .eq then
    return { expr := q($na * ($v : $M) = $nb * ($u : $M)), proof? := some q(clear_eq $pa $pb) }
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
    return { expr := q($left ≤ $right), proof? := some q(clear_le $hc $hl $hr) }
  | .lt =>
    let _mmM : Q(MulPosStrictMono $M) ← synthInstanceQ q(MulPosStrictMono $M)
    let _mrM : Q(MulPosReflectLT $M) ← synthInstanceQ q(MulPosReflectLT $M)
    return { expr := q($left < $right), proof? := some q(clear_lt $hc $hl $hr) }
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
    let r ← AtomM.run .reducible <| reduceProp disch t
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
