/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Tactic.Linter.OperatorFidelity
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Rat.Defs

/-!
# Tests for the operator-fidelity linter
-/

open Lean Elab Command
open Mathlib.Linter.OperatorFidelity

namespace OperatorFidelityTest

class ScopedCertificate : Prop where
  witness : ∃ _ : Nat, True

set_option linter.defProp false in
@[instance_reducible] private def scopedCertificate (a b : Nat) : ScopedCertificate :=
  ⟨⟨Nat.div a b, trivial⟩⟩

private def useScopedCertificate (_ : ScopedCertificate) : Nat := 1

def scopedProofUse (a b : Nat) : Nat := useScopedCertificate (scopedCertificate a b)

/--
info: scopedCertificate: Nat.div from scopedCertificate (Mathlib.Linter.OperatorFidelity.SourceOwnership.project)
-/
#guard_msgs (whitespace := lax) in
#operator_fidelity with_proofs in FidelityTest.Linter.OperatorFidelity

private def coveredPair (n : Nat) : Nat × Nat := (n, 1)

def selectedLawfulField (a : Nat) : Nat := (coveredPair (Nat.div a 0)).2

def selectedNativeQuotient (a : Nat) : Nat := (coveredPair (Nat.div a 0)).1

/--
error: Operator-fidelity semantic audit failed:

      selectedNativeQuotient: data: Nat.div
-/
#guard_msgs (whitespace := lax) in
#operator_fidelity in FidelityTest.Linter.OperatorFidelity

def badDirect (q : Rat) : Rat := Rat.inv q

private def badPrivateAlias (q : Rat) : Rat := badDirect q

def badDisguisedAlias (q : Rat) : Rat := badPrivateAlias q

def badConstructor (n : Int) (d : Nat) : Rat := mkRat n d

def BadPredicate (q : Rat) : Prop := Rat.inv q = q

structure Package where
  value : Rat
  law : True

def badPackage : Package where
  value := Rat.div 1 0
  law := True.intro

opaque consumeRetiredProof : Rat.inv 0 = 0 → True

opaque consumeProof {P : Prop} : P → True

set_option linter.defProp false in
def proofUsesRetiredOperator : True := consumeRetiredProof Rat.inv_zero

set_option linter.defProp false in
def proofUsesOfficialRetiredOperator : True := consumeProof Rat.inv_zero

private theorem retiredWitness : ∃ q : Rat, q = 0 := ⟨Rat.inv 0, Rat.inv_zero⟩

theorem inheritedRetiredWitness : ∃ q : Rat, q = 0 := retiredWitness

def goodPackage : Package where
  value := Rat.normalize 1 2 (by decide)
  law := True.intro

structure ProofPackage where
  value : Rat
  law : Rat.inv value = Rat.inv value

def proofPackage : ProofPackage where
  value := Rat.normalize 1 2 (by decide)
  law := rfl

def goodArithmetic (q r : Rat) : Rat := q * r + 1

def goodNormalize : Rat := Rat.normalize 3 4 (by decide)

def goodRationalRounding (q : Rat) : Int × Int := (q.floor, q.ceil)

def badRationalRoundingArgument (q r : Rat) : Int := (Rat.div q r).floor

def goodUnitsInverse (u : Ratˣ) : Rat := ↑u⁻¹

structure MixedOperations where
  selected : Rat → Rat
  unusedRetired : Rat → Rat

def mixedOperations : MixedOperations where
  selected q := q * q
  unusedRetired := Rat.inv

def goodSelectedProjection (q : Rat) : Rat := mixedOperations.selected q

def badConditionalProjection (p : Bool) : Rat → Rat :=
  (if p then mixedOperations else ⟨Rat.inv, Rat.neg⟩).selected

def goodConditionalProjection (p : Bool) : Rat → Rat :=
  (if p then mixedOperations else ⟨Rat.neg, Rat.inv⟩).selected

def goodDependentProjection (q : Rat) : Rat → Rat :=
  (if h : q = 0 then mixedOperations else
    ⟨Rat.neg, fun r => (fun (_ : q ≠ 0) => Rat.inv r) h⟩).selected

def unknownProjection (transform : MixedOperations → MixedOperations) : Rat → Rat :=
  (transform mixedOperations).selected

def badReducibleChoice : Nat :=
  (if Nat.div 8 2 = 4 then (⟨0, 0⟩ : PProd Nat Nat) else ⟨1, 1⟩).snd

private def pairWithCertificate (_ : (0 : Nat) = 0) : PProd Nat Nat := ⟨0, 7⟩

def projectionWithOfficialCertificate : Nat := (pairWithCertificate (Nat.div_zero 1)).snd

structure CertifiedNat where
  value : Nat
  certificate : ∃ _ : Nat, True

structure WithDiscardedCertificate where
  value : Nat
  payload : CertifiedNat

def projectionWithUnusedCertificate (a b : Nat) : Nat :=
  (⟨0, ⟨0, ⟨Nat.div a b, trivial⟩⟩⟩ : WithDiscardedCertificate).value

private theorem ignoreNat (_ : Nat) : True := trivial

theorem proofWithStuckProjection (transform : PProd Nat Nat → PProd Nat Nat) (a b : Nat) :
    True := ignoreNat (transform ⟨Nat.div a b, 0⟩).snd

theorem proofWithCoreExact (a b : Nat) (h : b ∣ a) : True :=
  ignoreNat (a.divExact b h)

meta def tacticWithRetiredComputation (a b : Nat) : Lean.Elab.Tactic.Tactic := fun _ =>
  if Nat.div a b = 0 then pure () else throwError "expected a zero quotient"

meta def checkerWithRetiredComputation (a b : Nat) : Lean.Core.CoreM Unit :=
  if Nat.div a b = 0 then pure () else throwError "expected a zero quotient"

meta def checkerWithRetiredDefault (a b : Nat) (q : Nat := Nat.div a b) : Lean.Core.CoreM Unit :=
  if q = 0 then pure () else throwError "expected a zero quotient"

def checksSyntaxWithRetiredComputation (_ : Expr) (a b : Nat) : Lean.Meta.MetaM Bool :=
  pure (Nat.div a b == 0)

def dataWithRetiredDefault (a b : Nat) (q : Nat := Nat.div a b) : Nat := q

meta def tacticWithRetiredSignature (a b : Nat) (_ : Nat.div a b = 0) :
    Lean.Elab.Tactic.Tactic := fun _ => pure ()

meta def tacticReturningData (_ : Expr) (a b : Nat) : Lean.Elab.Tactic.TacticM Nat :=
  pure (Nat.div a b)

private inductive SyntaxPayload
  | term : Lean.Syntax.Term → SyntaxPayload

private structure WrappedSyntaxPayload where
  stx : Option SyntaxPayload

private structure MixedPayload where
  stx : Lean.Syntax.Term
  value : Nat

private meta def tacticReturningSyntax (stx : Lean.Syntax.Term) (a b : Nat) :
    Lean.Meta.MetaM WrappedSyntaxPayload :=
  pure ⟨if Nat.div a b = 0 then some (.term stx) else none⟩

private meta def tacticReturningMixedData (stx : Lean.Syntax.Term) (a b : Nat) :
    Lean.Meta.MetaM MixedPayload :=
  pure ⟨stx, Nat.div a b⟩

meta def tacticReturningSyntaxPair (stx : Syntax) (a b : Nat) :
    Lean.Meta.MetaM (Syntax × Expr) :=
  pure (stx, mkNatLit (Nat.div a b))

meta def tacticReturningMixedPair (stx : Syntax) (a b : Nat) :
    Lean.Meta.MetaM (Syntax × Nat) :=
  pure (stx, Nat.div a b)

private abbrev MixedCompilerM (α : Type) := Lean.Meta.MetaM (α × Nat)

meta def tacticReturningMixedAlias (stx : Syntax) (a b : Nat) : MixedCompilerM Syntax :=
  show Lean.Meta.MetaM (Syntax × Nat) from pure (stx, Nat.div a b)

meta def tacticWithMathematicalState (stx : Syntax) (a b : Nat) :
    StateT Nat Lean.Meta.MetaM Syntax := fun _ => pure (stx, Nat.div a b)

meta section

private structure CompilerResult where
  term : Expr

private abbrev CompilerM := StateT Unit MetaM

private partial def recursiveCompiler (a b n : Nat) : CompilerM CompilerResult :=
  if n == 0 then pure ⟨mkNatLit (Nat.div a b)⟩ else recursiveCompiler a b (n - 1)

end

local macro "supplyRetiredQuotient" "(" a:term "," b:term ")" : tactic =>
  `(tactic| exact Nat.div $a $b)

def emittedQuotient (a b : Nat) : Nat := by supplyRetiredQuotient (a, b)

-- These are the elaborated applications of the original native `/` notation, including the
-- adapter from `Div` to `HDiv` and an alias of the natural-number instance.
private abbrev nativeNatInstance := Nat.instDiv

def oldNatNotation (a b : Nat) : Nat :=
  @HDiv.hDiv Nat Nat Nat (@instHDiv Nat nativeNatInstance) a b

def OldIntPredicate (a b : Int) : Prop :=
  @HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) a b = a

def badCheckedWrapper (a b : Nat) (_ : b ≠ 0) : Nat := Nat.div a b

def badExactQuotient (a b : Nat) (h : b ∣ a) : Nat := a.divExact b h

def badGuardedExactQuotient (a b : Nat) (_ : b ≠ 0) (h : b ∣ a) : Nat :=
  a.divExact b h

theorem nativeProofUse : True := consumeProof (Nat.div_zero 1)

theorem retiredIff : True ↔ True := ⟨fun _ => nativeProofUse, id⟩

theorem proofThroughIff : True := retiredIff.mp trivial

def proofArgumentValue (_ : ∃ _ : Nat, True) : Nat := 0

theorem proofArgumentInStatement (a b : Nat) :
    proofArgumentValue ⟨Nat.div a b, trivial⟩ = 0 := rfl

def goodNatWorker (a b : Nat) (h : b ≠ 0) : Nat :=
  Nat.div.go b (Nat.pos_of_ne_zero h) a.succ a (Nat.lt_succ_self _)

def goodLcm (a b : Nat) : Nat := a.lcm b

def badLcmArgument (a b : Nat) : Nat := (Nat.div a b).lcm b

def goodSqrt (a : Nat) : Nat := a.sqrt

def badSqrtArgument (a b : Nat) : Nat := (Nat.div a b).sqrt

def goodBinaryLog (a : Nat) : Nat := a.log2

def badBinaryLogArgument (a b : Nat) : Nat := (Nat.div a b).log2

def goodMergeSort (xs : List Nat) : List Nat := xs.mergeSort (fun a b => decide (a ≤ b))

def badMergeSortComparator (n : Nat) (xs : List Nat) : List Nat :=
  xs.mergeSort (fun a b => decide (Nat.div a n ≤ b))

def goodBitwise (a b : Nat) : Nat := Nat.land a (Nat.shiftRight a b)

def badBitwiseArgument (a b : Nat) : Nat := Nat.land (Nat.div a b) (Nat.shiftRight a b)

def badShiftArgument (a b : Nat) : Nat := Nat.shiftRight a (Nat.div a b)

def badQuotientArgument (a b : Nat) (hb : b ≠ 0) : Nat :=
  Nat.euclideanDiv (Nat.div a b) b hb

def goodRemainders (a b : Nat) (x y : Int) : Nat × Int := (a % b, x % y)

private meta def assertContains (roots : Array Name) (root : Name) (context : String) :
    CommandElabM Unit :=
  unless roots.contains root do
    throwError "{context}: expected {root}, found {roots}"

private meta def assertEmpty (roots : Array Name) (context : String) : CommandElabM Unit :=
  unless roots.isEmpty do
    throwError "{context}: expected no roots, found {roots}"

elab "#guard_operator_fidelity" : command => do
  let direct ← liftTermElabM <| auditDeclaration ``badDirect
  assertContains direct.dataRoots ``Rat.inv "direct definition"

  let disguised ← liftTermElabM <| auditDeclaration ``badDisguisedAlias
  assertContains disguised.dataRoots ``Rat.inv "private indirect alias"

  let nativeNat ← liftTermElabM <| auditDeclaration ``oldNatNotation
  assertContains nativeNat.dataRoots ``Nat.div "native division through the HDiv adapter"
  let nativeInt ← liftTermElabM <| auditDeclaration ``OldIntPredicate
  assertContains nativeInt.statementRoots ``Int.ediv "native integer division in a predicate"
  for name in #[``badCheckedWrapper, ``badExactQuotient, ``badGuardedExactQuotient] do
    let result ← liftTermElabM <| auditDeclaration name
    assertContains result.dataRoots ``Nat.div s!"unchecked implementation of {name}"
  let proofUse ← liftTermElabM <| auditDeclaration ``nativeProofUse
  assertEmpty proofUse.statementRoots "faithful proposition using an official theorem"
  unless proofUse.proofUses.any (fun use => use.root == ``Nat.div &&
      use.ownership == .officialToolchain && use.sourceDeclaration == ``Nat.div_zero) do
    throwError "expected a proof dependency from Nat.div_zero, found {reprStr proofUse.proofUses}"
  for name in #[``proofThroughIff, ``proofArgumentInStatement] do
    let result ← liftTermElabM <| auditDeclaration name
    if result.hasActionableFinding then
      throwError "the proof-only use in {name} must not count as a semantic dependency"
    unless result.proofUses.any (fun use => use.root == ``Nat.div) do
      throwError "expected a proof dependency on Nat.div in {name}"
  for name in #[``proofWithStuckProjection, ``proofWithCoreExact] do
    let result ← liftTermElabM <| auditDeclaration name
    if result.hasActionableFinding || !(result.proofUses.any (fun use => use.root == ``Nat.div)) then
      throwError "expected a complete proof-only finding for {name}, found {reprStr result.proofUses}"
  for name in #[``tacticWithRetiredComputation, ``checkerWithRetiredComputation,
      ``checkerWithRetiredDefault, ``checksSyntaxWithRetiredComputation,
      ``tacticReturningSyntax, ``tacticReturningSyntaxPair] do
    let result ← liftTermElabM <| auditDeclaration name
    if result.hasActionableFinding || !result.proofUses.any (fun use =>
        use.root == ``Nat.div && use.sourceDeclaration == name && use.ownership == .project) then
      throwError "expected the native division in {name} to be a project proof dependency"
  let tacticSignature ← liftTermElabM <| auditDeclaration ``tacticWithRetiredSignature
  assertContains tacticSignature.statementRoots ``Nat.div "retired operator in a tactic signature"
  let dataDefault ← liftTermElabM <| auditDeclaration ``dataWithRetiredDefault
  assertContains dataDefault.statementRoots ``Nat.div "retired operator in a mathematical default"
  for name in #[``tacticReturningData, ``tacticReturningMixedData, ``tacticReturningMixedPair,
      ``tacticReturningMixedAlias, ``tacticWithMathematicalState, ``emittedQuotient] do
    let result ← liftTermElabM <| auditDeclaration name
    assertContains result.dataRoots ``Nat.div s!"retired operator in data produced by {name}"
  let implementation := Compiler.mkUnsafeRecName ``recursiveCompiler
  let generated ← liftTermElabM <| auditDeclaration implementation
  if generated.hasActionableFinding || !generated.proofUses.any (fun use =>
      use.root == ``Nat.div && use.sourceDeclaration == implementation &&
        use.ownership == .generatedProject) then
    throwError "expected a complete proof dependency in the generated compiler implementation"
  let lcmArgument ← liftTermElabM <| auditDeclaration ``badLcmArgument
  assertContains lcmArgument.dataRoots ``Nat.div "retired operator in a lawful operation's argument"
  liftTermElabM do
    let some equations ← Meta.getEqnsFor? ``Nat.lcm | throwError "expected a generated lcm equation"
    let hasProofUse ← equations.anyM fun name => do
      let result ← auditDeclaration name
      return !result.hasActionableFinding && result.proofUses.any (·.root == ``Nat.div)
    unless hasProofUse do
      throwError "expected the implementation equation to contribute a proof dependency"
  let roundingArgument ← liftTermElabM <| auditDeclaration ``badRationalRoundingArgument
  assertContains roundingArgument.dataRoots ``Rat.div "retired operator in the floor argument"
  let sqrtArgument ← liftTermElabM <| auditDeclaration ``badSqrtArgument
  assertContains sqrtArgument.dataRoots ``Nat.div "retired operator in the square root argument"
  let binaryLogArgument ← liftTermElabM <| auditDeclaration ``badBinaryLogArgument
  assertContains binaryLogArgument.dataRoots ``Nat.div "retired operator in the binary log argument"
  let mergeSortComparator ← liftTermElabM <| auditDeclaration ``badMergeSortComparator
  assertContains mergeSortComparator.dataRoots ``Nat.div "retired operator in the sort comparator"
  let quotientArgument ← liftTermElabM <| auditDeclaration ``badQuotientArgument
  assertContains quotientArgument.dataRoots ``Nat.div
    "retired operator in the guarded quotient argument"
  let branch ← liftTermElabM <| auditDeclaration ``badConditionalProjection
  assertContains branch.dataRoots ``Rat.inv "operator selected in one conditional branch"
  let choice ← liftTermElabM <| auditDeclaration ``badReducibleChoice
  assertContains choice.dataRoots ``Nat.div "operator in a reducible conditional's guard"
  let certificate ← liftTermElabM <| auditDeclaration ``projectionWithOfficialCertificate
  if certificate.hasActionableFinding || !certificate.proofUses.any (fun use =>
      use.root == ``Nat.div && use.sourceDeclaration == ``Nat.div_zero &&
        use.ownership == .officialToolchain) then
    throwError "expected a complete proof dependency from the projection's certificate"
  let unused ← liftTermElabM <| auditDeclaration ``projectionWithUnusedCertificate
  if unused.hasActionableFinding || !unused.proofUses.any (·.root == ``Nat.div) then
    throwError "expected a complete proof dependency from the discarded proof field"
  let projectedLaw ← liftTermElabM <| Meta.withLocalDeclD `pkg (mkConst ``ProofPackage) fun pkg =>
    auditExpression (.proj ``ProofPackage 1 pkg)
  if projectedLaw.hasActionableFinding || !projectedLaw.proofUses.any (·.root == ``Rat.inv) then
    throwError "expected the selected proof field's type to contribute a proof dependency"
  let natType := mkConst ``Nat
  let quotient := mkApp2 (mkConst ``Nat.div) (mkNatLit 6) (mkNatLit 2)
  let quotientEq := mkApp3 (mkConst ``Eq [.succ .zero]) natType quotient quotient
  let certificateTerm := mkApp2 (mkConst ``Eq.refl [.succ .zero]) natType quotient
  let inner := mkApp (Expr.lam `h quotientEq (mkConst ``True.intro) .default) certificateTerm
  let nested := mkApp (Expr.lam `u (mkConst ``Unit) inner .default) (mkConst ``Unit.unit)
  let nestedProof ← liftTermElabM <| auditExpression nested .proof
  if nestedProof.hasActionableFinding || !nestedProof.proofUses.any (fun use => use.root == ``Nat.div) then
    throwError "expected the proof dependency inside the nested beta redex"
  for name in #[``badBitwiseArgument, ``badShiftArgument] do
    let result ← liftTermElabM <| auditDeclaration name
    assertContains result.dataRoots ``Nat.div s!"retired operator in an argument to {name}"
  let unknown ← liftTermElabM <| auditDeclaration ``unknownProjection
  unless unknown.incomplete do throwError "unresolved projection must fail closed"
  let kernelProjection := fun i => Expr.proj ``MixedOperations i (mkConst ``mixedOperations)
  let selected ← liftTermElabM <| auditExpression (kernelProjection 0)
  unless !selected.hasActionableFinding do throwError "kernel projection included an unused field"
  let retired ← liftTermElabM <| auditExpression (kernelProjection 1)
  assertContains retired.dataRoots ``Rat.inv "kernel projection of a retired operator"
  let localLet ← liftTermElabM <| show MetaM AuditResult from
    Lean.Meta.withLetDecl `q (mkConst ``Nat) (mkApp2 (mkConst ``Nat.div) (mkNatLit 8) (mkNatLit 2))
      auditExpression
  assertContains localLet.dataRoots ``Nat.div "retired operator in a local let"

  let deep := (List.range 140).foldl
    (fun body i => .lam (.mkSimple s!"x{i}") (.const ``Nat []) body .default)
    (mkConst ``badDisguisedAlias)
  let deepResult ← liftTermElabM <| auditExpression deep
  unless deepResult.incomplete do
    throwError "deep private alias traversal must fail closed on exhaustion"

  let constructor ← liftTermElabM <| auditDeclaration ``badConstructor
  assertContains constructor.dataRoots ``mkRat "fallback constructor"

  let predicate ← liftTermElabM <| auditDeclaration ``BadPredicate
  assertContains predicate.statementRoots ``Rat.inv "predicate body"
  assertEmpty predicate.dataRoots "predicate body classification"

  let badStructure ← liftTermElabM <| auditDeclaration ``badPackage
  assertContains badStructure.dataRoots ``Rat.div "structure data field"

  let lawfulStructure ← liftTermElabM <| auditDeclaration ``goodPackage
  assertEmpty lawfulStructure.statementRoots "lawful structure statement"
  assertEmpty lawfulStructure.dataRoots "lawful structure data"

  let goodStructure ← liftTermElabM <| auditDeclaration ``proofPackage
  assertEmpty goodStructure.statementRoots "proof-field container statement"
  assertEmpty goodStructure.dataRoots "proof-field container data"
  unless goodStructure.proofUses.any (fun use => use.root == ``Rat.inv &&
      use.ownership == .project) do
    throwError "law proof: expected a project-owned proof dependency on Rat.inv, found \
      {reprStr goodStructure.proofUses}"

  let directProof ← liftTermElabM <| auditDeclaration ``proofUsesRetiredOperator
  unless directProof.proofUses.any (fun use => use.root == ``Rat.inv &&
      use.ownership == .project) do
    throwError "direct theorem: expected a project-owned proof dependency on Rat.inv, found \
      {reprStr directProof.proofUses}"

  let officialStatement ← liftTermElabM <| auditDeclaration ``Rat.inv_zero
  assertContains officialStatement.statementRoots ``Rat.inv "official theorem statement"

  let inheritedProof ← liftTermElabM <| auditDeclaration ``inheritedRetiredWitness
  assertEmpty inheritedProof.statementRoots "inherited theorem statement"
  assertEmpty inheritedProof.dataRoots "inherited theorem data"
  unless inheritedProof.proofUses.any (fun use => use.root == ``Rat.inv &&
      use.ownership == .project && use.sourceDeclaration == ``retiredWitness) do
    throwError "theorem body: expected a project-owned proof dependency on Rat.inv"

  let officialProof ← liftTermElabM <| auditDeclaration ``proofUsesOfficialRetiredOperator
  unless officialProof.proofUses.any (fun use => use.root == ``Rat.inv &&
      use.ownership == .officialToolchain && use.sourceDeclaration == ``Rat.inv_zero) do
    throwError "official proof caller: expected an official-toolchain dependency on Rat.inv, found \
      {reprStr officialProof.proofUses}"

  for (name, context) in #[
      (``goodArithmetic, "lawful rational arithmetic"),
      (``goodNormalize, "Rat.normalize"),
      (``goodRationalRounding, "rational floor and ceiling"),
      (``goodUnitsInverse, "Units inversion"),
      (``goodNatWorker, "positive-divisor Euclidean algorithm"),
      (``goodLcm, "least common multiple"),
      (``goodSqrt, "integer square root"),
      (``goodBinaryLog, "binary length minus one"),
      (``goodMergeSort, "stable list sorting"),
      (``goodBitwise, "bitwise and and right shift"),
      (``goodRemainders, "native remainders"),
      (``goodConditionalProjection, "selected operations across a conditional"),
      (``goodDependentProjection, "selected operations across a dependent conditional"),
      (``goodSelectedProjection, "projection-selected structure data")] do
    let result ← liftTermElabM <| auditDeclaration name
    if result.incomplete then
      throwError "{context}: the audit must complete for this lawful declaration"
    assertEmpty result.statementRoots context
    assertEmpty result.dataRoots context

#guard_operator_fidelity

end OperatorFidelityTest
