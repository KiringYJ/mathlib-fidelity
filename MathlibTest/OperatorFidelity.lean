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

def goodUnitsInverse (u : Ratˣ) : Rat := ↑u⁻¹

structure MixedOperations where
  selected : Rat → Rat
  unusedRetired : Rat → Rat

def mixedOperations : MixedOperations where
  selected q := q * q
  unusedRetired := Rat.inv

def goodSelectedProjection (q : Rat) : Rat := mixedOperations.selected q

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

  let officialProof ← liftTermElabM <| auditDeclaration ``proofUsesOfficialRetiredOperator
  unless officialProof.proofUses.any (fun use => use.root == ``Rat.inv &&
      use.ownership == .officialToolchain) do
    throwError "official proof caller: expected an official-toolchain dependency on Rat.inv, found \
      {reprStr officialProof.proofUses}"

  for (name, context) in #[
      (``goodArithmetic, "lawful rational arithmetic"),
      (``goodNormalize, "Rat.normalize"),
      (``goodUnitsInverse, "Units inversion"),
      (``goodSelectedProjection, "projection-selected structure data")] do
    let result ← liftTermElabM <| auditDeclaration name
    assertEmpty result.statementRoots context
    assertEmpty result.dataRoots context

#guard_operator_fidelity

end OperatorFidelityTest
