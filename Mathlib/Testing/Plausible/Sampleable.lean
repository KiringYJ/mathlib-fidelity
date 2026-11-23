/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
module

public import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Data.List.Monad
public meta import Mathlib.Data.PNat.Defs
public import Plausible.Sampleable
public import Plausible.Arbitrary
public import Plausible.Gen
public import Plausible.Random
public meta import Plausible.Sampleable
import Mathlib.Lean.Elab.NativeDivision

/-!
This module contains `Plausible.Shrinkable` and `Plausible.SampleableExt` instances for mathlib
types.
-/

public section

namespace Plausible

open Random Gen

section Shrinkers

/-- Successive halving gives the same candidate order as Plausible's natural shrinker. -/
private meta def shrinkNat : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let half := Nat.euclideanDiv (n + 1) 2
    half :: shrinkNat half
termination_by n => n
decreasing_by exact Nat.euclideanDiv_lt_self (Nat.succ_pos _) Nat.one_lt_two

@[no_expose]
meta instance Rat.shrinkable : Shrinkable Rat where
  shrink r :=
    let numerators := (shrinkNat r.num.natAbs).flatMap fun n => [Int.ofNat n, -Int.ofNat n]
    numerators.flatMap fun d =>
      shrinkNat r.den |>.filterMap fun n =>
        if hn : n = 0 then none else some (Rat.normalize d n hn)

@[no_expose]
meta instance PNat.shrinkable : Shrinkable PNat where
  shrink m := shrinkNat m.natPred |>.map Nat.succPNat

end Shrinkers

section Samplers

open SampleableExt

meta instance Rat.Arbitrary : Arbitrary Rat where
  arbitrary := do
    let size ← getSize
    let d ← choose Int (-(size : Int)) size
      (le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.natCast_nonneg _))
    let n ← choose Nat 0 (size - 1) (Nat.zero_le _)
    return Rat.normalize d (n + 1) (Nat.succ_ne_zero n)

meta instance Rat.sampleableExt : SampleableExt Rat := by infer_instance


meta instance PNat.Arbitrary : Arbitrary PNat where
  arbitrary := do
    let n ← chooseNat
    return Nat.succPNat n

meta instance PNat.sampleableExt : SampleableExt PNat := by infer_instance

end Samplers

end Plausible
