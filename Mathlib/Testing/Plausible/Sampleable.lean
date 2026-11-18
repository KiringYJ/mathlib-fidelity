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

/-!
This module contains `Plausible.Shrinkable` and `Plausible.SampleableExt` instances for mathlib
types.
-/

public section

namespace Plausible

open Random Gen

section Shrinkers

meta instance Rat.shrinkable : Shrinkable Rat where
  shrink r :=
    (Shrinkable.shrink r.num).flatMap fun d =>
      Nat.shrink r.den |>.filterMap fun n =>
        if hn : n = 0 then none else some (Rat.normalize d n hn)

meta instance PNat.shrinkable : Shrinkable PNat where
  shrink m := Nat.shrink m.natPred |>.map Nat.succPNat

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
