/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Field structure on the multiplicative/additive opposite
-/

public section

assert_not_exists RelIso

variable {α : Type*}

namespace MulOpposite

@[to_additive] instance instNNRatCast [NNRatCast α] : NNRatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩
@[to_additive] instance instRatCast [RatCast α] : RatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩

@[to_additive (attr := simp, norm_cast)]
lemma op_nnratCast [NNRatCast α] (q : ℚ≥0) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
lemma unop_nnratCast [NNRatCast α] (q : ℚ≥0) : unop (q : αᵐᵒᵖ) = q := rfl

@[to_additive (attr := simp, norm_cast)]
lemma op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
lemma unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q := rfl

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnratCastOfCharZero _ q :=
    haveI := CharZero.of_map_natCast (op : α → αᵐᵒᵖ) fun _ => rfl
    op q
  nnratCastOfCharZero_mul_den _ q := by
    have := CharZero.of_map_natCast (op : α → αᵐᵒᵖ) fun _ => rfl
    apply unop_injective
    change (q.den : α) * DivisionSemiring.nnratCastOfCharZero _ q = (q.num : α)
    rw [(Nat.cast_commute q.den _).eq]
    exact DivisionSemiring.nnratCastOfCharZero_mul_den _ q

instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  ratCastOfCharZero _ q :=
    haveI := CharZero.of_map_natCast (op : α → αᵐᵒᵖ) fun _ => rfl
    op q
  ratCastOfCharZero_mul_den _ q := by
    have := CharZero.of_map_natCast (op : α → αᵐᵒᵖ) fun _ => rfl
    apply unop_injective
    change (q.den : α) * DivisionRing.ratCastOfCharZero _ q = (q.num : α)
    rw [(Nat.cast_commute q.den _).eq]
    exact DivisionRing.ratCastOfCharZero_mul_den _ q

instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵐᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end MulOpposite

namespace AddOpposite

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnratCastOfCharZero _ q :=
    haveI := CharZero.of_map_natCast (op : α → αᵃᵒᵖ) fun _ => rfl
    op q
  nnratCastOfCharZero_mul_den _ q := by
    have := CharZero.of_map_natCast (op : α → αᵃᵒᵖ) fun _ => rfl
    exact congrArg op (DivisionSemiring.nnratCastOfCharZero_mul_den _ q)

instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  ratCastOfCharZero _ q :=
    haveI := CharZero.of_map_natCast (op : α → αᵃᵒᵖ) fun _ => rfl
    op q
  ratCastOfCharZero_mul_den _ q := by
    have := CharZero.of_map_natCast (op : α → αᵃᵒᵖ) fun _ => rfl
    exact congrArg op (DivisionRing.ratCastOfCharZero_mul_den _ q)

instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵃᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end AddOpposite
