/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
module

public meta import Mathlib.Data.Rat.Init

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv.Basic
public import Mathlib.Util.Qq

/-!
## `norm_num` plugin for `^`.
-/

public section

assert_not_exists RelIso

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

variable {a b c : ℕ}

theorem natPow_zero : Nat.pow a (nat_lit 0) = nat_lit 1 := rfl
theorem natPow_one : Nat.pow a (nat_lit 1) = a := Nat.pow_one _
theorem zero_natPow : Nat.pow (nat_lit 0) (Nat.succ b) = nat_lit 0 := rfl
theorem one_natPow : Nat.pow (nat_lit 1) b = nat_lit 1 := Nat.one_pow _

/-- This is an opaque wrapper around `Nat.pow` to prevent lean from unfolding the definition of
`Nat.pow` on numerals. The arbitrary precondition `p` is actually a formula of the form
`Nat.pow a' b' = c'` but we usually don't care to unfold this proposition so we just carry a
reference to it. -/
structure IsNatPowT (p : Prop) (a b c : Nat) : Prop where
  /-- Unfolds the assertion. -/
  run' : p → Nat.pow a b = c

theorem IsNatPowT.run
    (p : IsNatPowT (Nat.pow a (nat_lit 1) = a) a b c) : Nat.pow a b = c := p.run' (Nat.pow_one _)

/-- This is the key to making the proof proceed as a balanced tree of applications instead of
a linear sequence. It is just modus ponens after unwrapping the definitions. -/
theorem IsNatPowT.trans {p : Prop} {b' c' : ℕ} (h1 : IsNatPowT p a b c)
    (h2 : IsNatPowT (Nat.pow a b = c) a b' c') : IsNatPowT p a b' c' :=
  ⟨h2.run' ∘ h1.run'⟩

theorem IsNatPowT.bit0 : IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b) (Nat.mul c c) :=
  ⟨fun h1 => by simp [two_mul, pow_add, ← h1]⟩

theorem IsNatPowT.bit1 :
    IsNatPowT (Nat.pow a b = c) a (nat_lit 2 * b + nat_lit 1) (Nat.mul c (Nat.mul c a)) :=
  ⟨fun h1 => by simp [two_mul, pow_add, mul_assoc, ← h1]⟩

/--
Proves `Nat.pow a b = c` where `a` and `b` are raw nat literals. This could be done by just
`rfl` but the kernel does not have a special case implementation for `Nat.pow` so this would
proceed by unary recursion on `b`, which is too slow and also leads to deep recursion.

We instead do the proof by binary recursion, but this can still lead to deep recursion,
so we use an additional trick to do binary subdivision on `log2 b`. As a result this produces
a proof of depth `log (log b)` which will essentially never overflow before the numbers involved
themselves exceed memory limits.
-/
meta partial def evalNatPow (a b : Q(ℕ)) : OptionT CoreM ((c : Q(ℕ)) × Q(Nat.pow $a $b = $c)) := do
  if b.natLit! = 0 then
    haveI : $b =Q 0 := ⟨⟩
    return ⟨q(nat_lit 1), q(natPow_zero)⟩
  else if a.natLit! = 0 then
    haveI : $a =Q 0 := ⟨⟩
    have b' : Q(ℕ) := mkRawNatLit (b.natLit! - 1)
    haveI : $b =Q Nat.succ $b' := ⟨⟩
    return ⟨q(nat_lit 0), q(zero_natPow)⟩
  else if a.natLit! = 1 then
    haveI : $a =Q 1 := ⟨⟩
    return ⟨q(nat_lit 1), q(one_natPow)⟩
  else if b.natLit! = 1 then
    haveI : $b =Q 1 := ⟨⟩
    return ⟨a, q(natPow_one)⟩
  else
    guard <| ← Lean.checkExponent b.natLit!
    let ⟨c, p⟩ := go b.natLit!.log2 a q(nat_lit 1) a b _ .rfl
    return ⟨c, q(($p).run)⟩
where
  /-- Invariants: `a ^ b₀ = c₀`, `depth > 0`, `b >>> depth = b₀`, `p := Nat.pow $a $b₀ = $c₀` -/
  go (depth : Nat) (a b₀ c₀ b : Q(ℕ)) (p : Q(Prop)) (hp : $p =Q (Nat.pow $a $b₀ = $c₀)) :
      (c : Q(ℕ)) × Q(IsNatPowT $p $a $b $c) :=
    let b' := b.natLit!
    if depth ≤ 1 then
      let a' := a.natLit!
      let c₀' := c₀.natLit!
      if b' &&& 1 == 0 then
        have c : Q(ℕ) := mkRawNatLit (c₀' * c₀')
        haveI : $c =Q Nat.mul $c₀ $c₀ := ⟨⟩
        haveI : $b =Q 2 * $b₀ := ⟨⟩
        ⟨c, q(IsNatPowT.bit0)⟩
      else
        have c : Q(ℕ) := mkRawNatLit (c₀' * (c₀' * a'))
        haveI : $c =Q Nat.mul $c₀ (Nat.mul $c₀ $a) := ⟨⟩
        haveI : $b =Q 2 * $b₀ + 1 := ⟨⟩
        ⟨c, q(IsNatPowT.bit1)⟩
    else
      let d := depth >>> 1
      have hi : Q(ℕ) := mkRawNatLit (b' >>> d)
      let ⟨c1, p1⟩ := go (depth - d) a b₀ c₀ hi p (by exact hp)
      let ⟨c2, p2⟩ := go d a hi c1 b q(Nat.pow $a $hi = $c1) ⟨⟩
      ⟨c2, q(($p1).trans $p2)⟩

theorem intPow_ofNat (h1 : Nat.pow a b = c) :
    Int.pow (Int.ofNat a) b = Int.ofNat c := by simp [← h1]

theorem intPow_negOfNat_bit0 {b' c' : ℕ} (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' = b) (hc : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  rw [← hb, Int.negOfNat_eq, Int.pow_eq, pow_mul, neg_pow_two, ← pow_mul, two_mul, pow_add, ← hc,
    ← h1]
  simp

theorem intPow_negOfNat_bit1 {b' c' : ℕ} (h1 : Nat.pow a b' = c')
    (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  rw [← hb, Int.negOfNat_eq, Int.negOfNat_eq, Int.pow_eq, pow_succ, pow_mul, neg_pow_two, ← pow_mul,
    two_mul, pow_add, ← hc, ← h1]
  simp [mul_comm, mul_left_comm]

/-- Evaluates `Int.pow a b = c` where `a` and `b` are raw integer literals. -/
meta partial def evalIntPow (za : ℤ) (a : Q(ℤ)) (b : Q(ℕ)) :
    OptionT CoreM (ℤ × (c : Q(ℤ)) × Q(Int.pow $a $b = $c)) := do
  have a' : Q(ℕ) := a.appArg!
  if 0 ≤ za then
    have : $a =Q .ofNat $a' := ⟨⟩
    let ⟨c, p⟩ ← evalNatPow a' b
    return ⟨c.natLit!, q(.ofNat $c), q(intPow_ofNat $p)⟩
  else
    have : $a =Q .negOfNat $a' := ⟨⟩
    let b' := b.natLit!
    have b₀ : Q(ℕ) := mkRawNatLit (b' >>> 1)
    let ⟨c₀, p⟩ ← evalNatPow a' b₀
    let c' := c₀.natLit!
    if b' &&& 1 == 0 then
      have c : Q(ℕ) := mkRawNatLit (c' * c')
      have pc : Q($c₀ * $c₀ = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ = $b) := (q(Eq.refl $b) : Expr)
      return ⟨c.natLit!, q(.ofNat $c), q(intPow_negOfNat_bit0 $p $pb $pc)⟩
    else
      have c : Q(ℕ) := mkRawNatLit (c' * (c' * a'.natLit!))
      have pc : Q($c₀ * ($c₀ * $a') = $c) := (q(Eq.refl $c) : Expr)
      have pb : Q(2 * $b₀ + 1 = $b) := (q(Eq.refl $b) : Expr)
      return ⟨-c.natLit!, q(.negOfNat $c), q(intPow_negOfNat_bit1 $p $pb $pc)⟩

-- see note [norm_num lemma function equality]
theorem isNat_pow {α} [Semiring α] : ∀ {f : α → ℕ → α} {a : α} {b a' b' c : ℕ},
    f = HPow.hPow → IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
theorem isInt_pow {α} [Ring α] : ∀ {f : α → ℕ → α} {a : α} {b : ℕ} {a' : ℤ} {b' : ℕ} {c : ℤ},
    f = HPow.hPow → IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

-- see note [norm_num lemma function equality]
theorem isRat_pow {α} [Ring α] {f : α → ℕ → α} {a : α} {an cn : ℤ} {ad b b' cd : ℕ} :
    f = HPow.hPow → IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

theorem isNNRat_pow {α} [Semiring α] {f : α → ℕ → α} {a : α} {an cn : ℕ} {ad b b' cd : ℕ} :
    f = HPow.hPow → IsNNRat a an ad → IsNat b b' →
    Nat.pow an b' = cn → Nat.pow ad b' = cd →
    IsNNRat (f a b) cn cd := by
  rintro rfl ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow, Nat.cast_commute]

/-- Main part of `evalPow`. -/
meta def evalPow.core {u : Level} {α : Q(Type u)} (e : Q(«$α»)) (f : Q(«$α» → ℕ → «$α»))
    (a : Q(«$α»)) (b nb : Q(ℕ)) (pb : Q(IsNat «$b» «$nb»)) (sα : Q(Semiring «$α»)) (ra : Result a) :
    OptionT CoreM (Result e) := do
  haveI' : $e =Q $a ^ $b := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  match ra with
  | .isBool .. => failure
  | .isNat sα na pa =>
    assumeInstancesCommute
    let ⟨c, r⟩ ← evalNatPow na nb
    return .isNat sα c q(isNat_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNegNat rα .. =>
    assumeInstancesCommute
    let ⟨za, na, pa⟩ ← OptionT.mk <| pure (ra.toInt rα)
    let ⟨zc, c, r⟩ ← evalIntPow za na nb
    return .isInt rα c zc q(isInt_pow (f := $f) (.refl $f) $pa $pb $r)
  | .isNNRat dα _qa na da pa =>
    assumeInstancesCommute
    let ⟨nc, r1⟩ ← evalNatPow na nb
    let ⟨dc, r2⟩ ← evalNatPow da nb
    if hdc : dc.natLit! = 0 then failure else
      let qc := Rat.fraction nc.natLit! dc.natLit! hdc
      return .isNNRat dα qc nc dc q(isNNRat_pow (f := $f) (.refl $f) $pa $pb $r1 $r2)
  | .isNegNNRat dα qa na da pa =>
    assumeInstancesCommute
    let ⟨zc, nc, r1⟩ ← evalIntPow qa.num q(Int.negOfNat $na) nb
    let ⟨dc, r2⟩ ← evalNatPow da nb
    if hdc : dc.natLit! = 0 then failure else
      let qc := Rat.fraction zc dc.natLit! hdc
      return .isRat dα qc nc dc q(isRat_pow (f := $f) (.refl $f) $pa $pb $r1 $r2)

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num _ ^ (_ : ℕ)]
meta def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app (f : Q($α → ℕ → $α)) (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(Nat.instAddMonoidWithOne)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  haveI' : $e =Q $a ^ $b := ⟨⟩
  haveI' : $f =Q HPow.hPow := ⟨⟩
  let .some r ←
    liftM <| OptionT.run (evalPow.core q($e) q($f) q($a) q($b) q($nb) q($pb) q($sα) ra) | failure
  return r

/-- Evaluating a nonnegative integer power never requires invertibility of its base. -/
theorem zpow_nat {α : Type*} [Monoid α] {a : α} {b : ℤ} {nb : ℕ}
    (h : b < 0 → IsUnit a) (pb : IsNat b nb) : Checked.zpow a b h = a ^ nb := by
  obtain ⟨hb⟩ := pb
  subst b
  rfl

/-- The natural power used to evaluate a negative exponent is invertible.
The zero exponent case needs no invertibility assumption on the base. -/
theorem zpow_neg_isUnit {α : Type*} [Monoid α] {a : α} {b : ℤ} {nb : ℕ}
    (h : b < 0 → IsUnit a) (pb : IsInt b (Int.negOfNat nb)) : IsUnit (a ^ nb) := by
  by_cases hn : nb = 0
  · subst nb
    simpa only [pow_zero] using (isUnit_one : IsUnit (1 : α))
  · have hb : b < 0 := by
      rw [pb.out, Int.cast_negOfNat]
      omega
    exact (h hb).pow nb

/-- Negative integer powers reduce to a checked inverse of a natural power,
carrying the original exponent-dependent domain evidence. -/
theorem zpow_neg {α : Type*} [Monoid α] {a : α} {b : ℤ} {nb : ℕ}
    (h : b < 0 → IsUnit a) (pb : IsInt b (Int.negOfNat nb)) :
    Checked.zpow a b h = Checked.inv (a ^ nb) (zpow_neg_isUnit h pb) := by
  by_cases hn : nb = 0
  · subst nb
    have hb : b = 0 := pb.out.trans rfl
    subst b
    simp only [zpow_zero₀, pow_zero, inv_one₀]
  · have hb : b < 0 := by
      rw [pb.out, Int.cast_negOfNat]
      omega
    let hu := h hb
    rw [hu.zpow_eq_val_unit_zpow b]
    have hp : (zpow_neg_isUnit h pb).unit = hu.unit ^ nb := Units.ext (by
      simp only [IsUnit.unit_spec, Units.val_pow_eq_pow_val])
    change (↑(hu.unit ^ b) : α) = ↑(zpow_neg_isUnit h pb).unit⁻¹
    rw [hp, pb.out, Int.cast_negOfNat, _root_.zpow_neg, zpow_natCast]

/-- Evaluate a checked integer power by evaluating its natural power and, when
needed, its checked inverse. Equality transport retains the source domain proof. -/
@[norm_num (Checked.zpow _ _ _ : _)]
meta def evalZPow : NormNumExt where eval {u α} e := do
  let .app (.app (.app (.app (.app (.const ``Checked.zpow _) _)
      (inst : Q(Monoid $α))) (a : Q($α))) (b : Q(ℤ))) (sourceH : Expr) := e | failure
  let dsα ← inferDivisionSemiring α
  guard <| ← isDefEq inst q(@Semiring.toMonoid $α (@DivisionSemiring.toSemiring $α $dsα))
  assumeInstancesCommute
  have h : Q($b < 0 → IsUnit $a) := sourceH
  haveI' : $e =Q Checked.zpow $a $b $h := ⟨⟩
  let rb ← derive (α := q(ℤ)) b
  match rb with
  | .isBool .. | .isNNRat _ .. | .isNegNNRat _ .. => failure
  | .isNat _ nb pb =>
    assumeInstancesCommute
    return Result.eqTrans q(zpow_nat $h $pb) (← derive q($a ^ $nb))
  | .isNegNat _ nb pb =>
    assumeInstancesCommute
    have hp : Q(IsUnit ($a ^ $nb)) := q(zpow_neg_isUnit $h $pb)
    let r ← (← derive q($a ^ $nb)).inv dsα hp
    return Result.eqTrans q(zpow_neg $h $pb) r

end NormNum

end Meta

end Mathlib
