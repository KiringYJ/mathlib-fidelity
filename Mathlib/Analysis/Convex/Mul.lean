/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monovary
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp

/-!
# Product of convex functions

This file proves that the product of convex functions is convex, provided they monovary.

As corollaries, we also prove that `x ↦ x ^ n` is convex
* `Even.convexOn_pow`: for even `n : ℕ`.
* `convexOn_pow`: over $[0, +∞)$ for `n : ℕ`.
* `convexOn_zpow`: over $(0, +∞)$ for `n : ℤ`, as a function on the positive elements, convex in
  the coordinate `Subtype.val`.

The product lemmas and `ConvexOn.pow` hold for functions that are convex in coordinates.
-/

public section

open Set

variable {𝕜 E F G : Type*}

section LinearOrderedCommRing
variable [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [CommRing E] [LinearOrder E] [IsStrictOrderedRing E]
  [AddCommGroup F] [LinearOrder F] [IsOrderedAddMonoid F]
  [AddCommGroup G] [Module 𝕜 G]
  [Module 𝕜 E] [Module 𝕜 F] [Module E F] [IsScalarTower 𝕜 E F] [SMulCommClass 𝕜 E F]
  [IsOrderedModule 𝕜 F] [IsStrictOrderedModule E F] {D : Type*} {coord : D → G} {s : Set D}
  {f : D → E} {g : D → F}

lemma ConvexOn.smul' (hf : ConvexOn 𝕜 s f coord) (hg : ConvexOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) coord := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab z hz hzxy ↦ ?_⟩
  dsimp
  refine
    (smul_le_smul (hf.2 hx hy ha hb hab hz hzxy) (hg.2 hx hy ha hb hab hz hzxy) (hf₀ hz) <|
      add_nonneg (smul_nonneg ha <| hg₀ hx) <| smul_nonneg hb <| hg₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := ?_
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ = _ := by simp_rw [hab, mul_one]
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a, ← smul_smul_smul_comm b, ← smul_smul_smul_comm a b,
    ← smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b,
    add_comm _ ((b * b) • f y • g y), add_add_add_comm, add_comm ((a * b) • f y • g x)]

lemma ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f coord)
    (hg : ConcaveOn 𝕜 s g coord) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x)
    (hfg : AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g) coord := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab z hz hzxy ↦ ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab hz hzxy) (hg.2 hx hy ha hb hab hz hzxy)
    (add_nonneg (smul_nonneg ha <| hf₀ hx) <| smul_nonneg hb <| hf₀ hy)
    (hg₀ hz)).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by simp_rw [hab, mul_one]
    _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = _ := ?_
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a, ← smul_smul_smul_comm b, ← smul_smul_smul_comm a b,
    ← smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b a,
    add_comm ((a * b) • f x • g y), add_comm ((a * b) • f x • g y), add_add_add_comm]

lemma ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f coord)
    (hg : ConvexOn 𝕜 s g coord) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0)
    (hfg : AntivaryOn f g s) : ConcaveOn 𝕜 s (f • g) coord := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 <| hf₀ hx) (fun x hx ↦ neg_nonneg.2 <| hg₀ hx)
    hfg.neg

lemma ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f coord) (hg : ConcaveOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) coord := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 <| hf₀ hx) (fun x hx ↦ neg_nonneg.2 <| hg₀ hx)
    hfg.neg

lemma ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f coord) (hg : ConcaveOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) coord := by
  rw [← neg_convexOn_iff, ← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 <| hg₀ hx) hfg.neg_right

lemma ConcaveOn.smul_convexOn [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f coord)
    (hg : ConvexOn 𝕜 s g coord) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0)
    (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) coord := by
  rw [← neg_concaveOn_iff, ← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 <| hg₀ hx) hfg.neg_right

lemma ConvexOn.smul_concaveOn' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f coord)
    (hg : ConcaveOn 𝕜 s g coord) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x)
    (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) coord := by
  rw [← neg_concaveOn_iff, ← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 <| hg₀ hx) hfg.neg_right

lemma ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f coord) (hg : ConvexOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) coord := by
  rw [← neg_convexOn_iff, ← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 <| hg₀ hx) hfg.neg_right

variable [IsOrderedModule 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] {f g : D → E}

lemma ConvexOn.mul (hf : ConvexOn 𝕜 s f coord) (hg : ConvexOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) coord := hf.smul' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul (hf : ConcaveOn 𝕜 s f coord) (hg : ConcaveOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) coord := hf.smul' hg hf₀ hg₀ hfg

lemma ConvexOn.mul' (hf : ConvexOn 𝕜 s f coord) (hg : ConvexOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) coord := hf.smul'' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f coord) (hg : ConcaveOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) coord := hf.smul'' hg hf₀ hg₀ hfg

lemma ConvexOn.mul_concaveOn (hf : ConvexOn 𝕜 s f coord) (hg : ConcaveOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) coord := hf.smul_concaveOn hg hf₀ hg₀ hfg

lemma ConcaveOn.mul_convexOn (hf : ConcaveOn 𝕜 s f coord) (hg : ConvexOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) coord := hf.smul_convexOn hg hf₀ hg₀ hfg

lemma ConvexOn.mul_concaveOn' (hf : ConvexOn 𝕜 s f coord) (hg : ConcaveOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) coord := hf.smul_concaveOn' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul_convexOn' (hf : ConcaveOn 𝕜 s f coord) (hg : ConvexOn 𝕜 s g coord)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) coord := hf.smul_convexOn' hg hf₀ hg₀ hfg

lemma ConvexOn.pow (hf : ConvexOn 𝕜 s f coord) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) :
    ∀ n, ConvexOn 𝕜 s (f ^ n) coord
  | 0 => ⟨hf.1, fun _ _ _ _ _ _ _ _ hab _ _ _ ↦ by simpa using (Convex.combo_self hab (1 : E)).ge⟩
  | n + 1 => by
    rw [pow_succ']
    exact hf.mul (hf.pow hf₀ _) hf₀ (fun x hx ↦ pow_nonneg (hf₀ hx) _) <|
      (monovaryOn_self f s).pow_right₀ hf₀ n

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n`. -/
lemma convexOn_pow : ∀ n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 ↦ x ^ n :=
  (convexOn_id <| convex_Ici _).pow fun _ ↦ id

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even. -/
protected lemma Even.convexOn_pow {n : ℕ} (hn : Even n) : ConvexOn 𝕜 univ fun x : 𝕜 ↦ x ^ n := by
  obtain ⟨n, rfl⟩ := hn
  simp_rw [← two_mul, pow_mul]
  refine ConvexOn.pow (convexOn_iff.2 ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ sub_nonneg.1 ?_⟩)
    (fun _ _ ↦ by positivity) _
  calc
    (0 : 𝕜) ≤ (a * b) * (x - y) ^ 2 := by positivity
    _ = _ := by obtain rfl := eq_sub_of_add_eq hab; simp only [smul_eq_mul]; ring

end LinearOrderedCommRing

section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m`. A negative power exists only at invertible
elements, so the function is defined on the positive elements `Ioi 0` and is convex in the
coordinate `Subtype.val`. -/
lemma convexOn_zpow (n : ℤ) :
    ConvexOn 𝕜 univ (fun x : Ioi (0 : 𝕜) ↦ Checked.zpow (x : 𝕜) n fun _ ↦ x.2.ne'.isUnit)
      Subtype.val := by
  have himage : Convex 𝕜 ((Subtype.val : Ioi (0 : 𝕜) → 𝕜) '' univ) := by
    rw [image_univ, Subtype.range_coe]
    exact convex_Ioi 0
  rcases n with n | n
  · refine ⟨himage, fun x _ y _ a b ha hb hab z _ hz ↦ ?_⟩
    simp only [Int.ofNat_eq_natCast, zpow_natCast₀, hz]
    exact (convexOn_pow n).map_combo_le x.2.le y.2.le ha hb hab
  -- `x ^ -[n+1] = x⁻¹ ^ (n + 1)` is a power of the convex nonnegative function `x ↦ x⁻¹`.
  have hinv : ConvexOn 𝕜 univ (fun x : Ioi (0 : 𝕜) ↦ Checked.inv (x : 𝕜) x.2.ne'.isUnit)
      Subtype.val := by
    refine ⟨himage, fun x _ y _ a b ha hb hab z _ hz ↦ ?_⟩
    have hx : (0 : 𝕜) < x := x.2
    have hy : (0 : 𝕜) < y := y.2
    obtain rfl : b = 1 - a := eq_sub_of_add_eq' hab
    simp only [smul_eq_mul] at hz ⊢
    simp only [hz]
    have hxy : 0 < a * (x : 𝕜) + (1 - a) * y := by
      rw [← hz]
      exact z.2
    have key : a * (x : 𝕜)⁻¹ + (1 - a) * (y : 𝕜)⁻¹ - (a * x + (1 - a) * y)⁻¹ =
        a * (1 - a) * ((x : 𝕜) - y) ^ 2 / (x * y * (a * x + (1 - a) * y)) := by
      field_simp
      ring
    have : 0 ≤ a * (1 - a) * ((x : 𝕜) - y) ^ 2 / (x * y * (a * x + (1 - a) * y)) := by
      have : 0 ≤ 1 - a := hb
      positivity
    rw [← sub_nonneg, key]
    exact this
  refine (hinv.pow (fun x _ ↦ (inv_pos_of_pos x.2).le) (n + 1)).congr fun x _ ↦ ?_
  simp only [Pi.pow_apply]
  rw [zpow_negSucc₀, inv_pow₀]

end LinearOrderedField
