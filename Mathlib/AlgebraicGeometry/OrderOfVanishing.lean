/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.

The order of vanishing `Scheme.ord f z hz` is defined at points `z` of codimension `1`, which `hz`
states, and takes values in `WithTop ℤ`: as for a discrete valuation, the order of `0` is `⊤`, and
every nonzero `f` has an integer order.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/--
Order of vanishing on a locally Noetherian integral scheme as a monoid with zero hom to `ℤᵐ⁰`.
-/
noncomputable
def ordHom (z : X) (hz : coheight z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)

lemma ordHom_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    ordHom x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

/--
The order of vanishing of an element of the function field of a locally Noetherian integral scheme
at a point `z` of codimension `1`. It is `⊤` for `f = 0` and an integer otherwise.
-/
@[no_expose]
noncomputable
def ord (f : X.functionField) (z : X) (hz : coheight z = 1) : WithTop ℤ :=
  WithZero.recZeroCoe ⊤ (fun a ↦ ((Multiplicative.toAdd a : ℤ) : WithTop ℤ)) (X.ordHom z hz f)

lemma ord_eq_top_iff {z : X} (hz : coheight z = 1) {f : X.functionField} :
    ord f z hz = ⊤ ↔ f = 0 := by
  rw [← map_eq_zero (ordHom z hz), ord]
  rcases eq_or_ne (ordHom z hz f) 0 with h | h
  · simp [h]
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h
    simp [← ha]

@[simp]
lemma ord_zero {z : X} (hz : coheight z = 1) : ord (0 : X.functionField) z hz = ⊤ :=
  (ord_eq_top_iff hz).2 rfl

lemma ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f ≠ 0) :
    ord f x hx = ((WithZero.unzero ((map_ne_zero (ordHom x hx)).mpr hf)).toAdd : ℤ) := by
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 ((map_ne_zero (ordHom x hx)).mpr hf)
  simp [ord, ← ha]

lemma ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} {n : ℤ} :
    ord f z hz = n ↔ ordHom z hz f = Multiplicative.ofAdd n := by
  rw [ord]
  rcases eq_or_ne (ordHom z hz f) 0 with h | h
  · simp [h]
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h
    simp only [← ha, WithZero.recZeroCoe_coe, WithTop.coe_eq_coe, WithZero.coe_inj]
    exact ⟨fun h ↦ by rw [← h, ofAdd_toAdd], fun h ↦ by rw [h, toAdd_ofAdd]⟩

@[simp]
lemma ord_mul {x : X} (hx : coheight x = 1) (f g : X.functionField) :
    ord (f * g) x hx = ord f x hx + ord g x hx := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  rw [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hx hg, ← WithTop.coe_add, ord_eq_iff hx,
    map_mul, ofAdd_add, ofAdd_toAdd, ofAdd_toAdd, WithZero.coe_mul, WithZero.coe_unzero,
    WithZero.coe_unzero]

lemma ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
    (hx : coheight x = 1) (hx' : x ∈ U) : ord (X.germToFunctionField U f) x hx = 0 := by
  rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, ord_eq_iff hx,
    ordHom_of_isUnit hf hx hx', ofAdd_zero]
  rfl

lemma ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ord f x hx ≤ ord g y hy ↔ ordHom x hx f ≤ ordHom y hy g := by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]

lemma le_ord_iff {x : X} (hx : coheight x = 1) {f : X.functionField}
    (hf : f ≠ 0) {n : ℤ} :
    n ≤ ord f x hx ↔ Multiplicative.ofAdd n ≤ ordHom x hx f := by
  rw [ord_eq_unzero_ordHom hx hf, WithTop.coe_le_coe]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le, le_unzero_iff]

lemma ord_add {x : X} (hx : coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f g : X.functionField) :
    min (ord f x hx) (ord g x hx) ≤ ord (f + g) x hx := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases hfg : f + g = 0
  · simp [hfg]
  rw [inf_le_iff, ord_le_ord_iff hx hx hf hfg, ord_le_ord_iff hx hx hg hfg]
  exact inf_le_iff.mp <| Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg

lemma ord_le_smul {x : X} (hx : coheight x = 1) {U : X.Opens} [Nonempty U] (hxU : x ∈ U)
    (a : Γ(X, U)) (f : X.functionField) : ord f x hx ≤ ord (a • f) x hx := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f ≠ 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU).hom]
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  simp [ordHom, Ring.ordFrac_le_smul, RingHom.algebraMap_toAlgebra, map_ne_zero_iff,
    germ_injective_of_isIntegral, ha]

end AlgebraicGeometry.Scheme
