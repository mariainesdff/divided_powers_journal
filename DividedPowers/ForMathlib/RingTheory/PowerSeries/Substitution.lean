/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Substitutions in univariate power series

Here we specialize some results from `Mathlib.RingTheory.MvPowerSeries.Substitution` to the case of
univariate power series. In particular, we expand the API for the definition `PowerSeries.rescale`,
following the multivariate case.

We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Let `τ`, `R`, `S` be types, with `CommRing R`, `CommRing S`, and `Algebra R S`.

We endow `PowerSeries R` and `MvPowerSeries τ S` with the product topology induced by the
discrete topology on the coefficient rings.

## Main results

* `PowerSeries.hasSubst_of_constantCoeff_zero` : in the univariate case, having zero constant
  coefficient is enough for `HasSubst`.

* `PowerSeries.subst_linear_subst_scalar_comm` : when `p` is linear, substitution of `p` and then a
  scalar homothety is substitution of the homothety then `p`.

-/

namespace PowerSeries

variable {A R τ S: Type*} [CommRing A] [CommRing R] [Algebra A R] [CommRing S]

open MvPowerSeries.WithPiTopology

variable {a : MvPowerSeries τ S}

/- In the univariate case, having zero constant coefficient is enough for `HasSubst`.-/
theorem hasSubst_of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) : HasSubst a := by
  simp [HasSubst, ha, IsNilpotent.zero]

lemma subst_def [Algebra R S] (a : MvPowerSeries τ S) (f : PowerSeries R) :
    subst a f = MvPowerSeries.subst (fun _ ↦ a) f := rfl

lemma rescale_eq (r : R) (f : PowerSeries R) :
    rescale r f = MvPowerSeries.rescale (fun _ ↦ r) f := by
  ext n
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp only [pow_zero, Finsupp.prod_single_index, smul_eq_mul]

lemma rescale_eq_subst (r : R) (f : PowerSeries R) :
    PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f := by
  rw [rescale_eq, MvPowerSeries.rescale_eq_subst, X, subst, Pi.smul_def']

/-- Rescale power series, as an `AlgHom` -/
noncomputable def rescaleAlgHom (r : R) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.rescaleAlgHom (fun _ ↦ r)

lemma rescaleAlgHom_def (r : R) (f : PowerSeries R) :
    rescaleAlgHom r f = MvPowerSeries.rescaleAlgHom (fun _ ↦ r) f := by
  simp only [rescaleAlgHom]

theorem rescaleAlgHom_apply (r : R) :
    (rescaleAlgHom r) = rescale r := by
  ext f
  rw [rescale_eq, RingHom.coe_coe, rescaleAlgHom_def, MvPowerSeries.rescaleAlgHom_apply]

/-- When `p` is linear, substitution of `p` and then a scalar homothety is substitution of
  the homothety then `p`. -/
lemma subst_linear_subst_scalar_comm (a : R) {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin: ∀ d ∈ Function.support p, d.degree = 1) (f : PowerSeries R) :
    subst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply hasSubst_of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply MvPowerSeries.IsHomogeneous.coeff_eq_zero (p := 1) _ (by simp)
    simp only [MvPowerSeries.IsHomogeneous, MvPowerSeries.IsWeightedHomogeneous, ne_eq]
    intro d hd
    convert hp_lin d hd using 1
    simp [Finsupp.weight, Finsupp.linearCombination, Finsupp.degree]
    rfl
  rw [rescale_eq_subst, MvPowerSeries.rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' a) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.HasSubst.smul_X _),
    funext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X,
    ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_homogeneous_eq_smul hp_lin,
    subst, pow_one]

theorem rescale_map_eq_map_rescale' (φ : R →+* S) (r : R) (f : R⟦X⟧) :
    rescale (φ r) (PowerSeries.map φ f) =
      PowerSeries.map (φ : R →+* S) (rescale r f) := by
  ext n
  simp [coeff_rescale, coeff_map, map_mul, map_pow]

theorem rescale_map_eq_map_rescale [Algebra A S] (φ : R →ₐ[A] S) (a : A) (f : R⟦X⟧) :
    rescale (algebraMap A S a) (PowerSeries.map φ f) =
      PowerSeries.map (φ : R →+* S) (rescale (algebraMap A R a) f) := by
  rw [← rescale_map_eq_map_rescale', RingHom.coe_coe, AlgHom.commutes]

end PowerSeries
