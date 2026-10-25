module

public import RequestProject.Euler.PlanarWeakDivergenceMollification
public import RequestProject.Euler.Stationary
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Compact-test incompressibility follows from a genuine spatial C1
field with pointwise zero divergence. No spatial decay of the field
is needed, since the test function has compact support. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

private theorem compactSupport_test_pd {ψ : R2 → ℝ} (hs : HasCompactSupport ψ) (i : Fin 2) :
    HasCompactSupport (pd i ψ) :=
  (hs.fderiv ℝ).mono (fun x => mt (fun hx : fderiv ℝ ψ x = 0 => by simp only [pd, hx, ContinuousLinearMap.zero_apply]))

theorem integrable_planar_test_pairing {u : R2 → R2} (hu : Continuous u)
    {ψ : R2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x => ∑ i : Fin 2, u x i * pd i ψ x) := by
  apply integrable_finset_sum
  intro i _
  have hpi : Continuous (pd i ψ) := (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((EuclideanSpace.proj i).continuous.comp hu |>.mul hpi).integrable_of_hasCompactSupport
    (compactSupport_test_pd hs i).mul_left

theorem isPlanarWeaklyDivergenceFree_of_C1_divergence_zero
    {u : R2 → R2} (hu : ContDiff ℝ 1 u)
    (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0) :
    IsPlanarWeaklyDivergenceFree u := by
  intro ψ hψ hs
  have huc (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hpic (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have huic (i : Fin 2) : Continuous (pd i (fun y => u y i)) :=
    ((huc i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcomp (i : Fin 2) (x : R2) : pd i (fun y => u y i) x = pd i u x i :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) i i
  have hleft (i : Fin 2) : Integrable (fun x => u x i * pd i ψ x) :=
    ((huc i).continuous.mul (hpic i)).integrable_of_hasCompactSupport
      (compactSupport_test_pd hs i).mul_left
  have hright (i : Fin 2) : Integrable (fun x => pd i u x i * ψ x) := by
    have hi : Integrable (fun x => pd i (fun y => u y i) x * ψ x) :=
      ((huic i).mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    simpa only [hcomp] using hi
  have hibp (i : Fin 2) : (∫ x, u x i * pd i ψ x) = -(∫ x, pd i u x i * ψ x) := by
    have hi : Integrable (fun x => pd i (fun y => u y i) x * ψ x) :=
      ((huic i).mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hfg : Integrable (fun x => u x i * ψ x) :=
      ((huc i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := fun x => u x i) (g := ψ) (v := EuclideanSpace.single i 1)
      hi (hleft i) hfg ((huc i).differentiable one_ne_zero) (hψ.differentiable one_ne_zero)
    change (∫ x, u x i * pd i ψ x) = -(∫ x, pd i (fun y => u y i) x * ψ x) at hh
    simpa only [hcomp] using hh
  simp only [Fin.sum_univ_two]
  rw [integral_add (hleft 0) (hleft 1), hibp 0, hibp 1, ← neg_add,
    ← integral_add (hright 0) (hright 1)]
  simp_rw [← add_mul, hdiv, zero_mul]
  simp

theorem IsPlanarWeaklyDivergenceFree.add {u v : R2 → R2}
    (hu : IsPlanarWeaklyDivergenceFree u) (hv : IsPlanarWeaklyDivergenceFree v)
    (huc : Continuous u) (hvc : Continuous v) :
    IsPlanarWeaklyDivergenceFree (fun x => u x + v x) := by
  intro ψ hψ hs
  have he (x : R2) : (∑ i : Fin 2, (u x + v x) i * pd i ψ x) =
      (∑ i : Fin 2, u x i * pd i ψ x) + ∑ i : Fin 2, v x i * pd i ψ x := by
    simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib]
  simp_rw [he]
  rw [integral_add (integrable_planar_test_pairing huc hψ hs)
    (integrable_planar_test_pairing hvc hψ hs), hu ψ hψ hs, hv ψ hψ hs, zero_add]

end Euler2D

end
