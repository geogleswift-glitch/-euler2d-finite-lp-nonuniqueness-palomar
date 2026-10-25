module

public import RequestProject.Euler.RadialStationary
public import RequestProject.Euler.W1pLimit

/-!
# Sobolev bounds from classical derivatives on the fundamental square

Matching opposite face traces are sufficient for the distributional
derivatives in `MemW1p`. Quantitative bounds include the actual volume
factor of the square, so they can be used uniformly in approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

lemma integral_coord_mul_pd_matching_faces {u : R2 → R2}
    (hu : ContDiff ℝ 1 u) (hfaces : MatchesTorusFaces u)
    (i j : Fin 2) {ψ : R2 → ℝ} (hψ : IsScalarTest ψ) :
    (∫ x in torusBox, u x j * pd i ψ x) =
      -(∫ x in torusBox, pd i u x j * ψ x) := by
  have huc : ContDiff ℝ 1 (fun x => u x j) :=
    (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hfc : MatchesTorusFaces (fun x => u x j) :=
    fun x k hx => congrArg (fun y : R2 => y j) (hfaces x k hx)
  have hc (x : R2) : pd i (fun y => u y j) x = pd i u x j :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) i j
  simpa only [hc] using integral_mul_pd_matching_faces (fun x => u x j) ψ huc
    (hψ.1.of_le (by exact_mod_cast le_top)) hfc hψ.2.matchesTorusFaces i

theorem memW1p_of_C1_matching_faces {u : R2 → R2}
    (hu : ContDiff ℝ 1 u) (hfaces : MatchesTorusFaces u) (q : ENNReal) :
    MemW1p q u := by
  refine ⟨continuous_vector_memLp_torus hu.continuous q,
    fun i j x => pd i u x j, fun i j => ?_, fun i j ψ hψ => ?_⟩
  · exact continuous_memLp_torus
      ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one u hu i)) q
  · exact integral_coord_mul_pd_matching_faces hu hfaces i j hψ

/-- The explicit finite-volume conversion from a pointwise bound to an
`L^q` bound. It is valid also at exponent infinity. -/
def torusSobolevBound (q : ENNReal) (B : ℝ) : ℝ :=
  (μT univ ^ q.toReal⁻¹ * ENNReal.ofReal B).toReal

lemma torusSobolevBound_ne_top (q : ENNReal) (B : ℝ) :
    μT univ ^ q.toReal⁻¹ * ENNReal.ofReal B ≠ ∞ :=
  ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (measure_ne_top μT univ)) ENNReal.ofReal_ne_top

lemma eLpNorm_le_torusSobolevBound {F : Type*} [NormedAddCommGroup F]
    {f : R2 → F} {B : ℝ} (hf : AEStronglyMeasurable f μT)
    (q : ENNReal) (hb : ∀ x ∈ torusBox, ‖f x‖ ≤ B) :
    eLpNorm f q μT ≤ ENNReal.ofReal (torusSobolevBound q B) := by
  rw [torusSobolevBound, ENNReal.ofReal_toReal (torusSobolevBound_ne_top q B)]
  apply eLpNorm_le_of_ae_bound hf
  filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
  exact hb x hx

/-- Supremum bounds on the velocity and its actual first derivatives
give a uniform bound for the original distributional Sobolev predicate. -/
theorem w1pBoundedBy_of_C1_bounds {u : R2 → R2}
    (hu : ContDiff ℝ 1 u) (hfaces : MatchesTorusFaces u)
    (q : ENNReal) {B : ℝ}
    (hvel : ∀ x ∈ torusBox, ‖u x‖ ≤ B)
    (hgrad : ∀ i j x, x ∈ torusBox → |pd i u x j| ≤ B) :
    W1pBoundedBy q (torusSobolevBound q B) u := by
  refine ⟨continuous_vector_memLp_torus hu.continuous q,
    eLpNorm_le_torusSobolevBound
      (continuous_vector_memLp_torus hu.continuous q).aestronglyMeasurable q hvel,
    fun i j x => pd i u x j,
    fun i j => ⟨?_, ?_⟩, fun i j ψ hψ => ?_⟩
  · exact continuous_memLp_torus
      ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one u hu i)) q
  · exact eLpNorm_le_torusSobolevBound
      (continuous_memLp_torus
        ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
          (continuous_pd_of_contDiff_one u hu i)) q).aestronglyMeasurable
      q (by simpa only [Real.norm_eq_abs] using hgrad i j)
  · exact integral_coord_mul_pd_matching_faces hu hfaces i j hψ

/-- The same conversion using the actual support measure rather than the
whole square. This retains the small-radius factor in scaled blocks. -/
def torusLocalizedSobolevBound (q : ENNReal) (B : ℝ) (s : Set R2) : ℝ :=
  (μT s ^ q.toReal⁻¹ * ENNReal.ofReal B).toReal

lemma eLpNorm_le_torusLocalizedSobolevBound {F : Type*} [NormedAddCommGroup F]
    {f : R2 → F} {B : ℝ} (hf : AEStronglyMeasurable f μT)
    (hB : 0 ≤ B) (q : ENNReal) (s : Set R2)
    (hb : ∀ x ∈ torusBox, ‖f x‖ ≤ s.indicator (fun _ => B) x) :
    eLpNorm f q μT ≤ ENNReal.ofReal (torusLocalizedSobolevBound q B s) := by
  have hC : μT s ^ q.toReal⁻¹ * ENNReal.ofReal B ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
        (measure_ne_top μT s)) ENNReal.ofReal_ne_top
  rw [torusLocalizedSobolevBound, ENNReal.ofReal_toReal hC]
  let g : R2 → F := s.indicator f
  have hfg : f =ᵐ[μT] g := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
    by_cases hxs : x ∈ s
    · simp only [g, Set.indicator_of_mem hxs]
    · have hf0 : f x = 0 := norm_le_zero_iff.mp (by
        simpa only [Set.indicator_of_notMem hxs] using hb x hx)
      simp only [g, Set.indicator_of_notMem hxs, hf0]
  have hg : AEStronglyMeasurable g μT := hf.congr hfg
  have hgs : Function.support g ⊆ s := by
    intro x hx
    by_contra hxs
    exact hx (by simp only [g, Set.indicator_of_notMem hxs])
  have hgB : ∀ᵐ x ∂μT, ‖g x‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
    by_cases hxs : x ∈ s
    · simpa only [g, Set.indicator_of_mem hxs] using hb x hx
    · simpa only [g, Set.indicator_of_notMem hxs, norm_zero] using hB
  calc
    eLpNorm f q μT = eLpNorm g q μT := eLpNorm_congr_ae hfg
    _ = eLpNorm g q (μT.restrict s) :=
      (eLpNorm_restrict_eq_of_support_subset hg hgs).symm
    _ ≤ (μT.restrict s) univ ^ q.toReal⁻¹ * ENNReal.ofReal B :=
      eLpNorm_le_of_ae_bound hg.restrict
        (hgB.filter_mono (ae_mono Measure.restrict_le_self))
    _ = _ := by rw [Measure.restrict_apply_univ]

theorem w1pBoundedBy_of_C1_localized_bounds {u : R2 → R2}
    (hu : ContDiff ℝ 1 u) (hfaces : MatchesTorusFaces u)
    (q : ENNReal) {B : ℝ} (hB : 0 ≤ B) (s : Set R2)
    (hvel : ∀ x ∈ torusBox, ‖u x‖ ≤ s.indicator (fun _ => B) x)
    (hgrad : ∀ i j x, x ∈ torusBox → |pd i u x j| ≤ s.indicator (fun _ => B) x) :
    W1pBoundedBy q (torusLocalizedSobolevBound q B s) u := by
  refine ⟨continuous_vector_memLp_torus hu.continuous q,
    eLpNorm_le_torusLocalizedSobolevBound
      (continuous_vector_memLp_torus hu.continuous q).aestronglyMeasurable hB q s hvel,
    fun i j x => pd i u x j,
    fun i j => ⟨?_, ?_⟩, fun i j ψ hψ => ?_⟩
  · exact continuous_memLp_torus
      ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one u hu i)) q
  · exact eLpNorm_le_torusLocalizedSobolevBound
      (continuous_memLp_torus
        ((EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
          (continuous_pd_of_contDiff_one u hu i)) q).aestronglyMeasurable hB q s
      (by simpa only [Real.norm_eq_abs] using hgrad i j)
  · exact integral_coord_mul_pd_matching_faces hu hfaces i j hψ

end Euler2D

end
