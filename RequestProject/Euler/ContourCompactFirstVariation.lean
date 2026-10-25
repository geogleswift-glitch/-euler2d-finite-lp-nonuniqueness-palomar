module

public import RequestProject.Euler.ContourCompactLinearFamilyIntegral
public import RequestProject.Euler.ContourSelfLogBaseSmooth
public import RequestProject.Euler.ContourLogDerivative

/-! Explicit first variations of the actual logarithmic integrand and
of compact linear-family integrals. These are derivatives of the true
Banach-valued integrals, not independently postulated linear operators. -/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ContDiff

namespace Euler2D

theorem fderiv_contourSelfLogFiniteKernel_apply (q v : ℂ × ℂ) (hq : q.1 ≠ 0) :
    fderiv ℝ contourSelfLogFiniteKernel q v =
      (v.1 / q.1).re • q.2 + Real.log ‖q.1‖ • v.2 := by
  have hp : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hφ : HasFDerivAt contourSelfLogFiniteKernel (fderiv ℝ contourSelfLogFiniteKernel q) q :=
    ((contDiffOn_contourSelfLogFiniteKernel q hq).contDiffAt
      ((isOpen_ne_fun continuous_fst continuous_const).mem_nhds hq)).differentiableAt
        (by simp) |>.hasFDerivAt
  have hd := hφ.comp_hasDerivAt_of_eq 0 hp (by simp)
  change HasDerivAt (fun t : ℝ => Real.log ‖q.1 + t • v.1‖ • (q.2 + t • v.2))
    (fderiv ℝ contourSelfLogFiniteKernel q v) 0 at hd
  have h1 : HasDerivAt (fun t : ℝ => q.1 + t • v.1) v.1 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v.1).const_add q.1
  have h2 : HasDerivAt (fun t : ℝ => q.2 + t • v.2) v.2 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v.2).const_add q.2
  have hl := hasDerivAt_log_norm_complex h1 (by simpa only [zero_smul, add_zero] using hq)
  have he := hl.smul h2
  simp only [zero_smul, add_zero] at he
  have hv := hd.unique he
  exact hv.trans (add_comm _ _)

variable {P V E₀ E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem compactLinearFamilyDerivativeCoefficient_apply
    (L : P →L[ℝ] V) (T : E₀ →L[ℝ] E) (A : V →L[ℝ] E₀) (v : P) :
    compactLinearFamilyDerivativeCoefficient L T A v = T (A (L v)) := by
  simp only [compactLinearFamilyDerivativeCoefficient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

theorem hasFDerivAt_weightedIntegral_compactLinearFamily
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) {W : Set V} (hW : IsOpen W)
    (L : ℝ → P →L[ℝ] V) (T : ℝ → E₀ →L[ℝ] E) (φ : V → E₀)
    (hL : ContinuousOn L S) (hT : ContinuousOn T S) (hφ : ContDiffOn ℝ 1 φ W)
    (himage : ∀ p ∈ U, ∀ u ∈ S, L u p ∈ W) {p₀ : P} (hp₀ : p₀ ∈ U) :
    HasFDerivAt (fun p => ∫ u in S, w u • T u (φ (L u p)))
      (∫ u in S, w u • compactLinearFamilyDerivativeCoefficient (L u) (T u)
        (fderiv ℝ φ (L u p₀))) p₀ := by
  let T' : ℝ → (V →L[ℝ] E₀) →L[ℝ] P →L[ℝ] E :=
    fun u => compactLinearFamilyDerivativeCoefficient (L u) (T u)
  have hT' : ContinuousOn T' S := continuousOn_compactLinearFamilyDerivativeCoefficient hL hT
  have hc := continuousOn_compactLinearFamily_composition L T φ hL hT hφ.continuousOn himage
  have hc' := continuousOn_compactLinearFamily_composition L T' (fderiv ℝ φ) hL hT'
    (hφ.continuousOn_fderiv_of_isOpen hW (by simp)) himage
  apply hasFDerivAt_banachWeightedSetIntegral_of_continuousOn_compact hS hw hU _ _ hc hc' _ hp₀
  intro p hp u hu
  have hφat : ContDiffAt ℝ 1 φ (L u p) :=
    (hφ (L u p) (himage p hp u hu)).contDiffAt (hW.mem_nhds (himage p hp u hu))
  exact (T u).hasFDerivAt.comp p
    ((hφat.differentiableAt (by simp)).hasFDerivAt.comp p (L u).hasFDerivAt)

attribute [local irreducible] compactLinearFamilyDerivativeCoefficient

set_option maxHeartbeats 600000 in
theorem fderiv_weightedIntegral_compactLinearFamily_apply
    {S : Set ℝ} (hS : IsCompact S) {w : ℝ → ℝ} (hw : IntegrableOn w S)
    {U : Set P} (hU : IsOpen U) {W : Set V} (hW : IsOpen W)
    (L : ℝ → P →L[ℝ] V) (T : ℝ → E₀ →L[ℝ] E) (φ : V → E₀)
    (hL : ContinuousOn L S) (hT : ContinuousOn T S) (hφ : ContDiffOn ℝ 1 φ W)
    (himage : ∀ p ∈ U, ∀ u ∈ S, L u p ∈ W) {p₀ : P} (hp₀ : p₀ ∈ U) (v : P) :
    fderiv ℝ (fun p => ∫ u in S, w u • T u (φ (L u p))) p₀ v =
      ∫ u in S, w u • T u (fderiv ℝ φ (L u p₀) (L u v)) := by
  let D : ℝ → (V →L[ℝ] E₀) →L[ℝ] P →L[ℝ] E :=
    fun u => compactLinearFamilyDerivativeCoefficient (L u) (T u)
  have hD : ContinuousOn D S := continuousOn_compactLinearFamilyDerivativeCoefficient hL hT
  have hc' : ContinuousOn (Function.uncurry (fun p u => D u (fderiv ℝ φ (L u p)))) (U ×ˢ S) :=
    continuousOn_compactLinearFamily_composition L D (fderiv ℝ φ) hL hD
      (hφ.continuousOn_fderiv_of_isOpen hW (by simp)) himage
  have hi : IntegrableOn (fun u => w u • compactLinearFamilyDerivativeCoefficient (L u) (T u)
      (fderiv ℝ φ (L u p₀))) S :=
    integrableOn_smul_continuousOn_compact hS hw
      (hc'.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hp₀, hu⟩))
  have hd := hasFDerivAt_weightedIntegral_compactLinearFamily hS hw hU hW L T φ
    hL hT hφ himage hp₀
  calc
    fderiv ℝ (fun p => ∫ u in S, w u • T u (φ (L u p))) p₀ v =
        (∫ u in S, w u • D u (fderiv ℝ φ (L u p₀))) v :=
      congrArg (fun A : P →L[ℝ] E => A v) hd.fderiv
    _ = ∫ u in S, (w u • D u (fderiv ℝ φ (L u p₀))) v :=
      ContinuousLinearMap.integral_apply hi v
    _ = ∫ u in S, w u • T u (fderiv ℝ φ (L u p₀) (L u v)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [ContinuousLinearMap.smul_apply]
      dsimp only [D]
      rw [compactLinearFamilyDerivativeCoefficient_apply]

end Euler2D

end
