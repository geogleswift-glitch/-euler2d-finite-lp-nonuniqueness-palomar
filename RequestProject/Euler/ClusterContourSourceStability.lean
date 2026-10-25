module

public import RequestProject.Euler.CircularPhysicalContourLittle
public import RequestProject.Euler.PhaseOuterRadialBounds
public import RequestProject.Euler.LabelInteractions

/-! Strong L1 stability of the true inner-cluster field in the original
Little contour norm, on targets separated from the actual source. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_clusterContourLittle {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {w : ℂ → ℝ} {a M₄ d : ℝ} (ha : 0 ≤ a) (hw : Integrable w)
    (hsupp : ∀ y, a < ‖y‖ → w y = 0) (hmass : ∫ y, w y = 0)
    (hsym : ∀ y, w (I * y) = w y)
    (hM : (∫ y : ℂ, ‖y‖ ^ 4 * |w y|) ≤ M₄) (hd : 0 < d) (hsep : 8 * a ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖) :
    ∃ Q : LittleContourSpace γ,
      (∀ θ, LittleContourSpace.lift γ Q θ = velocityC w (LittleContourSpace.lift γ Z θ)) ∧
      ‖Q‖ ≤ cauchyContourNormBudget 5 (γ : ℝ) M₄ d ‖Z‖ := by
  obtain ⟨Q, hQ, hn⟩ := exists_clusterContourFieldC1 hγ1 ha hw hsupp hmass hsym hM hd
    (by linarith) Z.val hZ
  have hmem := clusterContourFieldC1_mem_little hγ1 ha hw hsupp hmass hsym hM hd hsep Z hZ Q hQ
  exact ⟨⟨Q, hmem⟩, hQ, hn⟩

theorem norm_clusterContourLittle_sub_source_le {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {u v : ℂ → ℝ} {a d Mu Mv : ℝ}
    (ha : 0 ≤ a) (hu : Integrable u) (hv : Integrable v)
    (hMu : ∀ y, |u y| ≤ Mu) (hMv : ∀ y, |v y| ≤ Mv)
    (hsu : ∀ y, a < ‖y‖ → u y = 0) (hsv : ∀ y, a < ‖y‖ → v y = 0)
    (hmu : ∫ y, u y = 0) (hmv : ∫ y, v y = 0)
    (hyu : ∀ y, u (I * y) = u y) (hyv : ∀ y, v (I * y) = v y)
    (hd : 0 < d) (hsep : 8 * a ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖)
    (Qu Qv : LittleContourSpace γ)
    (hQu : ∀ θ, LittleContourSpace.lift γ Qu θ = velocityC u (LittleContourSpace.lift γ Z θ))
    (hQv : ∀ θ, LittleContourSpace.lift γ Qv θ = velocityC v (LittleContourSpace.lift γ Z θ)) :
    ‖Qu - Qv‖ ≤ cauchyContourNormBudget 5 (γ : ℝ)
      (a ^ 4 * ∫ y, |u y - v y|) d ‖Z‖ := by
  have hi : Integrable (fun y => u y - v y) := hu.sub hv
  have hs : ∀ y, a < ‖y‖ → u y - v y = 0 := by
    intro y hy
    rw [hsu y hy, hsv y hy, sub_self]
  have hm : (∫ y, u y - v y) = 0 := by rw [integral_sub hu hv, hmu, hmv, sub_self]
  have hy : ∀ y, u (I * y) - v (I * y) = u y - v y := by
    intro y
    rw [hyu y, hyv y]
  obtain ⟨Q, hQ, hn⟩ := exists_clusterContourLittle hγ1 ha hi hs hm hy
    (fourth_le_mass hi hs) hd hsep Z hZ
  have he : Q = Qu - Qv := by
    apply Subtype.ext
    apply ContourC1Space.ext
    intro x
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
    change LittleContourSpace.lift γ Q θ = LittleContourSpace.lift γ Qu θ - LittleContourSpace.lift γ Qv θ
    rw [hQ θ, hQu θ, hQv θ]
    exact velocityC_sub_of_bounded hu hv hMu hMv _
  rwa [he] at hn

theorem tendsto_clusterContourLittle_of_L1 {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    {α : Type*} {l : Filter α} {u : α → ℂ → ℝ} {v : ℂ → ℝ} {a d Mu Mv : ℝ}
    (ha : 0 ≤ a) (hu : ∀ i, Integrable (u i)) (hv : Integrable v)
    (hMu : ∀ i y, |u i y| ≤ Mu) (hMv : ∀ y, |v y| ≤ Mv)
    (hsu : ∀ i y, a < ‖y‖ → u i y = 0) (hsv : ∀ y, a < ‖y‖ → v y = 0)
    (hmu : ∀ i, ∫ y, u i y = 0) (hmv : ∫ y, v y = 0)
    (hyu : ∀ i y, u i (I * y) = u i y) (hyv : ∀ y, v (I * y) = v y)
    (hd : 0 < d) (hsep : 8 * a ≤ d)
    (Z : LittleContourSpace γ) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF γ Z.val x‖)
    (Qu : α → LittleContourSpace γ) (Qv : LittleContourSpace γ)
    (hQu : ∀ i θ, LittleContourSpace.lift γ (Qu i) θ = velocityC (u i) (LittleContourSpace.lift γ Z θ))
    (hQv : ∀ θ, LittleContourSpace.lift γ Qv θ = velocityC v (LittleContourSpace.lift γ Z θ))
    (hL1 : Tendsto (fun i => ∫ y, |u i y - v y|) l (𝓝 0)) :
    Tendsto Qu l (𝓝 Qv) := by
  have hc : Continuous (fun m : ℝ => cauchyContourNormBudget 5 (γ : ℝ) (a ^ 4 * m) d ‖Z‖) := by
    unfold cauchyContourNormBudget cauchySpatialDerivativeBudget
    fun_prop
  have hb : Tendsto (fun i => cauchyContourNormBudget 5 (γ : ℝ)
      (a ^ 4 * ∫ y, |u i y - v y|) d ‖Z‖) l (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, cauchyContourNormBudget, cauchySpatialDerivativeBudget,
      zero_div, mul_zero, add_zero, zero_mul, max_self] using hc.continuousAt.tendsto.comp hL1
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i => norm_nonneg _) (fun i =>
    norm_clusterContourLittle_sub_source_le hγ1 ha (hu i) hv (hMu i) hMv
      (hsu i) hsv (hmu i) hmv (hyu i) hyv hd hsep Z hZ (Qu i) Qv (hQu i) hQv) hb

end Euler2D

end
