module

public import RequestProject.Euler.RadialSobolev

/-!
# Distributional curl of the actual circular velocity

The continuous two-interface radial velocity has precisely the prescribed
piecewise constant vorticity. Forward averages justify integration by parts
without differentiating across the two circular interfaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace Euler2D

def cellCurlProfile (s : ℝ) : ℝ :=
  if s < 3 / 5 then 1 else if s < 1 then -(3 / 2) else 0

def cellOmegaSqDeriv (s : ℝ) : ℝ :=
  if s < 3 / 5 then 0 else if s < 1 then -(3 / 4) * (s ^ 2)⁻¹ else 0

def centeredCellW (x : R2) : ℝ := cellW (x - torusCenter)

lemma cellW_eq_cellCurlProfile (x : R2) : cellW x = cellCurlProfile (‖x‖ ^ 2) := by
  have ha := cellA_pos
  have ha2 := cellA_sq
  have hna : ‖x‖ < cellA ↔ ‖x‖ ^ 2 < (3 / 5 : ℝ) := by
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  have hn1 : ‖x‖ < 1 ↔ ‖x‖ ^ 2 < (1 : ℝ) := by
    constructor <;> intro h <;> nlinarith [norm_nonneg x]
  by_cases hs : ‖x‖ ^ 2 < (3 / 5 : ℝ)
  · have hs1 : ‖x‖ ^ 2 < (1 : ℝ) := by linarith
    norm_num [cellW, twoInterface, cellCurlProfile, hna, hn1, hs, hs1]
  · by_cases hs1 : ‖x‖ ^ 2 < (1 : ℝ) <;>
      simp [cellW, twoInterface, cellCurlProfile, hna, hn1, hs, hs1]

lemma cellOmegaSq_eq_half {s : ℝ} (hs : s ≤ 3 / 5) : cellOmegaSq s = 1 / 2 := by
  unfold cellOmegaSq
  rw [max_eq_right hs, min_eq_left (by norm_num : (3 / 5 : ℝ) ≤ 1)]
  norm_num

lemma cellOmegaSq_eq_inv {s : ℝ} (hs : 3 / 5 ≤ s) (hs1 : s ≤ 1) :
    cellOmegaSq s = (3 / 4 : ℝ) * (s⁻¹ - 1) := by
  have hs0 : s ≠ 0 := by linarith
  unfold cellOmegaSq
  rw [max_eq_left hs, min_eq_left hs1]
  field_simp

lemma hasDerivAt_cellOmegaSq {s : ℝ} (ha : s ≠ 3 / 5) (h1 : s ≠ 1) :
    HasDerivAt cellOmegaSq (cellOmegaSqDeriv s) s := by
  by_cases hs : s < 3 / 5
  · have heq : cellOmegaSq =ᶠ[𝓝 s] fun _ => (1 / 2 : ℝ) := by
      filter_upwards [eventually_lt_nhds hs] with t ht
      exact cellOmegaSq_eq_half ht.le
    simpa only [cellOmegaSqDeriv, if_pos hs] using
      (hasDerivAt_const s (1 / 2 : ℝ)).congr_of_eventuallyEq heq
  · have hs' : (3 / 5 : ℝ) < s := lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm ha)
    by_cases hs1 : s < 1
    · have heq : cellOmegaSq =ᶠ[𝓝 s] fun t => (3 / 4 : ℝ) * (t⁻¹ - 1) := by
        filter_upwards [eventually_gt_nhds hs', eventually_lt_nhds hs1] with t ht ht1
        exact cellOmegaSq_eq_inv ht.le ht1.le
      have hd := ((hasDerivAt_inv (show s ≠ 0 by linarith)).sub_const 1).const_mul
        (3 / 4 : ℝ)
      simpa only [cellOmegaSqDeriv, if_neg hs, if_pos hs1, mul_neg, neg_mul] using
        hd.congr_of_eventuallyEq heq
    · have hs1' : 1 < s := lt_of_le_of_ne (le_of_not_gt hs1) (Ne.symm h1)
      have heq : cellOmegaSq =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hs1'] with t ht
        exact cellOmegaSq_eq_zero_of_one_le t ht.le
      simpa only [cellOmegaSqDeriv, if_neg hs, if_neg hs1] using
        (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq

lemma cellOmegaSq_curl_identity (s : ℝ) :
    2 * cellOmegaSq s + 2 * s * cellOmegaSqDeriv s = cellCurlProfile s := by
  by_cases hs : s < 3 / 5
  · rw [cellOmegaSq_eq_half hs.le]
    simp [cellOmegaSqDeriv, cellCurlProfile, hs]
  · by_cases hs1 : s < 1
    · rw [cellOmegaSq_eq_inv (le_of_not_gt hs) hs1.le]
      have hs0 : s ≠ 0 := by linarith
      simp only [cellOmegaSqDeriv, cellCurlProfile, if_neg hs, if_pos hs1]
      field_simp
      ring
    · rw [cellOmegaSq_eq_zero_of_one_le s (le_of_not_gt hs1)]
      simp [cellOmegaSqDeriv, cellCurlProfile, hs, hs1]

lemma tendsto_deriv_profileAverage_of_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f)
    {s d : ℝ} (hd : HasDerivAt f d s) :
    Tendsto (fun n => deriv (profileAverage f (radialApproxScale n)) s) atTop (𝓝 d) := by
  simpa only [deriv_profileAverage hf, smul_eq_mul] using
    hd.tendsto_slope_zero_right.comp tendsto_radialApproxScale

lemma ae_sq_radius_ne_interfaces :
    ∀ᵐ x ∂μT, ‖x - torusCenter‖ ^ 2 ≠ (3 / 5 : ℝ) ∧ ‖x - torusCenter‖ ^ 2 ≠ 1 := by
  have ha : ∀ᵐ x ∂volume, x ∉ sphere torusCenter cellA :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume torusCenter cellA)
  have h1 : ∀ᵐ x ∂volume, x ∉ sphere torusCenter (1 : ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume torusCenter 1)
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae h1] with x hxa hx1
  have hn := norm_nonneg (x - torusCenter)
  have hna : ‖x - torusCenter‖ ≠ cellA := by
    simpa only [mem_sphere_iff_norm] using hxa
  have hn1 : ‖x - torusCenter‖ ≠ 1 := by
    simpa only [mem_sphere_iff_norm] using hx1
  constructor
  · intro he
    exact hna (by nlinarith [cellA_sq, cellA_pos])
  · intro he
    exact hn1 (by nlinarith)

def approxCellCurl (n : ℕ) (x : R2) : ℝ :=
  2 * profileAverage cellOmegaSq (radialApproxScale n) (‖x - torusCenter‖ ^ 2) +
    2 * ‖x - torusCenter‖ ^ 2 *
      deriv (profileAverage cellOmegaSq (radialApproxScale n)) (‖x - torusCenter‖ ^ 2)

lemma tendsto_approxCellCurl_ae :
    ∀ᵐ x ∂μT, Tendsto (fun n => approxCellCurl n x) atTop (𝓝 (centeredCellW x)) := by
  filter_upwards [ae_sq_radius_ne_interfaces] with x hx
  have hd := tendsto_deriv_profileAverage_of_hasDerivAt continuous_cellOmegaSq
    (hasDerivAt_cellOmegaSq hx.1 hx.2)
  have hv := (tendsto_profileAverage continuous_cellOmegaSq (‖x - torusCenter‖ ^ 2)).const_mul 2
  have hlim := hv.add (hd.const_mul (2 * ‖x - torusCenter‖ ^ 2))
  simpa only [approxCellCurl, cellOmegaSq_curl_identity,
    centeredCellW, cellW_eq_cellCurlProfile] using hlim

lemma radialVelocity_curl {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c x : R2) :
    pd 0 (radialVelocity f c) x 1 - pd 1 (radialVelocity f c) x 0 =
      2 * f (‖x - c‖ ^ 2) + 2 * ‖x - c‖ ^ 2 * deriv f (‖x - c‖ ^ 2) := by
  unfold pd
  rw [fderiv_radialVelocity_apply hf, fderiv_radialVelocity_apply hf,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [EuclideanSpace.inner_single_right, perpJ, EuclideanSpace.single_apply]
  ring

theorem isCurl_of_C1_matching_faces {u : R2 → R2} (hu : ContDiff ℝ 1 u)
    (hfaces : MatchesTorusFaces u) :
    IsCurl u (fun x => pd 0 u x 1 - pd 1 u x 0) := by
  intro ψ hψ
  have huc (j : Fin 2) : Continuous (fun x => u x j) :=
    (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp hu.continuous
  have hduc (i j : Fin 2) : Continuous (fun x => pd i u x j) :=
    (EuclideanSpace.proj j : R2 →L[ℝ] ℝ).continuous.comp
      (continuous_pd_of_contDiff_one u hu i)
  have hpc (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hIBP01 := integral_coord_mul_pd_matching_faces hu hfaces 0 1 hψ
  have hIBP10 := integral_coord_mul_pd_matching_faces hu hfaces 1 0 hψ
  have hdint (i j : Fin 2) : Integrable (fun x => pd i u x j * ψ x) μT :=
    integrable_torusBox_of_continuous ((hduc i j).mul hψ.1.continuous)
  have huint (i j : Fin 2) : Integrable (fun x => u x i * pd j ψ x) μT :=
    integrable_torusBox_of_continuous ((huc i).mul (hpc j))
  simp_rw [sub_mul]
  rw [integral_sub (hdint 0 1) (hdint 1 0), integral_sub (huint 0 1) (huint 1 0)]
  linarith

lemma IsCurl.congr_ae {u v : R2 → R2} {w₀ w : R2 → ℝ} (hu : IsCurl u w₀)
    (huv : u =ᵐ[μT] v) (hωw : w₀ =ᵐ[μT] w) : IsCurl v w := by
  intro ψ hψ
  calc
    (∫ x in torusBox, w x * ψ x) = ∫ x in torusBox, w₀ x * ψ x := by
      apply integral_congr_ae
      filter_upwards [hωw] with x hx
      rw [hx]
    _ = ∫ x in torusBox, u x 0 * pd 1 ψ x - u x 1 * pd 0 ψ x := hu ψ hψ
    _ = ∫ x in torusBox, v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x := by
      apply integral_congr_ae
      filter_upwards [huv] with x hx
      rw [hx]

lemma isCurl_radialApproxLp_cell (n : ℕ) :
    IsCurl (radialApproxLp cellOmegaSq continuous_cellOmegaSq n) (approxCellCurl n) := by
  have hf := contDiff_profileAverage continuous_cellOmegaSq (radialApproxScale n)
  have hu := isCurl_of_C1_matching_faces (contDiff_radialVelocity hf torusCenter)
    (radialVelocity_matchesTorusFaces (fun s hs =>
      profileAverage_eq_zero continuous_cellOmegaSq cellOmegaSq_eq_zero_of_one_le
        (radialApproxScale_pos n) hs))
  apply hu.congr_ae (radialApproxLp_ae cellOmegaSq continuous_cellOmegaSq n).symm
  exact Eventually.of_forall (fun x => radialVelocity_curl (hf.differentiable one_ne_zero)
    torusCenter x)

lemma continuous_approxCellCurl (n : ℕ) : Continuous (approxCellCurl n) := by
  unfold approxCellCurl
  simp_rw [deriv_profileAverage continuous_cellOmegaSq]
  have hs : Continuous (fun x : R2 => ‖x - torusCenter‖ ^ 2) := by fun_prop
  exact (continuous_const.mul
    ((contDiff_profileAverage continuous_cellOmegaSq (radialApproxScale n)).continuous.comp hs)).add
    ((continuous_const.mul hs).mul (continuous_const.mul
      ((continuous_cellOmegaSq.comp (hs.add continuous_const)).sub
        (continuous_cellOmegaSq.comp hs))))

lemma norm_approxCellCurl_le (n : ℕ) (x : R2) (hx : x ∈ torusBox) :
    ‖approxCellCurl n x‖ ≤ 217 := by
  have hε := radialApproxScale_pos n
  have hs0 : 0 ≤ ‖x - torusCenter‖ ^ 2 := sq_nonneg _
  have hs36 : ‖x - torusCenter‖ ^ 2 ≤ 36 := by
    nlinarith [norm_sub_torusCenter_le_six x hx, norm_nonneg (x - torusCenter)]
  have ha := norm_profileAverage_cellOmegaSq_le_half hε hs0
  have hd := norm_deriv_profileAverage_cellOmegaSq_le_three hε (‖x - torusCenter‖ ^ 2)
  calc
    ‖approxCellCurl n x‖ ≤
        ‖2 * profileAverage cellOmegaSq (radialApproxScale n) (‖x - torusCenter‖ ^ 2)‖ +
        ‖2 * ‖x - torusCenter‖ ^ 2 *
          deriv (profileAverage cellOmegaSq (radialApproxScale n)) (‖x - torusCenter‖ ^ 2)‖ :=
      norm_add_le _ _
    _ = 2 * ‖profileAverage cellOmegaSq (radialApproxScale n) (‖x - torusCenter‖ ^ 2)‖ +
        2 * ‖x - torusCenter‖ ^ 2 *
          ‖deriv (profileAverage cellOmegaSq (radialApproxScale n)) (‖x - torusCenter‖ ^ 2)‖ := by
      simp only [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        Real.norm_of_nonneg hs0]
    _ ≤ 2 * (1 / 2 : ℝ) + 2 * 36 * 3 := by gcongr
    _ = 217 := by norm_num

lemma tendsto_integral_approxCellCurl {ψ : R2 → ℝ} (hψ : Continuous ψ) :
    Tendsto (fun n => ∫ x in torusBox, approxCellCurl n x * ψ x) atTop
      (𝓝 (∫ x in torusBox, centeredCellW x * ψ x)) := by
  apply tendsto_integral_of_dominated_convergence (μ := μT) (fun x => 217 * ‖ψ x‖)
  · intro n
    exact ((continuous_approxCellCurl n).mul hψ).aestronglyMeasurable
  · exact (integrable_torusBox_of_continuous hψ.norm).const_mul _
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_approxCellCurl_le n x hx) (norm_nonneg _)
  · filter_upwards [tendsto_approxCellCurl_ae] with x hx
    exact hx.mul_const (ψ x)

/-- The actual circular velocity has exactly the prescribed two-interface
vorticity, in the original torus distributional definition. -/
theorem isCurl_centeredCellVelocityLp : IsCurl centeredCellVelocityLp centeredCellW := by
  intro ψ hψ
  have hlim := tendsto_radialApproxLp continuous_cellOmegaSq
    cellOmegaSq_eq_zero_of_one_le centeredCellVelocityLp_ae_radial
  have hpd (i : Fin 2) : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsplit (v : L2T) :
      (∫ x in torusBox, v x 0 * pd 1 ψ x - v x 1 * pd 0 ψ x) =
        (∫ x in torusBox, v x 0 * pd 1 ψ x) - ∫ x in torusBox, v x 1 * pd 0 ψ x := by
    have hint (i j : Fin 2) : Integrable (fun x => v x i * pd j ψ x) μT := by
      obtain ⟨C, hC⟩ := bound_on_box (hpd j)
      exact integrable_lin v i (hpd j).aestronglyMeasurable hC
    exact integral_sub (hint 0 1) (hint 1 0)
  have hright : Tendsto
      (fun n => ∫ x in torusBox,
        radialApproxLp cellOmegaSq continuous_cellOmegaSq n x 0 * pd 1 ψ x -
        radialApproxLp cellOmegaSq continuous_cellOmegaSq n x 1 * pd 0 ψ x) atTop
      (𝓝 (∫ x in torusBox,
        centeredCellVelocityLp x 0 * pd 1 ψ x - centeredCellVelocityLp x 1 * pd 0 ψ x)) := by
    simp_rw [hsplit]
    exact (tendsto_fixed_lin hlim (hpd 1) 0).sub (tendsto_fixed_lin hlim (hpd 0) 1)
  exact tendsto_nhds_unique (tendsto_integral_approxCellCurl hψ.1.continuous)
    (hright.congr' (Eventually.of_forall fun n => (isCurl_radialApproxLp_cell n ψ hψ).symm))

end Euler2D

end
