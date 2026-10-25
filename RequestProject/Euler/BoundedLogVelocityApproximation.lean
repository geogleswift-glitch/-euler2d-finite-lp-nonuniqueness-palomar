module

public import RequestProject.Euler.BoundedVelocityMollificationModulus
public import RequestProject.Euler.TorusKernelSymmetry

/-! Explicit smooth bounded Lipschitz approximations to a bounded
logarithmically continuous planar velocity. The mollifier is an actual
normalized positive compact bump at the origin. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Convolution ContDiff UniformConvergence

namespace Euler2D

def planarVelocityMollifierBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : R2) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := half_pos hε
  rIn_lt_rOut := half_lt_self hε

def planarVelocityMollifier (ε : ℝ) (hε : 0 < ε) (x : R2) : ℝ :=
  ((planarVelocityMollifierBump ε hε).normed volume x +
    (planarVelocityMollifierBump ε hε).normed volume (perpJ x)) / 2

theorem planarVelocityMollifier_nonneg {ε : ℝ} (hε : 0 < ε) (x : R2) :
    0 ≤ planarVelocityMollifier ε hε x := by
  exact div_nonneg (add_nonneg
    ((planarVelocityMollifierBump ε hε).nonneg_normed (μ := volume) x)
    ((planarVelocityMollifierBump ε hε).nonneg_normed (μ := volume) (perpJ x))) (by norm_num)

theorem planarVelocityMollifier_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (planarVelocityMollifier ε hε) := by
  have hφ : ContDiff ℝ ∞ ((planarVelocityMollifierBump ε hε).normed volume) :=
    (planarVelocityMollifierBump ε hε).contDiff_normed (μ := volume)
  exact (hφ.add (hφ.comp perpJL.contDiff)).div_const 2

theorem planarVelocityMollifier_zero {ε : ℝ} (hε : 0 < ε) {x : R2} (hx : ε ≤ ‖x‖) :
    planarVelocityMollifier ε hε x = 0 := by
  unfold planarVelocityMollifier ContDiffBump.normed
  rw [(planarVelocityMollifierBump ε hε).zero_of_le_dist
    (by simpa only [dist_zero_right, planarVelocityMollifierBump] using hx),
    (planarVelocityMollifierBump ε hε).zero_of_le_dist
      (by simpa only [dist_zero_right, norm_perpJ, planarVelocityMollifierBump] using hx)]
  norm_num

theorem planarVelocityMollifier_perpJ {ε : ℝ} (hε : 0 < ε) (x : R2) :
    planarVelocityMollifier ε hε (perpJ x) = planarVelocityMollifier ε hε x := by
  have hJJ : perpJ (perpJ x) = -x := by
    ext i
    fin_cases i <;> simp [perpJ]
  unfold planarVelocityMollifier ContDiffBump.normed
  rw [hJJ, (planarVelocityMollifierBump ε hε).neg]
  ring

theorem planarVelocityMollifier_compact {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (planarVelocityMollifier ε hε) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : R2) ε) isClosed_closedBall
  intro x hx
  apply planarVelocityMollifier_zero hε
  exact (lt_of_not_ge (fun h => hx (by simpa only [mem_closedBall, dist_zero_right] using h))).le

theorem planarVelocityMollifier_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (planarVelocityMollifier ε hε) :=
  (planarVelocityMollifier_smooth hε).continuous.integrable_of_hasCompactSupport
    (planarVelocityMollifier_compact hε)

theorem planarVelocityMollifier_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ x, planarVelocityMollifier ε hε x) = 1 := by
  let φ := (planarVelocityMollifierBump ε hε).normed volume
  have hi : Integrable φ := (planarVelocityMollifierBump ε hε).integrable_normed (μ := volume)
  have hj : Integrable (fun x => φ (perpJ x)) :=
    measurePreserving_perpJ.integrable_comp_of_integrable hi
  have hm : AEStronglyMeasurable φ (Measure.map perpJ volume) := by
    rw [measurePreserving_perpJ.map_eq]
    exact hi.aestronglyMeasurable
  have he := integral_map measurePreserving_perpJ.aemeasurable hm
  rw [measurePreserving_perpJ.map_eq] at he
  change (∫ x, (φ x + φ (perpJ x)) / 2) = 1
  rw [integral_div, integral_add hi hj, ← he]
  change ((∫ x, (planarVelocityMollifierBump ε hε).normed volume x) +
    (∫ x, (planarVelocityMollifierBump ε hε).normed volume x)) / 2 = 1
  rw [(planarVelocityMollifierBump ε hε).integral_normed]
  norm_num

def planarVelocityApproxScale (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) / 4

theorem planarVelocityApproxScale_pos (n : ℕ) : 0 < planarVelocityApproxScale n := by
  unfold planarVelocityApproxScale
  positivity

theorem planarVelocityApproxScale_le_half (n : ℕ) : planarVelocityApproxScale n ≤ 1 / 2 := by
  have hh : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  unfold planarVelocityApproxScale
  linarith

theorem tendsto_planarVelocityApproxScale : Tendsto planarVelocityApproxScale atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) / 4) atTop (𝓝 0)
  simpa only [zero_div] using
    (hh.div_const (4 : ℝ))

def smoothBoundedLogVelocityApproximation (v : ℝ → R2 → R2) (n : ℕ) : ℝ → R2 → R2 :=
  boundedVelocityMollification
    (planarVelocityMollifier (planarVelocityApproxScale n) (planarVelocityApproxScale_pos n)) v

theorem exists_smoothBoundedLogVelocityApproximation
    {v : ℝ → R2 → R2} {M C : ℝ≥0}
    (hv : Continuous (Function.uncurry v)) (hM : ∀ t x, ‖v t x‖ ≤ M)
    (hlip : ∀ t x z, ‖x - z‖ ≤ 1 / 2 →
      ‖v t x - v t z‖ ≤ C * logFlowModulus ‖x - z‖) :
    ∃ K : ℕ → ℝ≥0,
      (∀ n, IsBoundedLipschitzVelocity (smoothBoundedLogVelocityApproximation v n) (K n) M) ∧
      (∀ n t, ContDiff ℝ ∞ (smoothBoundedLogVelocityApproximation v n t)) ∧
      (∀ n t x z, ‖x - z‖ ≤ 1 / 2 →
        ‖smoothBoundedLogVelocityApproximation v n t x -
          smoothBoundedLogVelocityApproximation v n t z‖ ≤ C * logFlowModulus ‖x - z‖) ∧
      TendstoUniformly (fun n => Function.uncurry (smoothBoundedLogVelocityApproximation v n))
        (Function.uncurry v) atTop := by
  let φ : ℕ → R2 → ℝ := fun n =>
    planarVelocityMollifier (planarVelocityApproxScale n) (planarVelocityApproxScale_pos n)
  have hi (n : ℕ) : Integrable (φ n) := planarVelocityMollifier_integrable _
  have hp (n : ℕ) : ∀ x, 0 ≤ φ n x := planarVelocityMollifier_nonneg _
  have hm (n : ℕ) : (∫ x, φ n x) = 1 := planarVelocityMollifier_integral _
  have hc (n : ℕ) : HasCompactSupport (φ n) := planarVelocityMollifier_compact _
  have hs (n : ℕ) : ContDiff ℝ ∞ (φ n) := planarVelocityMollifier_smooth _
  choose K hK using (fun n => exists_lipschitz_boundedVelocityMollification (hc n) (hs n) hv hM)
  refine ⟨K, fun n => ⟨continuous_boundedVelocityMollification (hi n) hv hM,
    hK n, norm_boundedVelocityMollification_le (hi n) (hp n) (hm n) hM⟩,
    (fun n t => contDiff_boundedVelocityMollification (hc n) (hs n) hv t), ?_, ?_⟩
  · intro n t x z hxz
    exact boundedVelocityMollification_logFlowModulus_le (hi n) (hp n) (hm n) hv hM hlip t hxz
  · have hlim : Tendsto (fun n => (C : ℝ) * logFlowModulus (planarVelocityApproxScale n))
        atTop (𝓝 0) := by
      have he := (continuous_logFlowModulus.tendsto 0).comp tendsto_planarVelocityApproxScale
      simpa only [Function.comp_def, logFlowModulus, zero_mul, mul_zero, sub_zero] using
        he.const_mul (C : ℝ)
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn p
    rw [dist_eq_norm, norm_sub_rev]
    exact (norm_boundedVelocityMollification_sub_le (hi n) (hp n) (hm n)
      (fun x hx => planarVelocityMollifier_zero (planarVelocityApproxScale_pos n) hx)
      hv hM C.2 (planarVelocityApproxScale_pos n) (planarVelocityApproxScale_le_half n)
      hlip p.1 p.2).trans_lt hn

end Euler2D
