module

public import RequestProject.Euler.CircularFixedGraphExistingCaptureStep
public import RequestProject.Euler.CircularReferenceUniformTube
public import RequestProject.Euler.CircularAreaChartQuadratic
public import RequestProject.Euler.BanachCurrentBlockEnvelope

/-! Capture on the same existing trajectory with its actual proportional
forcing. Membership in both comparison domains follows from a fixed
reference tube. All constants precede the physical parameters. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] captureBlockLittle_group captureBlockLittle_space
  captureBlockFamily_tower captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

theorem exists_circular_existing_proportional_capture_step {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ x) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : ℝ, 1 < q ∧ q ^ 2 < (lamMult ^ 2) ^ k ∧
      let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
      let g := fun v => x v 0 - v
      let T := ((2 * k : ℕ) : ℝ) * period
      ∃ C > 0, ∃ d > 0, d ≤ r₀ / 2 ∧ ∃ E > 0, ∃ r > 0,
      ∃ κ₀ > 0, ∃ ε₀ > 0, ∃ H > 0,
        ∀ α w, P α = α → P w = 0 → ‖α‖ + ‖w‖ ≤ d →
        ∀ {B κ : ℝ}, 0 ≤ B → 0 ≤ κ → κ ≤ κ₀ →
          B + κ * (‖α‖ + ‖w‖) ≤ ε₀ →
        ∀ y p : ℝ → Fin 2 → LittleContourSpace γ,
          y 0 = circularConstrainedChart hγ hγ1 (α + g α + w) →
          (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
          (∀ t ∈ Icc (0 : ℝ) T, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ r) →
          (∀ t ∈ Icc (0 : ℝ) T, ‖p t‖ ≤ B + κ * ‖y t - littleCircularMaterialContours hγ hγ1 t‖) →
          let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
            (y T - littleCircularReference hγ hγ1)
          ‖P v - (lamMult ^ 2) ^ k • α‖ ≤
              C * (‖α‖ + ‖w‖) ^ 2 + E * B + E * κ * (‖α‖ + ‖w‖) ∧
          ‖(v - P v) - g (P v)‖ ≤ q * ‖w‖ +
              C * (‖α‖ + ‖w‖) * ‖w‖ + E * B + E * κ * (‖α‖ + ‖w‖) ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H * (‖α‖ + ‖w‖ + B) := by
  obtain ⟨k, hk, q, hq, hgap, hcomp, C, hC, d₁, hd₁, hdr, η₀, hη₀, Bf, hBf, hflat⟩ :=
    exists_circularFixedGraph_forced_capture_block_bounds (γ := γ) (R := R) (r := r₀)
      (X := X) (x := x) hγ hγ1 hR hr₀ hX hd hfix harea hg
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let g := fun v => x v 0 - v
  let T : ℝ := ((2 * k : ℕ) : ℝ) * period
  have hT : 0 < T := mul_pos (Nat.cast_pos.mpr (by omega)) (by unfold period; positivity)
  obtain ⟨ρ, hρ, Z, hZ, hconj⟩ := exists_circular_sameFlow_material_block_return
    hγ hγ1 hR hX hd hfix harea (m := 2 * k) (by omega)
  obtain ⟨U₁, _, _, _, K₁, r₁, hr₁, δ, hδ, htube₁, hcompare⟩ :=
    exists_circular_existing_forced_interval_constants hγ hγ1 hT
  obtain ⟨U₂, _, _, _, K₂, r₂, hr₂, _, _, hLip, htube₂, _⟩ :=
    exists_circular_reference_uniform_lipschitz_tube hγ hγ1
  have hinput : ∀ᶠ v : CircularConstrainedTangentSpace γ in 𝓝 0,
      circularConstrainedChart hγ hγ1 v ∈ ball (littleCircularReference hγ hγ1) (min ρ δ) :=
    (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
      (by rw [circularConstrainedChart_zero]; exact ball_mem_nhds _ (lt_min hρ hδ))
  obtain ⟨ζ, hζ, hζprop⟩ := Metric.eventually_nhds_iff.mp (hinput.and hconj)
  obtain ⟨Cc, hCc, rc, hrc, hchart⟩ := exists_circularConstrainedChart_quadratic_bound hγ hγ1
  let d := min d₁ (min (ζ / 4) (rc / 2))
  have hdpos : 0 < d := lt_min hd₁ (lt_min (by positivity) (by positivity))
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let H₀ := 2 * Real.exp ((K₂ : ℝ) * T)
  let M := 2 * (1 + Cc * rc)
  have hH₀ : 0 < H₀ := by dsimp only [H₀]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  let Dε := 1 + H₀ * T + H₀ * M
  have hDε : 0 < Dε := by dsimp only [Dε]; positivity
  let Cf := ‖circularConstraintProjectionToTangentCLM hγ hγ1.le‖ *
    (T * Real.exp ((K₁ : ℝ) * T))
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  let E₀ := ‖P‖ * Cf + Bf * Cf + 1
  have hE₀ : 0 < E₀ := by dsimp only [E₀]; positivity
  let E := E₀ * Dε
  have hE : 0 < E := mul_pos hE₀ hDε
  let κ₀ := min 1 (2 * (T * Real.exp ((K₂ : ℝ) * T)))⁻¹
  have hκ₀ : 0 < κ₀ := lt_min zero_lt_one (by positivity)
  let ε₀ := η₀ / (Cf * Dε + 1)
  have hε₀ : 0 < ε₀ := div_pos hη₀ (by positivity)
  let H := H₀ * (M + T + 1)
  have hH : 0 < H := by dsimp only [H]; positivity
  refine ⟨k, hk, q, hq, hgap, C, hC, d, hdpos, (min_le_left _ _).trans hdr,
    E, hE, r, hr, κ₀, hκ₀, ε₀, hε₀, H, hH, ?_⟩
  intro α w hα hw hsize B κ hB hκ hκcap hforcing y p hinit hyd hnear hp
  let a := ‖α‖ + ‖w‖
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hκ1 : κ ≤ 1 := hκcap.trans (min_le_left _ _)
  have hsmall : 2 * (T * Real.exp ((K₂ : ℝ) * T)) * κ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hκcap.trans (min_le_right _ _))
      (show 0 ≤ 2 * (T * Real.exp ((K₂ : ℝ) * T)) by positivity)
    simpa only [mul_inv_cancel₀ (show 2 * (T * Real.exp ((K₂ : ℝ) * T)) ≠ 0 by positivity)] using hh
  have har : ‖α‖ ≤ r₀ / 2 :=
    (le_add_of_nonneg_right (norm_nonneg w)).trans (hsize.trans ((min_le_left _ _).trans hdr))
  have hxn := hg.norm_le α hα har 0
  simp only [pow_zero, mul_one] at hxn
  have hzn : ‖α + g α + w‖ ≤ 2 * a := by
    rw [show α + g α + w = x α 0 + w by dsimp only [g]; abel]
    have hh := (norm_add_le (x α 0) w).trans (add_le_add hxn le_rfl)
    dsimp only [a]
    linarith only [hh, norm_nonneg w]
  have haz : a ≤ ζ / 4 := hsize.trans ((min_le_right _ _).trans (min_le_left _ _))
  have harc : a ≤ rc / 2 := hsize.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzin : α + g α + w ∈ ball (0 : CircularConstrainedTangentSpace γ) ζ := by
    apply mem_ball_zero_iff.mpr
    linarith only [hzn, haz, hζ]
  have hzrc : α + g α + w ∈ closedBall (0 : CircularConstrainedTangentSpace γ) rc := by
    apply mem_closedBall_zero_iff.mpr
    linarith only [hzn, harc]
  have hy0 : ‖y 0 - littleCircularMaterialContours hγ hγ1 0‖ ≤ M * a := by
    rw [littleCircularMaterialContours_zero, hinit]
    have hh := (hchart _ hzrc).2.trans
      (mul_le_mul_of_nonneg_left hzn (by positivity : 0 ≤ 1 + Cc * rc))
    exact hh.trans_eq (by dsimp only [M]; ring)
  have hym₁ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : y t ∈ U₁ :=
    htube₁ t ht (by simpa only [mem_closedBall, dist_eq_norm] using (hnear t ht).trans (min_le_left _ _))
  have hym₂ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : y t ∈ U₂ :=
    htube₂ t (by simpa only [mem_closedBall, dist_eq_norm] using (hnear t ht).trans (min_le_right _ _))
  have hbound := current_existing_block_envelope hLip hT.le hB hκ y
    (littleCircularMaterialContours hγ hγ1) p hyd
    (fun t _ => by simpa only [circularBanachField] using
      littleCircularMaterialContours_hasDerivAt hγ hγ1 t) hym₂
    (fun t _ => htube₂ t (mem_closedBall_self hr₂.le)) hp hsmall
  have hbound' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ H₀ * (M * a + T * B) :=
    (hbound t ht).trans (mul_le_mul_of_nonneg_left (add_le_add hy0 le_rfl) hH₀.le)
  let ε := B + κ * (H₀ * (M * a + T * B))
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hpc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖p t‖ ≤ ε :=
    (hp t ht).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbound' t ht) hκ))
  have hεle : ε ≤ Dε * (B + κ * a) := by
    have hh := mul_le_mul_of_nonneg_right hκ1 (show 0 ≤ H₀ * T * B by positivity)
    have hcoef₁ : 1 + H₀ * T ≤ Dε := by
      dsimp only [Dε]
      linarith [mul_nonneg hH₀.le hM.le]
    have hcoef₂ : H₀ * M ≤ Dε := by
      dsimp only [Dε]
      linarith [mul_nonneg hH₀.le hT.le]
    have h₁ := mul_le_mul_of_nonneg_right hcoef₁ hB
    have h₂ := mul_le_mul_of_nonneg_right hcoef₂ (mul_nonneg hκ ha)
    dsimp only [ε]
    nlinarith only [hh, h₁, h₂]
  have hη : Cf * ε ≤ η₀ := by
    have hh := (le_div_iff₀ (by positivity : 0 < Cf * Dε + 1)).mp hforcing
    have he := mul_le_mul_of_nonneg_left hεle hCf
    have hba : 0 ≤ B + κ * a := by positivity
    dsimp only [a] at he hba ⊢
    nlinarith only [hh, he, hba]
  have hyc : ContinuousOn y (Icc (0 : ℝ) T) :=
    fun t ht => (hyd t ht).continuousAt.continuousWithinAt
  have hdistance := hcompare hZ hε (hζprop hzin).1 hinit hyc hyd hym₁ hpc T ⟨hT.le, le_rfl⟩
  have hout := (circularConstrainedReturnMap_difference_le hγ hγ1
    (fun W => Z W T) (fun _ => y T) (α + g α + w)).trans
      (mul_le_mul_of_nonneg_left hdistance (norm_nonneg _))
  rw [(hζprop hzin).2] at hout
  let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (y T - littleCircularReference hγ hγ1)
  have herr : ‖v - F^[2 * k] (α + g α + w)‖ ≤ Cf * ε := by
    have hconstant : circularConstrainedReturnMap hγ hγ1 (fun _ => y T) (α + g α + w) = v := by
      unfold circularConstrainedReturnMap
      rfl
    rw [hconstant] at hout
    change ‖v - F^[2 * k] (α + g α + w)‖ ≤ _ at hout
    exact hout.trans_eq (by dsimp only [Cf]; ring)
  have hb := hflat α w hα hw (hsize.trans (min_le_left _ _)) v
    (mul_nonneg hCf hε) hη herr
  have hPcf : ‖P‖ * Cf ≤ E₀ := by
    dsimp only [E₀]
    linarith [mul_nonneg hBf.le hCf]
  have hBcf : Bf * Cf ≤ E₀ := by
    dsimp only [E₀]
    linarith [mul_nonneg (norm_nonneg P) hCf]
  have hEbudget : E₀ * ε ≤ E * B + E * κ * a := by
    have hh := mul_le_mul_of_nonneg_left hεle hE₀.le
    exact hh.trans_eq (by dsimp only [E]; ring)
  have hE₁ : ‖P‖ * (Cf * ε) ≤ E * B + E * κ * a := by
    have hm : ‖P‖ * (Cf * ε) ≤ E₀ * ε := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hPcf hε
    exact hm.trans hEbudget
  have hE₂ : Bf * (Cf * ε) ≤ E * B + E * κ * a := by
    have hm : Bf * (Cf * ε) ≤ E₀ * ε := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hBcf hε
    exact hm.trans hEbudget
  refine ⟨by have hh := hb.1.trans (add_le_add le_rfl hE₁); simpa only [a, add_assoc] using hh, ?_, ?_⟩
  · have hn := norm_le_norm_sub_add ((v - P v) - g (P v))
      ((((fderiv ℝ F 0) ^ 2) ^ k) w)
    have hl := hcomp w hw
    have hh := hb.2.trans (add_le_add le_rfl hE₂)
    dsimp only [a] at hh
    change ‖(v - P v) - g (P v)‖ ≤ _
    linarith only [hn, hl, hh]
  · intro t ht
    have hh : M * a + T * B ≤ (M + T + 1) * (a + B) := by
      nlinarith only [mul_nonneg hM.le hB, mul_nonneg hT.le ha, ha, hB]
    exact (hbound' t ht).trans ((mul_le_mul_of_nonneg_left hh hH₀.le).trans_eq
      (by dsimp only [H, a]; ring))

end Euler2D

end
