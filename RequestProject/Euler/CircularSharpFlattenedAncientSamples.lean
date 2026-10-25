module

public import RequestProject.Euler.CircularAncientSharpMaterialOrbit
public import RequestProject.Euler.CircularFlattenedReturnBounds

/-! The original sharp construction retains its same material Y and
same actual period flow X, together with the flattened return budget.
Existing ancient-core modules are unchanged. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) sharpFlattenedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) sharpFlattenedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) sharpFlattenedFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) sharpFlattenedTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sharpFlattenedTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sharpFlattenedTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM
  circularConstrainedChart circularConstraintProjectionToTangentCLM circularConstrainedPatchFourthMoment


def HasCircularFlattenedAncientSamples {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Y : ℝ → Fin 2 → LittleContourSpace γ) : Prop :=
  ∃ R > 0, ∃ X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ,
    IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X ∧
    ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1) ∧
    X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1 ∧
    (∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i)) ∧
    ∃ r > 0, ∃ x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ,
      IsLocalWeightedBackwardGraph
        (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
        (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x ∧
      ∃ C > 0, ∃ s > 0, s ≤ r / 2 ∧
        (∀ α w, circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α →
          circularConstrainedUnstableProjectionCLM hγ hγ1.le w = 0 → ‖α‖ + ‖w‖ ≤ s →
          let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
          let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
          let L := fderiv ℝ F 0
          let g := fun v => x v 0 - v
          let z := α + g α + w
          ‖P (F z) - (-lamMult : ℝ) • α‖ ≤ C * (‖α‖ + ‖w‖) ^ 2 ∧
          ‖(F z - P (F z)) - g (P (F z)) - L w‖ ≤ C * (‖α‖ + ‖w‖) * ‖w‖) ∧
        ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
          circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r / 2 ∧
          Y (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (x α 0)

theorem hasCircularFlattenedAncientSamples_of_samples {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R : ℝ} (hR : 0 < R)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (y : ℕ → CircularConstrainedTangentSpace γ)
    (hback : ∀ n, banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period))
      (y (n + 1)) = y n)
    {B : ℝ} (hnorm : ∀ n, ‖y n‖ ≤ B * (circularAncientBackwardWeight⁻¹) ^ n)
    (Y : ℝ → Fin 2 → LittleContourSpace γ)
    (hYsamp : ∀ n : ℕ, Y (-(n : ℝ) * (period + period)) =
      circularConstrainedChart hγ hγ1 (y n)) :
    HasCircularFlattenedAncientSamples hγ hγ1 Y := by
  obtain ⟨r, hr, _hrr, x, hg, C, hC, s, hs, hsr, hbounds⟩ :=
    exists_circularConstrained_flattenedReturn_bounds hγ hγ1 hR hX hd hfix harea
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N, hN⟩ := circularAncient_samples_on_quadraticBackwardGraph hγ hγ1 hr hg
    y hback hnorm Y hYsamp
  refine ⟨R, hR, X, hX, hd, hfix, harea, r, hr, x, hg, C, hC, s, hs, hsr, hbounds, N, ?_⟩
  intro n hn
  have ht := hN n hn
  exact ⟨circularConstrainedUnstableProjectionCLM hγ hγ1.le (y n),
    circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le _, ht.1, ht.2.2⟩

theorem exists_circularAncientMaterial_sharp_with_flattenedGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ Y : ℝ → Fin 2 → LittleContourSpace γ,
    ∃ A : ℝ → (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ),
    ∃ v : CircularConstrainedTangentSpace γ, ∃ E > 0,
      ContinuousOn Y (Iic 0) ∧
      (∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s) ∧
      Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
        (𝓝 (littleCircularReference hγ hγ1)) ∧
      (∀ s ≤ 0, ∀ i, littleContourArea γ (Y s i) = Real.pi * circularContourRadii i ^ 2) ∧
      (∀ s ≤ 0, ∀ i, Y s i ∈ fourfoldLittleContourSubmodule γ) ∧
      Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ) ∧
      (∀ s ∈ Icc (0 : ℝ) (period + period), HasDerivAt A
        ((fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 s)).comp (A s)) s) ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le v = v ∧ v ≠ 0 ∧
      (∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) (period + period),
        ‖Y (-((n + 1 : ℕ) : ℝ) * (period + period) + s) - littleCircularMaterialContours hγ hγ1 s -
            ((lamMult ^ 2)⁻¹) ^ (n + 1) • A s v.val‖ ≤
          E * (circularAncientBackwardRatio ^ 2) ^ (n + 1)) ∧
      HasCircularFlattenedAncientSamples hγ hγ1 Y := by
  obtain ⟨R, hR, X, hX, hs, hfix, hnear, harea, hfour⟩ :=
    exists_circularContour_constrained_period_flow hγ hγ1 3
  have hp0 : 0 < period := by unfold period; positivity
  have hp : period ∈ Icc (0 : ℝ) period := ⟨hp0.le, le_rfl⟩
  have hD : 0 < period + period := by linarith
  have hd3 : ContDiffAt ℝ 3 (fun W => X W period) (littleCircularReference hγ hγ1) :=
    (hs period hp).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hd1 := hd3.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  obtain ⟨ρ, hρ, hρsub⟩ := exists_banachDoubleFlow_initial_ball
    (ball_mem_nhds (littleCircularReference hγ hγ1) hR) hd1.continuousAt hfix
  let Z := banachDoubleFlow X period
  have hZ : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) (period + period) Z :=
    (isBanachFlowOn_banachDoubleFlow hp0.le hX).mono_initial hρsub
  have hXq : IsBanachFlowOn (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X :=
    ⟨hX.initial, hX.continuous, hX.hasDerivAt, hnear⟩
  have hZq : IsBanachFlowOn (circularBanachField hγ hγ1) (circularQuarterPhaseDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) (period + period) Z :=
    (isBanachFlowOn_banachDoubleFlow hp0.le hXq).mono_initial hρsub
  obtain ⟨A, hAc, hA0, hAd, hAf, δ, hδ, κ, hκ, hquad⟩ :=
    exists_circularReference_quadratic_Fourier_variation hγ hγ1 hD hρ hZ
  obtain ⟨K, hK, r, hr, hchart⟩ := exists_circularConstrainedChart_quadratic_bound hγ hγ1
  let F := circularConstrainedReturnMap hγ hγ1 (fun W => X W period)
  let Φ := circularConstrainedChart hγ hγ1
  have hF0 : F 0 = 0 := circularConstrainedReturnMap_zero hγ hγ1 _ hfix
  have hF : ContinuousAt F 0 := (contDiffAt_circularConstrainedReturnMap hγ hγ1 1 hd1).continuousAt
  have hΦ : ContinuousAt Φ 0 := (hasFDerivAt_circularConstrainedChart_zero hγ hγ1).continuousAt
  have hΦ0 : Φ 0 = littleCircularReference hγ hγ1 := circularConstrainedChart_zero hγ hγ1
  have hV : ball (littleCircularReference hγ hγ1) R ∈ 𝓝 (Φ 0) := by
    rw [hΦ0]
    exact ball_mem_nhds _ hR
  have hconj := eventually_circularConstrainedReturnMap_conjugacy hγ hγ1 hR hd1.continuousAt hfix
    (fun W hW i => harea W hW period hp i) (fun W hW hf i => hfour W hW hf period hp i)
  have hdouble := eventually_doubleReturn_chart_flow hF0 hF hΦ hV hconj
  have hΦρ : ∀ᶠ u in 𝓝 (0 : CircularConstrainedTangentSpace γ),
      Φ u ∈ ball (littleCircularReference hγ hγ1) ρ := hΦ (by rw [hΦ0]; exact ball_mem_nhds _ hρ)
  have hΦδ : ∀ᶠ u in 𝓝 (0 : CircularConstrainedTangentSpace γ),
      ‖Φ u - littleCircularReference hγ hγ1‖ < δ :=
    ((hΦ.sub continuousAt_const).norm).eventually (eventually_lt_nhds (by
      change ‖Φ 0 - littleCircularReference hγ hγ1‖ < δ
      rw [hΦ0, sub_self, norm_zero]
      exact hδ))
  have hgood : ∀ᶠ u in 𝓝 (0 : CircularConstrainedTangentSpace γ),
      Φ (banachDoubleReturn F u) = X (X (Φ u) period) period ∧
        Φ u ∈ ball (littleCircularReference hγ hγ1) ρ ∧
        ‖Φ u - littleCircularReference hγ hγ1‖ ≤ δ ∧ u ∈ closedBall 0 r := by
    filter_upwards [hdouble, hΦρ, hΦδ, closedBall_mem_nhds (0 : CircularConstrainedTangentSpace γ) hr]
      with u hu hρu hδu hru
    exact ⟨hu.2, hρu, hδu.le, hru⟩
  obtain ⟨s, hspos, hsball⟩ := Metric.eventually_nhds_iff.mp
    (hgood.and (eventually_circularConstrainedChart_positive hγ hγ1))
  obtain ⟨t, ht, x, v, B, hB, hback, hball, hnorm, hproj, hvP, hv0, herror, hmoment, hxlim⟩ :=
    exists_circularConstrained_nonzero_asymptotic_orbit hγ hγ1 hR hX (hd3.of_le (by norm_num)) hfix
      (fun W hW i => harea W hW period hp i) (half_pos hspos)
  have hrecord (n : ℕ) := hsball (closedBall_subset_ball (half_lt_self hspos) (hball n))
  have hg (n : ℕ) := (hrecord n).1
  let z : ℕ → Fin 2 → LittleContourSpace γ := fun n => Φ (x n)
  have hz (n : ℕ) : z n ∈ ball (littleCircularReference hγ hγ1) ρ := (hg n).2.1
  have hreturn (n : ℕ) : Z (z (n + 1)) (period + period) = z n := by
    dsimp only [Z]
    rw [banachDoubleFlow_endpoint hp0]
    calc
      _ = Φ (banachDoubleReturn F (x (n + 1))) := (hg (n + 1)).1.symm
      _ = _ := congrArg Φ (hback n)
  let L : CircularConstrainedTangentSpace γ →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
    (circularConstrainedTangentSubmodule γ).subtypeL
  let C := 2 * ‖t • circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖
  have hxnorm (n : ℕ) : ‖x n‖ ≤ C * circularAncientBackwardRatio ^ n := by
    convert hnorm n using 1 <;> dsimp only [C] <;> ring
  have hchart2 := quadratic_chart_backward_asymptotic Φ (littleCircularReference hγ hγ1) L x v hK.le
    (by positivity : 0 ≤ 1 + K * r) (fun n => (hchart (x n) (hg n).2.2.2).1)
    (fun n => (hchart (x n) (hg n).2.2.2).2) hxnorm herror
  let Braw := K * C ^ 2 + ‖L‖ * B
  have hBraw : 0 ≤ Braw := by dsimp only [Braw]; positivity
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hAc.continuousOn).isBounded.exists_norm_le
  let E := max (κ * ((1 + K * r) * C) ^ 2 + M * Braw) 0 + 1
  have hE : 0 < E := by dsimp only [E]; linarith [le_max_right (κ * ((1 + K * r) * C) ^ 2 + M * Braw) 0]
  let Y := banachAncientCurve hD Z z
  have hYm : ∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1 :=
    fun s hs => banachAncientCurve_mem hD hZq hz hreturn hs
  have hYd : ∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s :=
    fun s hs => banachAncientCurve_hasDerivAt hD hZq hz hreturn hs
  have hsample (n : ℕ) : Y (-(n : ℝ) * (period + period)) = z n :=
    banachAncientCurve_sample hD hZq hz hreturn n
  have hflatY : HasCircularFlattenedAncientSamples hγ hγ1 Y :=
    hasCircularFlattenedAncientSamples_of_samples hγ hγ1 hR hX (hd3.of_le (by norm_num)) hfix
      (fun W hW i => harea W hW period hp i) x hback
      (by simpa only [circularAncientBackwardWeight_inv] using hxnorm) Y hsample
  have hYlim : Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
      (𝓝 (littleCircularReference hγ hγ1)) := by
    have he := hΦ.tendsto.comp hxlim
    rw [hΦ0] at he
    exact he.congr' (Filter.Eventually.of_forall (fun n => (hsample n).symm))
  have hfourSample (n : ℕ) (i : Fin 2) :
      Y (-(n : ℝ) * (period + period)) i ∈ fourfoldLittleContourSubmodule γ := by
    rw [hsample n]
    exact circularConstrainedChart_fourfold hγ hγ1 (x n) i
  have harea0 (i : Fin 2) : littleContourArea γ (Y 0 i) = Real.pi * circularContourRadii i ^ 2 := by
    have he : Y 0 = z 0 := banachAncientCurve_zero hD hZq hz hreturn
    rw [he]
    exact circularConstrainedChart_area hγ hγ1 (x 0) (hrecord 0).2 i
  refine ⟨Y, A, v, E, hE, continuousOn_banachAncientCurve hD hZq hz hreturn,
    hYm, hYd, hYlim,
    fun s hs i => (circularAncientMaterial_area hγ hγ1 hYm hYd hs i).trans (harea0 i),
    fun s hs i => circularAncientMaterial_fourfold_of_samples hγ hγ1 hYm hYd hfourSample hs i,
    hAc, hA0, hAd, hvP, hv0, ?_, hflatY⟩
  intro n q hq
  have he := banachAncientCurve_cell_asymptotic hD hZ hz hreturn
    (littleCircularMaterialContours hγ hγ1) A v.val hκ.le hBraw
    (by simpa only [littleCircularMaterialContours_zero] using hquad)
    (by simpa only [littleCircularMaterialContours_zero] using fun n => (hg n).2.2.1)
    (by simpa only [littleCircularMaterialContours_zero] using hchart2.1)
    (by simpa only [littleCircularMaterialContours_zero, z, Braw, L,
      Submodule.subtypeL_apply] using hchart2.2)
    (fun q hq => hM _ (mem_image_of_mem _ hq)) n hq
  calc
    _ ≤ (κ * ((1 + K * r) * C) ^ 2 + M * Braw) * (circularAncientBackwardRatio ^ 2) ^ (n + 1) := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by dsimp only [E]; linarith [le_max_left (κ * ((1 + K * r) * C) ^ 2 + M * Braw) 0])
      (pow_nonneg (sq_nonneg circularAncientBackwardRatio) _)

end Euler2D

end

