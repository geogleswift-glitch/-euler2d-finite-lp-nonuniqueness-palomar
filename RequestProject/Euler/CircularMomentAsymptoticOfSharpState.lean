module

public import RequestProject.Euler.CircularAncientMomentAsymptotic

/-! The genuine observable calculation is applied to a specified sharp
material state, retaining that state for joint constructions. -/

@[expose] public section

set_option maxHeartbeats 18000000
set_option maxRecDepth 4000

noncomputable section

open Set Filter Topology Metric Asymptotics
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) sharpStateMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) sharpStateMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) sharpStateMomentFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) sharpStateMomentTangent_group (γ : ℝ≥0) :
    NormedAddCommGroup (CircularConstrainedTangentSpace γ) :=
  Submodule.normedAddCommGroup (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sharpStateMomentTangent_space (γ : ℝ≥0) :
    NormedSpace ℝ (CircularConstrainedTangentSpace γ) :=
  Submodule.normedSpace (circularConstrainedTangentSubmodule γ)
local instance (priority := 2000) sharpStateMomentTangent_continuousAdd (γ : ℝ≥0) :
    ContinuousAdd (CircularConstrainedTangentSpace γ) where
  continuous_add := by
    have h1 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.1.val) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous (fun p : CircularConstrainedTangentSpace γ × CircularConstrainedTangentSpace γ =>
        p.2.val) := continuous_subtype_val.comp continuous_snd
    exact (h1.add h2).subtype_mk _

attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedUnstableEmbeddingCLM circularConstrainedUnstableCoordinateCLM


theorem circularAncient_fourthMoment_asymptotic_of_sharp_state {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Y : ℝ → Fin 2 → LittleContourSpace γ)
    (A : ℝ → (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ))
    (v : CircularConstrainedTangentSpace γ) {E : ℝ} (hE : 0 < E)
    (hAc : Continuous A)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ (Fin 2 → LittleContourSpace γ))
    (hAd : ∀ s ∈ Icc (0 : ℝ) (period + period), HasDerivAt A
      ((fderiv ℝ (circularBanachField hγ hγ1) (littleCircularMaterialContours hγ hγ1 s)).comp (A s)) s)
    (hvP : circularConstrainedUnstableProjectionCLM hγ hγ1.le v = v) (hv0 : v ≠ 0)
    (hstate : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) (period + period),
      ‖Y (-((n + 1 : ℕ) : ℝ) * (period + period) + s) - littleCircularMaterialContours hγ hγ1 s -
          ((lamMult ^ 2)⁻¹) ^ (n + 1) • A s v.val‖ ≤
        E * (circularAncientBackwardRatio ^ 2) ^ (n + 1)) :
    ∃ κ : ℂ, ∃ δ > 0, κ ≠ 0 ∧
      (fun s : ℝ => circularBoundaryFourthMoment (Y s) - κ * Complex.exp ((s : ℂ) * lamStar)) =O[atBot]
        (fun s : ℝ => Real.exp ((sigma + δ) * s)) := by
  let ζ := circularConstrainedUnstableCoordinateCLM γ v
  have hvS : v = circularConstrainedUnstableEmbeddingCLM hγ hγ1.le ζ := by
    calc
      _ = circularConstrainedUnstableProjectionCLM hγ hγ1.le v := hvP.symm
      _ = _ := by unfold circularConstrainedUnstableProjectionCLM; rfl
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  have hvraw : v.val = circularUnstableEmbeddingCLM hγ hγ1.le ζ := by
    rw [hvS]
    exact circularConstrainedUnstableEmbeddingCLM_val hγ hγle ζ
  have hζ : ζ ≠ 0 := by
    intro hz
    apply hv0
    rw [hvS, hz]
    exact ContinuousLinearMap.map_zero (circularConstrainedUnstableEmbeddingCLM hγ hγle)
  let κ := circularPatchGrowingResponse * ζ
  have hκ : κ ≠ 0 := mul_ne_zero circularPatchGrowingResponse_ne_zero hζ
  let q := (lamMult ^ 2)⁻¹
  let b := circularAncientBackwardRatio
  have hq : 0 ≤ q := inv_nonneg.mpr (sq_nonneg _)
  have hqb : q ≤ b := by
    dsimp only [q, b, circularAncientBackwardRatio]
    rw [div_eq_mul_inv]
    linarith [inv_nonneg.mpr (sq_nonneg lamMult)]
  have hb0 : 0 < b := circularAncientBackwardRatio_bounds.1
  have hb1 : b < 1 := lt_trans circularAncientBackwardRatio_bounds.2 (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hAc.continuousOn).isBounded.exists_norm_le
  have hAv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (period + period)) : ‖q • A s v.val‖ ≤
      q * (max M 0 * ‖v.val‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
    apply mul_le_mul_of_nonneg_left _ hq
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((hM _ (mem_image_of_mem _ hs)).trans (le_max_left M 0)) (norm_nonneg _))
  have hcell (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (period + period)) :
      ‖Y (-((n + 1 : ℕ) : ℝ) * (period + period) + s) - littleCircularMaterialContours hγ hγ1 s -
        q ^ n • (q • A s v.val)‖ ≤ (E * b ^ 2) * (b ^ 2) ^ n := by
    rw [smul_smul, ← pow_succ q n]
    convert hstate n s hs using 1
    dsimp only [b]
    rw [pow_succ (circularAncientBackwardRatio ^ 2) n]
    ring
  have hφ : ContDiff ℝ 2 (@circularBoundaryFourthMoment γ) :=
    (contDiff_circularBoundaryFourthMoment γ).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨N, K, hK, hobs⟩ := exists_uniform_cell_observable_asymptotic hφ
    (contDiff_littleCircularMaterialContours hγ hγ1).continuous
    (fun n s => Y (-((n + 1 : ℕ) : ℝ) * (period + period) + s)) hq hqb hb0.le hb1
    (mul_nonneg hE.le (sq_nonneg b)) (by positivity : 0 ≤ q * (max M 0 * ‖v.val‖)) hAv hcell
  have hresponse (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (period + period)) :
      fderiv ℝ (@circularBoundaryFourthMoment γ) (littleCircularMaterialContours hγ hγ1 s) (A s v.val) =
        κ * Complex.exp ((s : ℂ) * lamStar) := by
    rw [hvraw, circularReference_variational_operator_unstable hγ hγ1 A hAc.continuousOn hA0 hAd ζ hs]
    exact fderiv_circularBoundaryFourthMoment_complexGrowing hγ hγ1 ζ s
  have hlead (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (period + period)) :
      q ^ n • fderiv ℝ (@circularBoundaryFourthMoment γ) (littleCircularMaterialContours hγ hγ1 s)
        (q • A s v.val) = κ * Complex.exp
          (((-((n + 1 : ℕ) : ℝ) * (period + period) + s : ℝ) : ℂ) * lamStar) := by
    rw [map_smul, hresponse s hs, smul_smul, ← pow_succ q n]
    exact circularGrowing_exponential_cell κ (n + 1) s
  obtain ⟨δ, hδ, hδexp⟩ := exists_circularAncient_faster_error_exponent
  refine ⟨κ, δ, hδ, hκ, ?_⟩
  apply isBigO_atBot_of_uniform_time_cells (by unfold period; positivity : 0 < period + period)
    (by linarith [sigma_pos] : 0 ≤ sigma + δ) hK.le hδexp.symm N
  intro n hn s hs
  have he := hobs n hn s hs
  rw [circularBoundaryFourthMoment_material_reference, sub_zero, hlead n s hs] at he
  exact he

end Euler2D

end

