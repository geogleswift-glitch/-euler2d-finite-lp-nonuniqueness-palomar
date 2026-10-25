module

public import RequestProject.Euler.CircularFiniteTubeGeometry
public import RequestProject.Euler.CircularFinitePhaseEndpoint
public import RequestProject.Euler.FiniteContourMaterialFieldBounds

/-! The original phase field is genuinely bounded on the whole closed
finite circular tube. The bound is obtained from actual chord and
separation estimates, without assuming a Banach velocity bound. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal BigOperators

namespace Euler2D

local instance (priority := 2000) circularPhaseBoundLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularPhaseBoundLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularPhaseBoundC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem exists_finiteCircular_phaseField_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    {N : ℕ} (g : FiniteCircularIndex N → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Z : FiniteCircularIndex N → LittleContourSpace γ,
      (∃ b : FiniteCircularIndex N → ℝ, ∀ p,
        ‖contourParameterShiftC1 (b p) (Z p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) →
      ‖finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) g Z‖ ≤ B := by
  let Ref : FiniteCircularIndex N → LittleContourSpace γ := finiteCircularReferenceLittle hγ hγ1 R ρ
  let Z₀ : FiniteCircularIndex N → ContourC1Space γ := finiteCircularReferenceC1 hγ hγ1 R ρ
  let r : FiniteCircularIndex N → ℝ := finiteCircularInterfaceRadius R ρ
  let hr := finiteCircularInterfaceRadius_pos (N := N) hR hρ
  let href := lift_finiteCircularReferenceC1 hγ hγ1 R ρ (N := N)
  let F := finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g
  let c := finiteCircularTubeChordConstant R ρ N
  let σ := finiteCircularTubeSeparationConstant R ρ N
  let M := R * (‖littleCircularReference hγ hγ1‖ + η) + ‖Ref‖
  let C := max (contourSelfLogShapeConstant (γ : ℝ) c M)
    (2 * contourCrossLogShapeConstant (γ : ℝ) σ M)
  let L := |-1 / (2 * Real.pi)| * (∑ j, |g j|) * C
  have hρ1 : ρ ≤ 1 := by linarith [cellA_lt_one]
  have hc : 0 < c := finiteCircularTubeChordConstant_pos hR hρ N
  have hσ : 0 < σ := finiteCircularTubeSeparationConstant_pos hR hρ N
  have hMr : 0 ≤ R * (‖littleCircularReference hγ hγ1‖ + η) := by positivity
  have hM : 0 ≤ M := add_nonneg hMr (norm_nonneg _)
  have hC : 0 ≤ C := (contourSelfLogShapeConstant_nonneg hγ hγ1 hc hM).trans (le_max_left _ _)
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) hC
  have hRefclose (p : FiniteCircularIndex N) : ‖(Ref p).val - Z₀ p‖ ≤ η * radScale R ρ p.1 := by
    change ‖finiteCircularReferenceC1 hγ hγ1 R ρ p - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ _
    simpa only [sub_self, norm_zero] using mul_nonneg hη (mul_pos hR (pow_pos hρ p.1)).le
  have hRefA : IsAdmissibleLittleContourFamily Z₀ r Ref :=
    admissible_scaledCircular_family_of_close hγ hγ1 hR hρ hρ1 hρa hη hηa hηgap Ref hRefclose
  have hRefgeo := finiteCircular_close_uniform_geometry hγ hγ1 hR hρ hρa hη hηa hηgap Ref hRefclose
  have hRefM (p : FiniteCircularIndex N) : ‖Ref p‖ ≤ M :=
    (norm_le_pi_norm Ref p).trans (le_add_of_nonneg_left hMr)
  refine ⟨L * M + ‖F Ref‖, by positivity, ?_⟩
  intro Z hZ
  obtain ⟨b, hb⟩ := hZ
  let W := contourParameterShiftFamilyCLM γ b Z
  have hWclose (p : FiniteCircularIndex N) : ‖(W p).val - Z₀ p‖ ≤ η * radScale R ρ p.1 := hb p
  have hWA : IsAdmissibleLittleContourFamily Z₀ r W :=
    admissible_scaledCircular_family_of_close hγ hγ1 hR hρ hρ1 hρa hη hηa hηgap W hWclose
  have hWgeo := finiteCircular_close_uniform_geometry hγ hγ1 hR hρ hρa hη hηa hηgap W hWclose
  have hZnorm : ‖Z‖ ≤ R * (‖littleCircularReference hγ hγ1‖ + η) :=
    norm_finiteCircular_closedPhaseTube_le hγ hγ1 hR hρ hρ1 hη ⟨b, hb⟩
  have hWnorm : ‖W‖ ≤ R * (‖littleCircularReference hγ hγ1‖ + η) := by
    dsimp only [W]
    rw [norm_contourParameterShiftFamilyCLM]
    exact hZnorm
  have hWM (p : FiniteCircularIndex N) : ‖W p‖ ≤ M :=
    (norm_le_pi_norm W p).trans (hWnorm.trans (le_add_of_nonneg_right (norm_nonneg Ref)))
  have hdist : ‖W - Ref‖ ≤ M := (norm_sub_le W Ref).trans (add_le_add hWnorm (le_refl _))
  have hdiff : ‖F W - F Ref‖ ≤ L * ‖W - Ref‖ :=
    norm_finiteContourMaterialField_sub_le hγ hγ1 Z₀ r hr href g ⟨W, hWA⟩ ⟨Ref, hRefA⟩
      hc hσ hM hWgeo.1 hRefgeo.1 hWgeo.2 hRefgeo.2 hWM hRefM
  have hphase : finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z =
      contourParameterShiftFamilyCLM γ (-b) (F W) := by
    rw [finiteContourPhaseFieldTotal_eq_chart hγ hγ1 Z₀ r hr href g (-b) Z (by
      simpa only [neg_neg] using hWA)]
    simp only [finiteContourPhaseFieldChart, neg_neg, F, W]
  rw [hphase, norm_contourParameterShiftFamilyCLM]
  exact (norm_le_norm_sub_add (F W) (F Ref)).trans
    (add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hdist hL)) (le_refl _))

end Euler2D

end
