module

public import RequestProject.Euler.BanachFiniteEndpointLimit
public import RequestProject.Euler.FinitePhaseTubeClosure
public import RequestProject.Euler.CircularFiniteContourInitialData

/-! A finite circular material path with a genuine velocity bound and
a strict geometric buffer has an actual endpoint in the original phase
domain. The little Banach topology and all finite interfaces are retained. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) circularEndpointLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularEndpointLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularEndpointC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

def finiteCircularReferenceLittle {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (R ρ : ℝ) {N : ℕ} (p : FiniteCircularIndex N) : LittleContourSpace γ :=
  radScale R ρ p.1 • littleCircularReference hγ hγ1 p.2

@[simp] theorem finiteCircularReferenceLittle_val {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (R ρ : ℝ) {N : ℕ} (p : FiniteCircularIndex N) :
    (finiteCircularReferenceLittle hγ hγ1 R ρ p).val = finiteCircularReferenceC1 hγ hγ1 R ρ p := rfl

theorem norm_finiteCircular_closedPhaseTube_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hη : 0 ≤ η)
    {N : ℕ} {Z : FiniteCircularIndex N → LittleContourSpace γ}
    (hZ : Z ∈ closedPhaseTube (finiteCircularReferenceLittle hγ hγ1 R ρ)
      (fun p => η * radScale R ρ p.1)) :
    ‖Z‖ ≤ R * (‖littleCircularReference hγ hγ1‖ + η) := by
  obtain ⟨b, hb⟩ := hZ
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR.le (by positivity))).mpr
  intro p
  have hr : 0 ≤ radScale R ρ p.1 := (mul_pos hR (pow_pos hρ p.1)).le
  have hrR : radScale R ρ p.1 ≤ R :=
    mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hRef : ‖finiteCircularReferenceLittle hγ hγ1 R ρ p‖ =
      radScale R ρ p.1 * ‖littleCircularReference hγ hγ1 p.2‖ := by
    rw [finiteCircularReferenceLittle, norm_smul, Real.norm_of_nonneg hr]
  calc
    ‖Z p‖ = ‖contourParameterShiftLittleCLM γ (b p) (Z p)‖ :=
      (norm_contourParameterShiftLittleCLM (b p) (Z p)).symm
    _ ≤ ‖contourParameterShiftLittleCLM γ (b p) (Z p) - finiteCircularReferenceLittle hγ hγ1 R ρ p‖ +
        ‖finiteCircularReferenceLittle hγ hγ1 R ρ p‖ := norm_le_norm_sub_add _ _
    _ ≤ η * radScale R ρ p.1 + radScale R ρ p.1 * ‖littleCircularReference hγ hγ1 p.2‖ :=
      add_le_add (hb p) hRef.le
    _ = radScale R ρ p.1 * (‖littleCircularReference hγ hγ1 p.2‖ + η) := by ring
    _ ≤ radScale R ρ p.1 * (‖littleCircularReference hγ hγ1‖ + η) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (norm_le_pi_norm (littleCircularReference hγ hγ1) p.2) (le_refl η)) hr
    _ ≤ R * (‖littleCircularReference hγ hγ1‖ + η) :=
      mul_le_mul_of_nonneg_right hrR (by positivity)

theorem exists_finiteCircular_phase_endpoint {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ η D M : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρa : ρ ≤ cellA / 4)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    (hD : 0 < D) (hM : 0 ≤ M) {N : ℕ}
    (Z Z' : ℝ → FiniteCircularIndex N → LittleContourSpace γ)
    (hd : ∀ t ∈ Ioo (0 : ℝ) D, HasDerivAt Z (Z' t) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) D, ‖Z' t‖ ≤ M)
    (htube : ∀ t ∈ Ioo (0 : ℝ) D, ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
      ‖contourParameterShiftC1 (b p) (Z t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        η * radScale R ρ p.1) :
    ∃ W : FiniteCircularIndex N → LittleContourSpace γ,
      Tendsto Z (𝓝[<] D) (𝓝 W) ∧
      IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) W ∧
      IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) W ∧
      ‖W‖ ≤ R * (‖littleCircularReference hγ hγ1‖ + η) ∧
      ∀ t ∈ Ioo (0 : ℝ) D, ‖Z t - W‖ ≤ M * (D - t) := by
  have hρ1 : ρ ≤ 1 := by linarith [cellA_lt_one]
  obtain ⟨W, hW, hdist⟩ := exists_left_limit_of_bounded_derivative hD hM hd hb
  have hWt : W ∈ closedPhaseTube (finiteCircularReferenceLittle hγ hγ1 R ρ)
      (fun p : FiniteCircularIndex N => η * radScale R ρ p.1) := by
    apply closedPhaseTube_mem_of_tendsto (show γ ≤ 1 from hγ1.le) _ _ hW
    filter_upwards [Ioo_mem_nhdsLT hD] with t ht
    exact htube t ht
  obtain ⟨b, hb⟩ := hWt
  have hshift : IsAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) (contourParameterShiftFamilyCLM γ b W) :=
    admissible_scaledCircular_family_of_close hγ hγ1 hR hρ hρ1 hρa hη hηa hηgap _ hb
  have hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) W := by
    refine ⟨-b, ?_⟩
    simpa only [neg_neg] using hshift
  have hquarter : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) W := by
    refine ⟨b, ?_⟩
    intro p
    have hrad := (circularContourRadii_bounds p.2).2.1
    have hsmall : η < circularContourRadii p.2 / 4 := by linarith [cellA_pos]
    have hm := mul_lt_mul_of_pos_right hsmall (mul_pos hR (pow_pos hρ p.1))
    exact (hb p).trans_lt (by dsimp only [finiteCircularInterfaceRadius, radScale]; nlinarith only [hm])
  refine ⟨W, hW, hphase, hquarter, ?_, hdist⟩
  exact norm_finiteCircular_closedPhaseTube_le hγ hγ1 hR hρ hρ1 hη ⟨b, hb⟩

end Euler2D

end
