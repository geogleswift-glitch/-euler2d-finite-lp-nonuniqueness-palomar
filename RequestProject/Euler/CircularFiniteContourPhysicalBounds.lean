module

public import RequestProject.Euler.CircularFiniteContourDensity
public import RequestProject.Euler.FiniteContourTorusDensityIdentification

/-! Physical containment and the literal initial density of the actual
finite circular contours. Near-reference containment is kept separate
from the weaker chord-arc admissibility condition. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) circularPhysicalLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularPhysicalLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularPhysicalC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem finiteCircularInterfaceRadius_le {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (p : FiniteCircularIndex N) : finiteCircularInterfaceRadius R ρ p ≤ R := by
  have hr : 0 ≤ radScale R ρ p.1 := (mul_pos hR (pow_pos hρ p.1)).le
  exact (mul_le_of_le_one_right hr (circularContourRadii_bounds p.2).2.2).trans
    (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1))

theorem complexTorusPoint_sub_center_norm (z : ℂ) :
    ‖complexTorusPoint z - torusCenter‖ = ‖z‖ := by
  change ‖complexPhysicalPlane z + torusCenter - torusCenter‖ = ‖z‖
  rw [add_sub_cancel_right, complexPhysicalPlane.norm_map]

theorem finiteCircular_contour_boundary_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (Z : FiniteCircularIndex N → ContourC1Space γ)
    (hsmall : ∀ p, ‖Z p - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
      finiteCircularInterfaceRadius R ρ p / 4) (p : FiniteCircularIndex N) (θ : ℝ) :
    ‖complexTorusPoint (ContourC1Space.lift γ (Z p) θ) - torusCenter‖ ≤ (5 / 4) * R := by
  rw [complexTorusPoint_sub_center_norm]
  have hd := (contourC1_norm_sub_ref_le (Z p)
    (finiteCircularReferenceC1 hγ hγ1 R ρ p)
    (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p) θ).trans (hsmall p)
  have hn := norm_sub_norm_le (ContourC1Space.lift γ (Z p) θ)
    (refCircle (finiteCircularInterfaceRadius R ρ p) θ)
  rw [norm_refCircle_actual, abs_of_pos (finiteCircularInterfaceRadius_pos hR hρ p)] at hn
  nlinarith [finiteCircularInterfaceRadius_le hR hρ hρ1 p]

theorem finiteCircular_contour_domain_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N : ℕ} (Z : FiniteCircularIndex N → ContourC1Space γ)
    (hsmall : ∀ p, ‖Z p - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
      finiteCircularInterfaceRadius R ρ p / 4)
    (p : FiniteCircularIndex N) {z : ℂ}
    (hz : z ∈ contourC1EnclosedDomain (Z p) (finiteCircularReferenceC1 hγ hγ1 R ρ p)
      (finiteCircularInterfaceRadius_pos hR hρ p) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p)
      (hsmall p)) :
    ‖complexTorusPoint z - torusCenter‖ ≤ (5 / 4) * R := by
  rw [complexTorusPoint_sub_center_norm]
  have hn := mem_ball_zero_iff.mp (contourC1EnclosedDomain_subset_ball _ _ _ _ _ hz)
  have hs := hsmall p
  have hr := finiteCircularInterfaceRadius_le hR hρ hρ1 p
  linarith

theorem exists_short_quarter_contour_interval {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (Z : ℝ → ι → LittleContourSpace γ) (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    {D : ℝ} (hD : 0 < D) (hZ : ContinuousOn Z (Icc (0 : ℝ) D))
    (hinit : ∀ i, ‖(Z 0 i).val - Z₀ i‖ < r i / 4) :
    ∃ δ > 0, δ ≤ D ∧ ∀ t ∈ Icc (0 : ℝ) δ, ∀ i, ‖(Z t i).val - Z₀ i‖ < r i / 4 := by
  let U := {W : ι → LittleContourSpace γ | ∀ i, ‖(W i).val - Z₀ i‖ < r i / 4}
  have ho : IsOpen U := by
    have hi (i : ι) : IsOpen {W : ι → LittleContourSpace γ | ‖(W i).val - Z₀ i‖ < r i / 4} :=
      isOpen_lt ((((LittleContourSpace.inclusion γ).continuous.comp (continuous_apply i)).sub
        continuous_const).norm) continuous_const
    simpa only [U, setOf_forall] using isOpen_iInter_of_finite hi
  have hn : Z ⁻¹' U ∈ 𝓝[Icc (0 : ℝ) D] 0 :=
    hZ 0 ⟨le_rfl, hD.le⟩ (ho.mem_nhds hinit)
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhdsWithin_iff.mp hn
  refine ⟨min D (ε / 2), lt_min hD (half_pos hε), min_le_left _ _, ?_⟩
  intro t ht
  apply he
  refine ⟨?_, ⟨ht.1, ht.2.trans (min_le_left _ _)⟩⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  exact (ht.2.trans (min_le_right _ _)).trans_lt (half_lt_self hε)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteCircularInitial_C1_density_eq {s A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ)
    (hsmall : ∀ p : FiniteCircularIndex N,
      ‖(finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val -
        finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ finiteCircularInterfaceRadius R ρ p / 4)
    (x : R2) :
    finiteContourC1PatchVorticity (finiteCircularInterfaceStrength A₀ b)
      (fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val)
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hsmall
      (centeredComplexHomeomorph.symm x) =
      P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter) := by
  have he : finiteContourC1PatchVorticity (finiteCircularInterfaceStrength A₀ b)
      (fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val)
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hsmall =
      phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b)
        (fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val) := by
    funext z
    unfold finiteContourC1PatchVorticity phaseFiniteContourPatchVorticity
    apply Finset.sum_congr rfl
    intro p _
    unfold contourC1PatchVorticity phaseContourPatchVorticity
    rw [contourC1EnclosedDomain_eq_radialFill]
  rw [he, P.finiteCircularInitial_density_eq hR hρ N,
    centeredComplexHomeomorph_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end CircularMaterialTransferProfile
end Euler2D

end
