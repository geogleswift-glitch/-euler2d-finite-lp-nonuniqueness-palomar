module

public import RequestProject.Euler.FiniteContourLocalFlow

/-! A genuinely quarter-radius initial family admits a real local
material solution staying in that actual geometric neighborhood. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) quarterFlowLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) quarterFlowLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) quarterFlowC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

set_option maxHeartbeats 600000 in
theorem exists_finiteContour_quarter_local_material_solution {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (hq : ∀ i, ‖(Z.val i).val - Z₀ i‖ < r i / 4) :
    ∃ T > 0, ∃ α : ℝ → ι → LittleContourSpace γ, α 0 = Z.val ∧
      ∀ t ∈ Ioo (-T) T, (∀ i, ‖(α t i).val - Z₀ i‖ < r i / 4) ∧
        ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (α t),
          HasDerivAt α (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨α t, ht⟩) t := by
  obtain ⟨T, hT, α, hα0, hd⟩ := exists_finiteContour_local_material_solution hγ hγ1 Z₀ r hr href g Z
  obtain ⟨h0, hd0⟩ := hd 0 (by constructor <;> linarith)
  have ho : IsOpen {W : ι → LittleContourSpace γ | ∀ i, ‖(W i).val - Z₀ i‖ < r i / 4} := by
    have hi (i : ι) : IsOpen {W : ι → LittleContourSpace γ | ‖(W i).val - Z₀ i‖ < r i / 4} :=
      isOpen_lt ((((LittleContourSpace.inclusion γ).continuous.comp (continuous_apply i)).sub
        continuous_const).norm) continuous_const
    simpa only [setOf_forall] using isOpen_iInter_of_finite hi
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, ‖(α t i).val - Z₀ i‖ < r i / 4 :=
    hd0.continuousAt (ho.mem_nhds (by rw [hα0]; exact hq))
  obtain ⟨σ, hσ, hσq⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min T σ, lt_min hT hσ, α, hα0, ?_⟩
  intro t ht
  have htT : t ∈ Ioo (-T) T :=
    ⟨(neg_le_neg (min_le_left T σ)).trans_lt ht.1, ht.2.trans_le (min_le_left T σ)⟩
  have htσ : t ∈ ball (0 : ℝ) σ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_le_neg (min_le_right T σ)).trans_lt ht.1, ht.2.trans_le (min_le_right T σ)⟩
  exact ⟨hσq htσ, hd t htT⟩

end Euler2D

end
