module

public import RequestProject.Euler.FiniteContourUniformFlow
public import RequestProject.Euler.BanachFlowRegularity

/-! Actual finite material flows have every requested finite order
of dependence on their initial contours, in the unchanged little norm. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) finiteSmoothFlowLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) finiteSmoothFlowLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) finiteSmoothFlowC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

set_option maxHeartbeats 600000 in
theorem exists_finiteContour_local_smooth_flow {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) (n : ℕ) :
    ∃ ρ > 0, ∃ τ > 0, ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
      (∀ W ∈ ball Z.val ρ, X W 0 = W) ∧
      (∀ t ∈ Icc 0 τ, ContDiffOn ℝ n (fun W => X W t) (ball Z.val ρ)) ∧
      ∀ W ∈ ball Z.val ρ, ∀ t ∈ Icc 0 τ,
        ∃ ht : IsAdmissibleLittleContourFamily Z₀ r (X W t),
          HasDerivAt (X W) (finiteContourMaterialField hγ hγ1 Z₀ r hr href g ⟨X W t, ht⟩) t ∧
          ∀ i θ, HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
            (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ) t := by
  obtain ⟨a, ha, hba, K, hLip, T, hT, X, hX, hpoint⟩ :=
    exists_finiteContour_local_flow hγ hγ1 Z₀ r hr href g Z
  have hf : ContDiffOn ℝ ∞ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
      (ball Z.val a) :=
    (contDiffOn_finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g (⊤ : ℕ∞)).mono hba
  obtain ⟨ρ, hρ, hρV, τ, hτ, hτT, hsmooth⟩ :=
    banachFlow_contDiffOn_initial_locally n isOpen_ball hf hLip
      (ball_mem_nhds Z.val (by positivity : 0 < a / 4)) hT hX
  refine ⟨ρ, hρ, τ, hτ, X, fun W hW => hX.initial W (hρV hW), hsmooth, ?_⟩
  intro W hW t ht
  have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hτT⟩
  have hmem : IsAdmissibleLittleContourFamily Z₀ r (X W t) :=
    hba (hX.mem W (hρV hW) t htT)
  have hd := hX.hasDerivAt W (hρV hW) t htT
  rw [finiteContourMaterialFieldTotal_of_mem hγ hγ1 Z₀ r hr href g ⟨X W t, hmem⟩] at hd
  exact ⟨hmem, hd, hpoint W (hρV hW) t htT⟩

end Euler2D

end
