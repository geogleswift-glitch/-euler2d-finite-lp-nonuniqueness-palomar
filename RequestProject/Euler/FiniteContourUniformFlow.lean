module

public import RequestProject.Euler.FiniteContourSmoothField
public import RequestProject.Euler.LocalBanachFlowExistence

/-! The genuine finite material equation admits one actual flow family
on a common neighborhood and a common positive time interval. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) finiteUniformLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) finiteUniformLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

local instance (priority := 2000) finiteUniformC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

set_option maxHeartbeats 600000 in
theorem exists_finiteContour_local_flow {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : AdmissibleLittleContourFamily Z₀ r) :
    ∃ a > 0,
      ball Z.val a ⊆ {W | IsAdmissibleLittleContourFamily Z₀ r W} ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
        (ball Z.val a) ∧
      ∃ T > 0, ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
        IsBanachFlowOn (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g)
          (ball Z.val a) (ball Z.val (a / 4)) T X ∧
        ∀ W ∈ ball Z.val (a / 4), ∀ t ∈ Icc 0 T, ∀ i θ,
          HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
            (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ) t := by
  let F := finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g
  let A := {W : ι → LittleContourSpace γ | IsAdmissibleLittleContourFamily Z₀ r W}
  have hA : A ∈ 𝓝 Z.val := (isOpen_admissibleLittleContourFamilies Z₀ r).mem_nhds Z.property
  obtain ⟨K, V, hV, hLip⟩ :=
    (contDiffAt_finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g Z 1).exists_lipschitzOnWith
  obtain ⟨a, ha, hball, T, hT, X, hX⟩ :=
    exists_local_banachFlow_of_lipschitzOn_nhds F Z.val (inter_mem hV hA)
      (hLip.mono inter_subset_left)
  have hba : ball Z.val a ⊆ A := hball.trans inter_subset_right
  refine ⟨a, ha, hba, K, hLip.mono (hball.trans inter_subset_left), T, hT, X, hX, ?_⟩
  intro W hW t ht i θ
  have hmem : IsAdmissibleLittleContourFamily Z₀ r (X W t) := hba (hX.mem W hW t ht)
  have hd := hX.hasDerivAt W hW t ht
  have he := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
    (LittleContourSpace.lift γ (finiteContourMaterialFieldTotal hγ hγ1 Z₀ r hr href g (X W t) i) θ) t at he
  rw [finiteContourMaterialFieldTotal_of_mem hγ hγ1 Z₀ r hr href g ⟨X W t, hmem⟩,
    lift_finiteContourMaterialField] at he
  exact he

end Euler2D

end
