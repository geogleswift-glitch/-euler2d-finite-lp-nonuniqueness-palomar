module

public import RequestProject.Euler.NonautonomousBanachOpenUniqueness
public import RequestProject.Euler.FiniteContourPhaseField

/-! Uniqueness of actual forced finite phase trajectories on their
common time interval. In particular provisional continuations of the
same initial material path agree on every overlap. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) forcedPhaseUniqueLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) forcedPhaseUniqueLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) forcedPhaseUniqueC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) forcedPhaseUniqueC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem eqOn_of_finitePhase_forcedODE {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ)
    {a A B : ℝ} {K : ℝ≥0}
    (hELip : ∀ t, LipschitzOnWith K (E t) (ball 0 (a / 4)))
    {α β : ℝ → ι → LittleContourSpace γ}
    (hαc : ContinuousOn α (Icc A B)) (hβc : ContinuousOn β (Icc A B))
    (hαmem : ∀ t ∈ Icc A B, IsPhaseAdmissibleLittleContourFamily Z₀ r (α t) ∧ ‖α t‖ < a / 4)
    (hβmem : ∀ t ∈ Icc A B, IsPhaseAdmissibleLittleContourFamily Z₀ r (β t) ∧ ‖β t‖ < a / 4)
    (hαd : ∀ t ∈ Ico A B, HasDerivAt α
      (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (α t) + E t (α t)) t)
    (hβd : ∀ t ∈ Ico A B, HasDerivAt β
      (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (β t) + E t (β t)) t)
    (h0 : α A = β A) : EqOn α β (Icc A B) := by
  let U : Set (ι → LittleContourSpace γ) :=
    {W | IsPhaseAdmissibleLittleContourFamily Z₀ r W} ∩ ball 0 (a / 4)
  have hU : IsOpen U := (isOpen_phaseAdmissibleLittleContourFamilies Z₀ r).inter isOpen_ball
  have hf : ContDiffOn ℝ 1 (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g) U :=
    (contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g 1).mono inter_subset_left
  exact eqOn_of_forced_banachODE_open hU hf (fun t => (hELip t).mono inter_subset_right)
    hαc hβc (fun t ht => ⟨(hαmem t ht).1, mem_ball_zero_iff.mpr (hαmem t ht).2⟩)
    (fun t ht => ⟨(hβmem t ht).1, mem_ball_zero_iff.mpr (hβmem t ht).2⟩) hαd hβd h0

end Euler2D

end
