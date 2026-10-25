module

public import RequestProject.Euler.NonautonomousBanachFlowExistence
public import RequestProject.Euler.FiniteContourPhaseField

/-! A genuine local material solution with continuous forcing at every
admissible phase. The original finite contour boundary integral is
retained through overlapping phase charts. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) forcedPhaseFiniteLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) forcedPhaseFiniteLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) forcedPhaseFiniteC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) forcedPhaseFiniteC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem exists_finitePhase_forced_local_flow {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (Z : ι → LittleContourSpace γ) (hZ : IsPhaseAdmissibleLittleContourFamily Z₀ r Z)
    (E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ)
    {U : Set (ι → LittleContourSpace γ)} {K : ℝ≥0} {T₀ : ℝ}
    (hT₀ : 0 < T₀) (hU : U ∈ 𝓝 Z)
    (hELip : ∀ t ∈ Icc (-T₀) T₀, LipschitzOnWith K (E t) U)
    (hEc : ∀ W ∈ U, ContinuousOn (fun t => E t W) (Icc (-T₀) T₀)) :
    ∃ ρ > 0, ∃ T > 0, T ≤ T₀ ∧ ∃ X : (ι → LittleContourSpace γ) → ℝ → ι → LittleContourSpace γ,
      IsNonautonomousBanachFlowOn
        (fun t W => finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g W + E t W)
        ({W | IsPhaseAdmissibleLittleContourFamily Z₀ r W} ∩ U) (ball Z ρ) T X ∧
      ∀ W ∈ ball Z ρ, ∀ t ∈ Icc (0 : ℝ) T, ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ +
            LittleContourSpace.lift γ (E t (X W t) i) θ) t := by
  let f := finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g
  let D : Set (ι → LittleContourSpace γ) := {W | IsPhaseAdmissibleLittleContourFamily Z₀ r W}
  have hD : IsOpen D := isOpen_phaseAdmissibleLittleContourFamilies Z₀ r
  have hf : ContDiffAt ℝ 1 f Z :=
    contDiffAt_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g Z hZ 1
  obtain ⟨K₀, V, hV, hLip⟩ := hf.exists_lipschitzOnWith
  have hnhds : V ∩ (U ∩ D) ∈ 𝓝 Z := inter_mem hV (inter_mem hU (hD.mem_nhds hZ))
  have htotalLip (t : ℝ) (ht : t ∈ Icc (-T₀) T₀) :
      LipschitzOnWith (K₀ + K) (fun W => f W + E t W) (V ∩ (U ∩ D)) :=
    (hLip.mono inter_subset_left).add ((hELip t ht).mono (fun _ h => h.2.1))
  have htotalc (W : ι → LittleContourSpace γ) (hW : W ∈ V ∩ (U ∩ D)) :
      ContinuousOn (fun t => f W + E t W) (Icc (-T₀) T₀) :=
    continuousOn_const.add (hEc W hW.2.1)
  obtain ⟨a, ha, hball, T, hT, hTT₀, X, hX⟩ :=
    exists_local_nonautonomous_banachFlow (fun t W => f W + E t W) Z hT₀ hnhds htotalLip htotalc
  have hXD : IsNonautonomousBanachFlowOn (fun t W => f W + E t W)
      (D ∩ U) (ball Z (a / 4)) T X :=
    ⟨hX.initial, hX.continuous, hX.hasDerivAt,
      fun W hW t ht => ⟨(hball (hX.mem W hW t ht)).2.2, (hball (hX.mem W hW t ht)).2.1⟩⟩
  refine ⟨a / 4, by positivity, T, hT, hTT₀, X, hXD, ?_⟩
  intro W hW t ht i θ
  have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hXD.hasDerivAt W hW t ht)
  change HasDerivAt (fun s => LittleContourSpace.lift γ (X W s i) θ)
    (LittleContourSpace.lift γ (f (X W t) i) θ + LittleContourSpace.lift γ (E t (X W t) i) θ) t at hd
  have hfield : LittleContourSpace.lift γ (f (X W t) i) θ =
      contourBoundaryField g (fun j => LittleContourSpace.lift γ (X W t j)) i θ :=
    lift_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (X W t) (hXD.mem W hW t ht).1 i θ
  rwa [hfield] at hd

end Euler2D

end
