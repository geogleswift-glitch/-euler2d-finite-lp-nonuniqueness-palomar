module

public import RequestProject.Euler.FinitePhaseEndpointContinuation
public import RequestProject.Euler.TorusForcedFinitePhaseFlow
public import RequestProject.Euler.BanachEndpointConcatenation

/-! A genuine finite material trajectory extends across a finite
limit in the open phase domain. The forcing is kept fixed, and the
derivative at the joining time is proved from the same equation. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseLocalEndpointLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) phaseLocalEndpointLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) phaseLocalEndpointC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseLocalEndpointC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem exists_finitePhase_continuation_at_limit_local_forcing {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (E : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ)
    (V : Set (ι → LittleContourSpace γ))
    {a D H : ℝ} {K : ℝ≥0} (hD : 0 < D) (hH : 0 < H)
    (hELip : ∀ t, LipschitzOnWith K (E t) V)
    (hEc : ∀ W ∈ V, Continuous (fun t => E t W))
    (α : ℝ → ι → LittleContourSpace γ) (W : ι → LittleContourSpace γ)
    (hV : V ∈ 𝓝 W)
    (hα : ∀ t ∈ Ico (0 : ℝ) D, HasDerivAt α
      (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (α t) + E t (α t)) t)
    (hαmem : ∀ t ∈ Ico (0 : ℝ) D,
      IsPhaseAdmissibleLittleContourFamily Z₀ r (α t) ∧
      ‖α t‖ < a / 4 ∧ IsQuarterPhaseLittleContourFamily Z₀ r (α t))
    (hlim : Tendsto α (𝓝[<] D) (𝓝 W))
    (hW : IsPhaseAdmissibleLittleContourFamily Z₀ r W)
    (hWa : ‖W‖ < a / 4) (hWq : IsQuarterPhaseLittleContourFamily Z₀ r W) :
    ∃ δ > 0, δ ≤ H ∧ ∃ Y : ℝ → ι → LittleContourSpace γ,
      (∀ t ∈ Ico (0 : ℝ) D, Y t = α t) ∧ Y D = W ∧
      ContinuousOn Y (Icc (0 : ℝ) (D + δ)) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ), HasDerivAt Y
        (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (Y t) + E t (Y t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (D + δ),
        IsPhaseAdmissibleLittleContourFamily Z₀ r (Y t) ∧
        ‖Y t‖ < a / 4 ∧ IsQuarterPhaseLittleContourFamily Z₀ r (Y t)) ∧
      ∀ t ∈ Icc (0 : ℝ) (D + δ), ∀ i θ,
        HasDerivAt (fun s => LittleContourSpace.lift γ (Y s i) θ)
          (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Y t j)) i θ +
            LittleContourSpace.lift γ (E t (Y t) i) θ) t := by
  let U : Set (ι → LittleContourSpace γ) := V ∩ (ball 0 (a / 4) ∩
    {V | IsQuarterPhaseLittleContourFamily Z₀ r V})
  have hU : U ∈ 𝓝 W := inter_mem hV (inter_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hWa))
    ((isOpen_quarterPhaseLittleContourFamilies Z₀ r).mem_nhds hWq))
  have hLipU (t : ℝ) : LipschitzOnWith K (E t) U := (hELip t).mono inter_subset_left
  have hcU (V : ι → LittleContourSpace γ) (hV : V ∈ U) : Continuous (fun t => E t V) :=
    hEc V hV.1
  obtain ⟨ρ, hρ, δ, hδ, hδH, X, hX, _⟩ :=
    exists_finitePhase_time_restart hγ hγ1 Z₀ r hr href g W hW E hH hU hLipU hcU D
  have hWball : W ∈ ball W ρ := mem_ball_self hρ
  let f : ℝ → (ι → LittleContourSpace γ) → ι → LittleContourSpace γ :=
    fun t V => finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g V + E t V
  let Y := concatenateAtEndpoint α (X W) D W
  have hfc : ContinuousAt (fun p : ℝ × (ι → LittleContourSpace γ) => f p.1 p.2) (D, W) :=
    continuousAt_finitePhase_forcedField hγ hγ1 Z₀ r hr href g W hW E
      hV hELip (hEc W (mem_of_mem_nhds hV)).continuousAt
  have hβ0 : X W 0 = W := hX.initial W hWball
  have hβ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) δ) :
      HasDerivAt (X W) (f (D + s) (X W s)) s := hX.hasDerivAt W hWball s hs
  have hYderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (D + δ)) :
      HasDerivAt Y (f t (Y t)) t :=
    concatenateAtEndpoint_hasDerivAt hD hδ.le hα hlim hfc hβ0 hβ ht
  have hYmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (D + δ)) :
      IsPhaseAdmissibleLittleContourFamily Z₀ r (Y t) ∧
      ‖Y t‖ < a / 4 ∧ IsQuarterPhaseLittleContourFamily Z₀ r (Y t) := by
    rcases lt_trichotomy t D with hlt | heq | hgt
    · simpa only [Y, concatenateAtEndpoint, if_pos hlt.le, leftEndpointExtension, if_pos hlt] using
        hαmem t ⟨ht.1, hlt⟩
    · subst t
      simpa only [Y, concatenateAtEndpoint, le_refl, if_true, leftEndpointExtension,
        lt_self_iff_false, if_false] using And.intro hW (And.intro hWa hWq)
    · have hs : t - D ∈ Icc (0 : ℝ) δ := ⟨by linarith, by linarith [ht.2]⟩
      have hm := hX.mem W hWball (t - D) hs
      simpa only [Y, concatenateAtEndpoint, if_neg (not_le.mpr hgt),
        Set.mem_ofPred_eq] using
        And.intro hm.1 (And.intro (mem_ball_zero_iff.mp hm.2.2.1) hm.2.2.2)
  refine ⟨δ, hδ, hδH, Y, ?_, ?_, ?_, hYderiv, hYmem, ?_⟩
  · intro t ht
    simp only [Y, concatenateAtEndpoint, if_pos ht.2.le, leftEndpointExtension, if_pos ht.2]
  · simp only [Y, concatenateAtEndpoint, le_refl, if_true, leftEndpointExtension,
      lt_self_iff_false, if_false]
  · exact fun t ht => (hYderiv t ht).continuousAt.continuousWithinAt
  · intro t ht i θ
    have hd := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
      (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t (hYderiv t ht)
    change HasDerivAt (fun s => LittleContourSpace.lift γ (Y s i) θ)
      (LittleContourSpace.lift γ (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (Y t) i) θ +
        LittleContourSpace.lift γ (E t (Y t) i) θ) t at hd
    rw [lift_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (Y t) (hYmem t ht).1 i θ] at hd
    exact hd

end Euler2D

end

