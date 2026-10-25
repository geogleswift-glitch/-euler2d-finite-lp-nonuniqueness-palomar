module

public import RequestProject.Euler.CircularMaterialTransferProfile
public import RequestProject.Euler.CircularFlattenedAncientMomentAsymptotic

/-! One original physical transfer profile retains its same sharp Y,
actual material return map, and proved flattened capture budget. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

theorem exists_circularMaterial_moment_LaplaceHyp_with_flattenedGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ Y : ℝ → Fin 2 → LittleContourSpace γ,
    ∃ S : GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity (Y 0)),
    ∃ κ : ℂ, ∃ δ : ℝ, ∃ N : ℝ → ℂ,
      ContinuousOn Y (Iic 0) ∧
      (∀ s ≤ 0, Y s ∈ circularQuarterPhaseDomain hγ hγ1) ∧
      (∀ s ≤ 0, HasDerivAt Y (circularBanachField hγ hγ1 (Y s)) s) ∧
      Tendsto (fun n : ℕ => Y (-(n : ℝ) * (period + period))) atTop
        (𝓝 (littleCircularReference hγ hγ1)) ∧
      (∀ s ≤ 0, ∀ i, littleContourArea γ (Y s i) = Real.pi * circularContourRadii i ^ 2) ∧
      (∀ s ≤ 0, ∀ i, Y s i ∈ fourfoldLittleContourSubmodule γ) ∧
      IsOriginFourfoldGlobalPlanarEulerParticleSystem S ∧
      (∀ s ≤ 0, N s = circularBoundaryFourthMoment (Y s)) ∧
      (∀ s, 0 ≤ s → N s = planarFourthMoment (S.vorticity s)) ∧
      LaplaceHyp sigma (-3 / 4) δ 4 κ N ∧ HasCircularFlattenedAncientSamples hγ hγ1 Y := by
  obtain ⟨Y, κ, δ, hδ, hκ, hYc, hYm, hYd, hLim, hArea, hFour, hbot, hflatY⟩ :=
    exists_circularAncientMaterial_fourthMoment_with_flattenedGraph hγ hγ1
  have hY0 := hYm 0 le_rfl
  obtain ⟨S, hS⟩ := exists_circularPhasePatch_originFourfoldGlobalPlanarEuler hγ hγ1 hY0 (hFour 0 le_rfl)
  have hw := integrable_circularPhasePatchPlanarVorticity hγ hγ1 hY0
  have hB := norm_circularPhasePatchPlanarVorticity_le hγ hγ1 hY0
  have hsource := fun x => norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1 hY0 (x := x)
  let V := planarBiotSavartMassBound (finiteContourPatchSupBound circularContourStrengths)
    (∫ x, ‖circularPhasePatchPlanarVorticity (Y 0) x‖)
  have hspeed : ∀ t x, ‖S.velocity t x‖ ≤ V := S.norm_velocity_le hw hB
  have hV : 0 ≤ V := (norm_nonneg (S.velocity 0 0)).trans (hspeed 0 0)
  have hR : (0 : ℝ) ≤ 5 / 4 := by norm_num
  have hpos : ContinuousOn (fun s : ℝ => planarFourthMoment (S.vorticity s)) (Ici (0 : ℝ)) :=
    S.continuousOn_fourthMoment_nonneg hw hR hV hsource hspeed
  have hneg : ContinuousOn (fun s : ℝ => circularBoundaryFourthMoment (Y s)) (Iic (0 : ℝ)) :=
    (contDiff_circularBoundaryFourthMoment γ).continuous.comp_continuousOn hYc
  have hmatch : planarFourthMoment (S.vorticity 0) = circularBoundaryFourthMoment (Y 0) := by
    rw [S.vorticity_zero]
    exact planarFourthMoment_circularPhasePatchPlanarVorticity hγ hγ1 hY0
  let N : ℝ → ℂ := fun s => if s ≤ 0 then circularBoundaryFourthMoment (Y s)
    else planarFourthMoment (S.vorticity s)
  have hNneg (s : ℝ) (hs : s ≤ 0) : N s = circularBoundaryFourthMoment (Y s) := if_pos hs
  have hNpos (s : ℝ) (hs : 0 ≤ s) : N s = planarFourthMoment (S.vorticity s) := by
    by_cases hz : s ≤ 0
    · have he : s = 0 := le_antisymm hz hs
      subst s
      rw [hNneg 0 le_rfl]
      exact hmatch.symm
    · exact if_neg hz
  have hNcneg : ContinuousOn N (Iic (0 : ℝ)) := hneg.congr (fun s hs => hNneg s hs)
  have hNcpos : ContinuousOn N (Ici (0 : ℝ)) := hpos.congr (fun s hs => hNpos s hs)
  have hNcu := hNcneg.union_of_isClosed hNcpos isClosed_Iic isClosed_Ici
  have hunion : Iic (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext s
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total s 0
  rw [hunion] at hNcu
  have hNc : Continuous N := continuousOn_univ.mp hNcu
  have hexp (s : ℝ) : (s : ℂ) * lamStar =
      ((sigma : ℂ) + ((-3 / 4 : ℝ) : ℂ) * I) * (s : ℂ) := by
    unfold lamStar
    push_cast
    ring
  have hbotN : (fun s : ℝ => N s - κ * Complex.exp
      (((sigma : ℂ) + ((-3 / 4 : ℝ) : ℂ) * I) * (s : ℂ))) =O[atBot]
      (fun s : ℝ => Real.exp ((sigma + δ) * s)) := by
    apply hbot.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
    rw [hNneg s hs, hexp s]
  refine ⟨Y, S, κ, δ, N, hYc, hYm, hYd, hLim, hArea, hFour, hS, hNneg, hNpos, ?_, hflatY⟩
  refine ⟨sigma_pos, hδ, by norm_num, hκ, hNc.locallyIntegrable, hbotN, ?_⟩
  refine ⟨(∫ x, ‖circularPhasePatchPlanarVorticity (Y 0) x‖) * (5 / 4 + V) ^ 4, ?_⟩
  intro s hs
  rw [hNpos s hs]
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact S.fourthMoment_polynomial_bound hw hR hV hsource hspeed hs


theorem exists_circularMaterialTransferProfile_with_flattenedGraph {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    ∃ P : CircularMaterialTransferProfile hγ hγ1,
      HasCircularFlattenedAncientSamples hγ hγ1 P.ancient := by
  obtain ⟨Y, S, κ, δ, N, hYc, hYm, hYd, hLim, hArea, hFour, hS, hNm, hNp, hN, hflatY⟩ :=
    exists_circularMaterial_moment_LaplaceHyp_with_flattenedGraph hγ hγ1
  exact ⟨⟨Y, S, κ, δ, N, hYc, hYm, hYd, hLim, hArea, hFour, hS, hNm, hNp, hN⟩, hflatY⟩

end Euler2D

end

