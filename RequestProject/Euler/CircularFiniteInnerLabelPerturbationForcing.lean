module

public import RequestProject.Euler.CircularFiniteExteriorReference
public import RequestProject.Euler.PhaseExteriorPerturbationForcing
public import RequestProject.Euler.CircularFiniteRealRadialFeedback

/-! The entire actual transported inner label produces a sixth-ratio
Little forcing linear in that label's own material displacement. All
cancellation and source identities use the same original finite S. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteInnerLabel_contourLittle_sixthRatio
    {η : ℝ≥0} (hη : (η : ℝ) ≤ 1) {s A₀ b R ρ c δ ql e rj L : ℝ}
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (l : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N l S t c δ)
    (hql0 : 0 ≤ ql)
    (hql : ∀ i, ‖contourParameterShiftC1 (G.shifts (l, i)) (G.contours (l, i)) -
      G.reference (l, i)‖ ≤ radScale R ρ l * ql)
    (he : 0 < e) (hrj : 0 < rj) (hsep : 10 * radScale R ρ l ≤ e * rj)
    (W : LittleContourSpace η)
    (hW : ∀ x, e * rj ≤ ‖ContourC1Space.toBCF η W.val x‖)
    (hL : ‖W‖ ≤ rj * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t))
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / rj ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L *
        (4 * Real.pi * (ampScale A₀ b l * circularRadialPerturbationWeight)) *
          (5 / 4 : ℝ) ^ 4 * (radScale R ρ l / rj) ^ 6 * ql := by
  have hr : 0 < radScale R ρ l := radScale_pos hR hρ l
  have hAl : 0 < ampScale A₀ b l := by unfold ampScale; positivity
  have heq := P.finiteOuterLabelComplexPerturbation_eq_phaseContours
    (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N l S G.contours t ht
    (G.initial_box l le_rfl) (G.current_box l le_rfl) (G.images l le_rfl)
  have hm : (∫ x, phaseFiniteContourPatchPerturbation
      (fun i => finiteCircularInterfaceStrength A₀ b (l, i))
      (fun i => G.contours (l, i)) (fun i => circularContourRadii i * radScale R ρ l) x) = 0 := by
    rw [← heq]
    exact P.integral_finiteOuterLabelComplexPerturbation_zero hs hA.le hb hR hRmax hρ hρ1 N l S t
  have hmax (i : Fin 2) : (5 / 4 : ℝ) * circularContourRadii i ≤ 5 / 4 := by
    nlinarith only [(circularContourRadii_bounds i).2.2]
  obtain ⟨Q, hQ, hn⟩ := exists_phaseExteriorPerturbationContourLittle_ratio hη
    (fun i => finiteCircularInterfaceStrength A₀ b (l, i))
    (fun i => G.contours (l, i)) (fun i => G.reference (l, i))
    circularContourRadii (fun i => G.shifts (l, i)) hr hrj (by norm_num : (0 : ℝ) ≤ 5 / 4)
    he hql0 (fun i => (circularContourRadii_bounds i).1)
    (G.reference_lift l le_rfl) (G.quarter_tube l le_rfl) hql hmax
    (G.fourfold l le_rfl) hm (by nlinarith only [hsep]) W hW hL
  rw [finiteCircularInterfaceRadialWeight_eq, abs_of_nonneg hAl.le] at hn
  refine ⟨Q, ?_, hn⟩
  intro θ
  rw [hQ θ, ← heq]
  symm
  apply P.velocityC_boxed_finiteLabel_eq_exteriorPerturbation hs hA.le hb hR hRmax hρ hρ1
    N l S t
  have hh := hW (θ : ContourCircle)
  change e * rj ≤ ‖LittleContourSpace.lift η W θ‖ at hh
  exact (by nlinarith only [hsep, hr] : radScale R ρ l ≤ e * rj).trans hh

end CircularMaterialTransferProfile
end Euler2D

end

