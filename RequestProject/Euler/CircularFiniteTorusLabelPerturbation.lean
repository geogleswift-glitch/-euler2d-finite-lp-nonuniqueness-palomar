module

public import RequestProject.Euler.ActualTorusRadialPerturbationBudget
public import RequestProject.Euler.PhasePatchPerturbationMomentBudget
public import RequestProject.Euler.CircularFiniteExteriorReference
public import RequestProject.Euler.CircularFiniteRealRadialFeedback

/-! The actual periodic velocity of one transported finite label is
controlled by that label's own material deviation. All source bounds,
zero mass and radial-reference cancellation are supplied here from the
original label and its actual material geometry. -/

@[expose] public section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_finiteLabel_torus_contourLittle_perturbation :
    ∃ C : ℝ, 0 < C ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c δ ql a rj L : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → 0 < a → a ≤ 1 / 16 →
      ∀ (N : ℕ) (l : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N l S t c δ,
      0 ≤ ql →
      (∀ i, ‖contourParameterShiftC1 (G.shifts (l, i)) (G.contours (l, i)) -
        G.reference (l, i)‖ ≤ radScale R ρ l * ql) →
      (5 / 4 : ℝ) * radScale R ρ l ≤ a →
      0 < rj → 0 ≤ L → (L + 1) * rj ≤ a / 2 →
      ∀ W : LittleContourSpace η, ‖W‖ ≤ L * rj →
      ∃ Q : LittleContourSpace η,
        (∀ θ, LittleContourSpace.lift η Q θ =
          actualTorusCorrectionVelocity
            (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t))
            (LittleContourSpace.lift η W θ)) ∧
        ‖Q‖ / rj ≤ C * torusCorrectionContourBudget (η : ℝ) L * rj ^ 2 *
          (4 * Real.pi * (ampScale A₀ b l * circularRadialPerturbationWeight)) *
            (5 / 4 : ℝ) ^ 4 * radScale R ρ l ^ 6 * ql := by
  obtain ⟨C, hC, hsource⟩ := exists_uniform_actualTorusCorrection_radialPerturbation_contourLittle
  refine ⟨C, hC, ?_⟩
  intro η hη s A₀ b R ρ c δ ql a rj L hs hA hb hR hRmax hρ hρ1 ha ha16
    N l f T S t ht G hql0 hql hradius hrj hL hgeom W hW
  let rl := radScale R ρ l
  let w := boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)
  let v : ℂ → ℝ := fun y => ∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (l, i) *
    circlePatchVorticity (circularContourRadii i * rl) y
  have hrl : 0 < rl := radScale_pos hR hρ l
  have hAl : 0 < ampScale A₀ b l := by unfold ampScale; positivity
  have hmax (i : Fin 2) : (5 / 4 : ℝ) * circularContourRadii i ≤ 5 / 4 := by
    nlinarith only [(circularContourRadii_bounds i).2.2]
  have hdEq : (fun y => w y - v y) =
      phaseFiniteContourPatchPerturbation
        (fun i => finiteCircularInterfaceStrength A₀ b (l, i))
        (fun i => G.contours (l, i)) (fun i => circularContourRadii i * rl) :=
    P.finiteOuterLabelComplexPerturbation_eq_phaseContours hs hR hRmax hρ hρ1
      N l S G.contours t ht (G.initial_box l le_rfl)
      (G.current_box l le_rfl) (G.images l le_rfl)
  obtain ⟨_hiD, hDsupp, _hDL1, hDM4⟩ := phaseFiniteContourPatchPerturbation_moment_budget
    (fun i => finiteCircularInterfaceStrength A₀ b (l, i))
    (fun i => G.contours (l, i)) (fun i => G.reference (l, i))
    circularContourRadii (fun i => G.shifts (l, i)) hrl
    (by norm_num : (0 : ℝ) ≤ 5 / 4) hql0
    (fun i => (circularContourRadii_bounds i).1)
    (G.reference_lift l le_rfl) (G.quarter_tube l le_rfl) hql hmax
  have hw : Integrable w :=
    (P.boxed_finitePeriodicLabel_bounds hs hA.le hb hR hRmax hρ hρ1 N l S t).1
  have hv : Integrable v := integrable_finset_sum _ fun i _ =>
    (integrable_circlePatchVorticity _).const_mul _
  have hvs : ∀ y : ℂ, a < ‖y‖ → v y = 0 := by
    intro y hy
    apply Finset.sum_eq_zero
    intro i _
    have hi : circularContourRadii i * rl ≤ a :=
      (mul_le_of_le_one_left hrl.le (circularContourRadii_bounds i).2.2).trans
        (by change rl ≤ a; change (5 / 4 : ℝ) * rl ≤ a at hradius; linarith only [hradius, hrl])
    have hnot : y ∉ ball (0 : ℂ) (circularContourRadii i * rl) := by
      rw [mem_ball_zero_iff, not_lt]
      exact hi.trans hy.le
    rw [circlePatchVorticity, indicator_of_notMem hnot, mul_zero]
  have hws : ∀ y : ℂ, a < ‖y‖ → w y = 0 := by
    intro y hy
    have hh : w y - v y = 0 := (congrFun hdEq y).trans (hDsupp y (hradius.trans_lt hy))
    simpa only [hvs y hy, sub_zero] using hh
  have hvr : ∀ (θ : ℝ) (y : ℂ), v (exp ((θ : ℂ) * I) * y) = v y := by
    intro θ y
    apply Finset.sum_congr rfl
    intro i _
    have he : ‖exp ((θ : ℂ) * I) * y‖ = ‖y‖ := by
      rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
    by_cases hy : ‖y‖ < circularContourRadii i * rl <;>
      simp [circlePatchVorticity, mem_ball_zero_iff, he, hy]
  have hvy (y : ℂ) : v (I * y) = v y := by
    apply Finset.sum_congr rfl
    intro i _
    rw [circlePatchVorticity_mul_I]
  have hwy : ∀ y : ℂ, w (I * y) = w y := by
    intro y
    have hdrot : w (I * y) - v (I * y) = w y - v y := by
      change (fun y => w y - v y) (I * y) = (fun y => w y - v y) y
      rw [hdEq]
      exact phaseFiniteContourPatchPerturbation_fourfold _ _ _ (G.fourfold l le_rfl) y
    rw [hvy y] at hdrot
    linarith only [hdrot]
  have hwm : (∫ y, w y) = 0 := by
    obtain ⟨hilabel, hper, _⟩ := P.finitePeriodicLabel_bounds hs hA.le hb hR hRmax hρ hρ1 N l
    change (∫ y, boxedComplexDensity
      (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) y) = 0
    rw [integral_boxedComplexDensity, S.integral_transportedScalar hilabel hper,
      P.integral_finitePeriodicLabel_zero hs hR hRmax hρ hρ1 N l]
  have hvm : (∫ y, v y) = 0 := finiteCircularReference_integral_zero hR hρ l
  have hM4 : (∫ y : ℂ, ‖y‖ ^ 4 * |w y - v y|) ≤
      (4 * Real.pi * (ampScale A₀ b l * circularRadialPerturbationWeight)) *
        (5 / 4 : ℝ) ^ 4 * rl ^ 6 * ql := by
    change (∫ y : ℂ, ‖y‖ ^ 4 * |(fun y => w y - v y) y|) ≤ _
    rw [hdEq]
    rw [finiteCircularInterfaceRadialWeight_eq, abs_of_nonneg hAl.le] at hDM4
    exact hDM4
  obtain ⟨Q, hQ, hn⟩ := hsource ha ha16 hη w v hw hv hws hvs hwm hvm hwy hvr
    hrj hL hgeom W hW
  have hCt : 0 ≤ torusCorrectionContourBudget (η : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  refine ⟨Q, hQ, hn.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hM4 (mul_nonneg (mul_nonneg hC.le hCt) (by positivity))).trans_eq
    (by dsimp only [rl]; ring)

end CircularMaterialTransferProfile
end Euler2D

end
