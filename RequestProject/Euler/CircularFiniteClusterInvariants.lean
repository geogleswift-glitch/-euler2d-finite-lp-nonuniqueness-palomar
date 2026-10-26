module

public import RequestProject.Euler.CircularFiniteClusterVelocity

/-! Genuine transported inner-cluster invariants and mass budget.
All labels use the same actual Euler inverse map; no cluster radius or
geometry assumption is substituted for this transport. -/

@[expose] public section

set_option maxHeartbeats 2700000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem integral_transportedScalar {w : R2 → ℝ} (hw : Integrable w μT)
    (hper : IsTorusPeriodic w) (t : ℝ) :
    (∫ x in torusBox, S.transportedScalar w t x) = ∫ x in torusBox, w x := by
  simp_rw [S.transportedScalar_eq_of_periodic hper]
  exact (S.backward_area t).integral_comp hw.aestronglyMeasurable hper

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finitePlanarLabel_perpJ {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (N j : ℕ) (x : R2) :
    P.finitePlanarLabel s A₀ b R ρ N j (perpJ x) = P.finitePlanarLabel s A₀ b R ρ N j x := by
  by_cases hj : j = N
  · simp only [finitePlanarLabel, if_pos hj, finiteBaseDensity, ← perpJ_smul,
      circularPhasePatchPlanarVorticity_fourfold (P.ancient s) (P.ancient_fourfold s hs)]
  · simp only [finitePlanarLabel, if_neg hj, datumTerm_perpJ]

theorem finitePeriodicLabel_quarterTurn {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (N j : ℕ) (x : R2) :
    P.finitePeriodicLabel s A₀ b R ρ N j (torusQuarterTurn x) =
      P.finitePeriodicLabel s A₀ b R ρ N j x := by
  change (∑' k, P.finitePlanarLabel s A₀ b R ρ N j
    (torusQuarterTurn x + torusLatticeShift k - torusCenter)) = _
  rw [← torusLatticeQuarterTurn.tsum_eq]
  apply tsum_congr
  intro k
  rw [torusLatticeShift_quarterTurn, ← torusQuarterTurn_add]
  simp only [torusQuarterTurn, add_sub_cancel_left, P.finitePlanarLabel_perpJ hs]

theorem integral_finitePlanarLabel_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hρ : 0 < ρ) (N j : ℕ) :
    (∫ x, P.finitePlanarLabel s A₀ b R ρ N j x) = 0 := by
  by_cases hj : j = N
  · simp only [finitePlanarLabel, if_pos hj]
    exact P.integral_finiteBaseDensity_zero hs hR hρ N
  · simp only [finitePlanarLabel, if_neg hj]
    exact integral_datumTerm hR hρ j

theorem integral_finitePeriodicLabel_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N j : ℕ) :
    (∫ x in torusBox, P.finitePeriodicLabel s A₀ b R ρ N j x) = 0 := by
  rw [finitePeriodicLabel, integral_periodicCenteredSource
    (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j)]
  exact P.integral_finitePlanarLabel_zero hs hR hρ N j

theorem integrable_finiteInnerClusterSource {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    Integrable (P.finiteInnerClusterSource s A₀ b R ρ N k S t) μT := by
  exact integrable_finset_sum _ fun j _ => S.integrable_transportedScalar_of_integrable
    (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).1 t

theorem integral_finiteInnerClusterSource_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    (∫ x in torusBox, P.finiteInnerClusterSource s A₀ b R ρ N k S t x) = 0 := by
  unfold finiteInnerClusterSource
  rw [integral_finset_sum _ (fun j _ => S.integrable_transportedScalar_of_integrable
    (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).1 t)]
  apply Finset.sum_eq_zero
  intro j _
  obtain ⟨hi, hp, _, _⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
  rw [S.integral_transportedScalar hi hp t]
  exact P.integral_finitePeriodicLabel_zero hs hR hRmax hρ hρ1 N j

theorem finiteInnerClusterSource_quarterTurn {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    P.finiteInnerClusterSource s A₀ b R ρ N k S t (torusQuarterTurn x) =
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x := by
  apply Finset.sum_congr rfl
  intro j _
  exact S.transportedScalar_quarterTurn hS (isTorusPeriodic_periodicCenteredSource _)
    (P.finitePeriodicLabel_quarterTurn hs N j) t ht x

theorem integral_abs_finiteInnerClusterSource_le {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : ρ ^ 2 < b) (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    (∫ x in torusBox, |P.finiteInnerClusterSource s A₀ b R ρ N k S t x|) ≤
      finiteLabelMassBound * ampScale A₀ b k * radScale R ρ k ^ 2 *
        (ρ ^ 2 / b) / (1 - ρ ^ 2 / b) := by
  have hi (j : ℕ) := S.integrable_transportedScalar_of_integrable
    (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).1 t
  have hmass (j : ℕ) : (∫ x in torusBox,
      |S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x|) ≤
      finiteLabelMassBound * ampScale A₀ b j * radScale R ρ j ^ 2 := by
    obtain ⟨hij, hpj, _, hjm⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
    rwa [S.integral_abs_transportedScalar hij hpj t]
  have hκ0 : 0 ≤ ρ ^ 2 / b := div_nonneg (sq_nonneg _) hb.le
  have hκ1 : ρ ^ 2 / b < 1 := (div_lt_one hb).mpr hsmall
  have hsum : ∑ j ∈ Finset.Ico (k + 1) (N + 1), (ρ ^ 2 / b) ^ j ≤
      (ρ ^ 2 / b) ^ (k + 1) / (1 - ρ ^ 2 / b) := geom_sum_Ico_le_of_lt_one hκ0 hκ1
  have hscale (j : ℕ) : ampScale A₀ b j * radScale R ρ j ^ 2 =
      (A₀ * R ^ 2) * (ρ ^ 2 / b) ^ j := by
    simpa only [div_one, Real.rpow_two] using
      (datum_scale_geometric (A₀ := A₀) (b := b) (q := 1) hR.le hρ.le j)
  calc
    _ ≤ ∫ x in torusBox, ∑ j ∈ Finset.Ico (k + 1) (N + 1),
        |S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x| := by
      apply integral_mono (P.integrable_finiteInnerClusterSource hs hA hb hR hRmax hρ hρ1 N k S t).abs
        (integrable_finset_sum _ (fun j _ => (hi j).abs))
      intro x
      change |∑ j ∈ Finset.Ico (k + 1) (N + 1),
        S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x| ≤
        ∑ j ∈ Finset.Ico (k + 1) (N + 1),
          |S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x|
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.Ico (k + 1) (N + 1))
        (fun j => S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x)
    _ = ∑ j ∈ Finset.Ico (k + 1) (N + 1), ∫ x in torusBox,
        |S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x| :=
      integral_finset_sum _ (fun j _ => (hi j).abs)
    _ ≤ ∑ j ∈ Finset.Ico (k + 1) (N + 1),
        (finiteLabelMassBound * (A₀ * R ^ 2)) * (ρ ^ 2 / b) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact (hmass j).trans_eq (by rw [mul_assoc, hscale]; ring)
    _ = (finiteLabelMassBound * (A₀ * R ^ 2)) *
        ∑ j ∈ Finset.Ico (k + 1) (N + 1), (ρ ^ 2 / b) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (finiteLabelMassBound * (A₀ * R ^ 2)) *
        ((ρ ^ 2 / b) ^ (k + 1) / (1 - ρ ^ 2 / b)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity [finiteLabelMassBound_nonneg])
    _ = _ := by
      conv_rhs => rw [mul_assoc finiteLabelMassBound, hscale]
      rw [pow_succ]
      ring

end CircularMaterialTransferProfile
end Euler2D

end
