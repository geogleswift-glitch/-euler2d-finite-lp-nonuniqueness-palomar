module

public import RequestProject.Euler.CircularFiniteClusterContourForcing

/-! The actual inner labels, transported by one torus Euler inverse
map and placed in the physical plane, have a uniform planar self-speed
bound. This is the singular planar part in the true radial bootstrap. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem boxed_finitePeriodicLabel_bounds {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N j : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    Integrable (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) ∧
      (∀ x, |boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x| ≤
        finiteLabelAmplitudeBound * ampScale A₀ b j) ∧
      (∫ x : ℂ, |boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) x|) ≤
        finiteLabelMassBound * ampScale A₀ b j * radScale R ρ j ^ 2 := by
  obtain ⟨hi, hp, hsup, hm⟩ := P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j
  refine ⟨integrable_boxedComplexDensity (S.integrable_transportedScalar_of_integrable hi t), ?_, ?_⟩
  · intro x
    by_cases hx : complexTorusPoint x ∈ torusBox
    · rw [boxedComplexDensity, indicator_of_mem hx]
      simpa only [BoundedEulerParticleSystem.transportedScalar, Real.norm_eq_abs] using
        hsup (torusWrap (S.backward t (complexTorusPoint x)))
    · rw [boxedComplexDensity, indicator_of_notMem hx, abs_zero]
      exact mul_nonneg finiteLabelAmplitudeBound_nonneg (by unfold ampScale; positivity)
  · rw [integral_abs_boxedComplexDensity, S.integral_abs_transportedScalar hi hp t]
    exact hm

theorem exists_uniform_boxedFiniteLabel_planarVelocity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ : ℝ}, s ≤ 0 → 0 ≤ A₀ → 0 < b →
      0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 →
      ∀ N j : ℕ, ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T), ∀ t x,
        ‖velocityC (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x‖ ≤
            C * ampScale A₀ b j * radScale R ρ j := by
  let C := finiteLabelAmplitudeBound + finiteLabelMassBound / (2 * Real.pi) + 1
  have hC : 0 < C := by dsimp [C]; positivity [finiteLabelAmplitudeBound_nonneg, finiteLabelMassBound_nonneg]
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ hs hA hb hR hRmax hρ hρ1 N j f T S t x
  obtain ⟨hi, hsup, hm⟩ := P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j S t
  have hr := radScale_pos hR hρ j
  have hAj : 0 ≤ ampScale A₀ b j := by unfold ampScale; positivity
  calc
    _ ≤ (finiteLabelAmplitudeBound * ampScale A₀ b j) * radScale R ρ j +
        (∫ y : ℂ, |boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) y|) /
            (2 * Real.pi * radScale R ρ j) := velocity_bound_split hi hsup x hr
    _ ≤ (finiteLabelAmplitudeBound * ampScale A₀ b j) * radScale R ρ j +
        (finiteLabelMassBound * ampScale A₀ b j * radScale R ρ j ^ 2) /
          (2 * Real.pi * radScale R ρ j) := add_le_add le_rfl (div_le_div_of_nonneg_right hm (by positivity))
    _ = (finiteLabelAmplitudeBound + finiteLabelMassBound / (2 * Real.pi)) *
        ampScale A₀ b j * radScale R ρ j := by field_simp [hr.ne'] <;> ring
    _ ≤ C * ampScale A₀ b j * radScale R ρ j := by
      apply mul_le_mul_of_nonneg_right _ hr.le
      apply mul_le_mul_of_nonneg_right _ hAj
      dsimp [C]
      linarith

theorem velocityC_finiteInnerClusterComplexSource_eq_sum {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x =
      ∑ j ∈ Finset.Ico (k + 1) (N + 1), velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x := by
  have he : P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t =
      fun y => ∑ j ∈ Finset.Ico (k + 1) (N + 1), boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t) y := by
    funext y
    by_cases hy : complexTorusPoint y ∈ torusBox <;>
      simp [finiteInnerClusterComplexSource, finiteInnerClusterSource, boxedComplexDensity, hy]
  rw [he]
  unfold velocityC
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  apply integral_finset_sum
  intro j _
  obtain ⟨hi, hsup, _⟩ := P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j S t
  exact integrable_velocity_integrand hi hsup x

theorem exists_uniform_finiteInnerCluster_planarVelocity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ : ℝ}, s ≤ 0 → 0 ≤ A₀ → 0 < b →
      0 < R → R ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → ρ < b →
      ∀ N k : ℕ, ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T), ∀ t x,
        ‖velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x‖ ≤
          C * ampScale A₀ b k * radScale R ρ k * (ρ / b) / (1 - ρ / b) := by
  obtain ⟨C, hC, hlabel⟩ := P.exists_uniform_boxedFiniteLabel_planarVelocity_bound
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ hs hA hb hR hRmax hρ hρ1 hρb N k f T S t x
  rw [P.velocityC_finiteInnerClusterComplexSource_eq_sum hs hA hb hR hRmax hρ hρ1 N k S t x]
  have hκ0 : 0 ≤ ρ / b := div_nonneg hρ.le hb.le
  have hκ1 : ρ / b < 1 := (div_lt_one hb).mpr hρb
  have hsum : ∑ j ∈ Finset.Ico (k + 1) (N + 1), (ρ / b) ^ j ≤
      (ρ / b) ^ (k + 1) / (1 - ρ / b) := geom_sum_Ico_le_of_lt_one hκ0 hκ1
  have hscale (j : ℕ) : ampScale A₀ b j * radScale R ρ j = (A₀ * R) * (ρ / b) ^ j := by
    simp only [ampScale, radScale, div_pow, div_eq_mul_inv]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.Ico (k + 1) (N + 1), ‖velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Ico (k + 1) (N + 1), (C * (A₀ * R)) * (ρ / b) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact (hlabel hs hA hb hR hRmax hρ hρ1 N j S t x).trans_eq (by rw [mul_assoc, hscale]; ring)
    _ = (C * (A₀ * R)) * ∑ j ∈ Finset.Ico (k + 1) (N + 1), (ρ / b) ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C * (A₀ * R)) * ((ρ / b) ^ (k + 1) / (1 - ρ / b)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      conv_rhs => rw [mul_assoc C, hscale]
      rw [pow_succ]
      ring

end CircularMaterialTransferProfile
end Euler2D

end
