module

public import RequestProject.Euler.TorusPhysicalRadialFeedback
public import RequestProject.Euler.CircularFiniteTorusCorrectionBudget
public import RequestProject.Euler.CircularFinitePlanarRadialFeedback

/-! The original same-S real particle velocity differs radially from
the full actual planar finite source by the genuine uniform
R^8 (b rho^2)^k correction. Initial L1 mass is conserved exactly;
the growing finite L-infinity auxiliary never enters this bound. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteEuler_uniformRadialCorrection_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {s A₀ b R ρ q T d : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 < A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (_hsmall : ρ ^ 2 < b)
        (_hd : 0 < d) (_hd16 : d * R ≤ 1 / 16),
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      (∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t y = 0) →
      ∀ k : ℕ, ∀ x : ℂ, ‖x‖ ≤ d * R →
      inner ℝ (complexTorusPoint x - torusCenter)
        (particleVelocityRepresentative
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          S.backward S.backward_area t (complexTorusPoint x)) ≤
        (velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x * conj x).re +
          (K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ k *
            (ampScale A₀ b k / radScale R ρ k ^ 2)) * ‖x‖ ^ 4 := by
  obtain ⟨K, hK, hcorrection⟩ := exists_uniform_actualEuler_radialCorrection_bound
  refine ⟨K, hK, ?_⟩
  intro s A₀ b R ρ q T d _ hs hA hb hR hRmax hρ hρ1 hq hqE hsmall hd hd16 N S hS t ht hsupp k x hx
  let w := P.finiteInitialPeriodicDensity s A₀ b R ρ N
  have hwf : w =ᵐ[μT] (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with y hy hybox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hybox).trans hy.symm
  let M : ℝ := ∑ j ∈ Finset.range (N + 1), finiteLabelAmplitudeBound * ampScale A₀ b j
  have hwM : ∀ y, ‖w y‖ ≤ M := by
    intro y
    rw [show w y = ∑ j ∈ Finset.range (N + 1), P.finitePeriodicLabel s A₀ b R ρ N j y from
      P.finiteInitialPeriodicDensity_eq_sum_labels hs hR hRmax hρ hρ1 N y]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ =>
      (P.finitePeriodicLabel_bounds hs hA.le hb hR hRmax hρ hρ1 N j).2.2.1 y))
  have hm : (∫ y in torusBox, finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N y) = 0 :=
    (integral_congr_ae hwf).symm.trans
      (P.integral_finiteInitialPeriodicDensity_zero hs hR hRmax hρ hρ1 N)
  have hactual := hcorrection S hS hwf hwM
    (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
    (P.finiteInitialPeriodicDensity_quarterTurn hs N) hm (mul_pos hd hR) hd16 ht hsupp x hx
  have hmass := S.physicalComplexSource_fourthAbsoluteMoment_le_initialL1 hwf hsupp
  have hf := P.integral_abs_finiteBaseCurlL2_le hs hA.le hb hR hρ hq hqE hsmall N
  rw [finiteBaseNormBound_one_eq] at hf
  have hfour : (∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y|) ≤
      (d * R) ^ 4 * (circularFiniteL1Coefficient b ρ * (A₀ * R ^ 2)) :=
    hmass.trans (mul_le_mul_of_nonneg_left hf (by positivity))
  have hcoord : planeComplexEquiv (complexTorusPoint x - torusCenter) = x := by
    rw [← normalizedComplexCoordinate_one, normalizedComplexCoordinate_one_complexTorusPoint]
  rw [real_inner_eq_complex_radial_product, hcoord]
  calc
    _ = (velocityC (S.physicalComplexSource w t) x * conj x).re +
        ((planeComplexEquiv (particleVelocityRepresentative _ S.backward S.backward_area t (complexTorusPoint x)) -
          velocityC (S.physicalComplexSource w t) x) * conj x).re := by
      rw [sub_mul, sub_re]
      ring
    _ ≤ (velocityC (S.physicalComplexSource w t) x * conj x).re +
        K * ‖x‖ ^ 4 * (∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y|) :=
      add_le_add le_rfl ((le_abs_self _).trans hactual)
    _ ≤ (velocityC (S.physicalComplexSource w t) x * conj x).re +
        K * ‖x‖ ^ 4 * ((d * R) ^ 4 * (circularFiniteL1Coefficient b ρ * (A₀ * R ^ 2))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hfour (by positivity))
    _ = _ := by
      dsimp only [w]
      have hp : (ρ ^ 2) ^ k = (ρ ^ k) ^ 2 := by simp only [← pow_mul, Nat.mul_comm]
      rw [mul_pow b (ρ ^ 2) k, hp]
      unfold ampScale radScale
      field_simp [hb.ne', hR.ne', hρ.ne']
      <;> simp only [mul_comm, mul_left_comm, mul_assoc]
      <;> ring

end CircularMaterialTransferProfile
end Euler2D

end
