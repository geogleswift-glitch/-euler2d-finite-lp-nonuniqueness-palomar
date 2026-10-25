module

public import RequestProject.Euler.CircularMaterialMomentLaplaceHyp
public import RequestProject.Euler.Transfer
public import RequestProject.Euler.Survival
public import RequestProject.Euler.ClusterField
public import RequestProject.Euler.CircularAncientNesting

/-! A concrete material/Euler moment profile with an actual nonzero
transfer scale. The retarded linear response to its real moment is
nonzero at a finite nonnegative time. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

structure CircularMaterialTransferProfile {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) where
  ancient : ℝ → Fin 2 → LittleContourSpace γ
  positive : GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity (ancient 0))
  coefficient : ℂ
  errorExponent : ℝ
  moment : ℝ → ℂ
  ancient_continuous : ContinuousOn ancient (Iic 0)
  ancient_domain : ∀ s ≤ 0, ancient s ∈ circularQuarterPhaseDomain hγ hγ1
  ancient_derivative : ∀ s ≤ 0, HasDerivAt ancient (circularBanachField hγ hγ1 (ancient s)) s
  ancient_samples_tendsto : Tendsto (fun n : ℕ => ancient (-(n : ℝ) * (period + period))) atTop
    (𝓝 (littleCircularReference hγ hγ1))
  ancient_area : ∀ s ≤ 0, ∀ i, littleContourArea γ (ancient s i) = Real.pi * circularContourRadii i ^ 2
  ancient_fourfold : ∀ s ≤ 0, ∀ i, ancient s i ∈ fourfoldLittleContourSubmodule γ
  positive_fourfold : IsOriginFourfoldGlobalPlanarEulerParticleSystem positive
  moment_negative : ∀ s ≤ 0, moment s = circularBoundaryFourthMoment (ancient s)
  moment_positive : ∀ s, 0 ≤ s → moment s = planarFourthMoment (positive.vorticity s)
  laplace : LaplaceHyp sigma (-3 / 4) errorExponent 4 coefficient moment

theorem exists_circularMaterialTransferProfile {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    Nonempty (CircularMaterialTransferProfile hγ hγ1) := by
  obtain ⟨Y, S, κ, δ, N, hYc, hYm, hYd, hLim, hArea, hFour, hS, hNm, hNp, hN⟩ :=
    exists_circularMaterial_moment_LaplaceHyp_fourfold hγ hγ1
  exact ⟨⟨Y, S, κ, δ, N, hYc, hYm, hYd, hLim, hArea, hFour, hS, hNm, hNp, hN⟩⟩

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
  (P : CircularMaterialTransferProfile hγ hγ1)

theorem ancient_closure_nested {s : ℝ} (hs : s ≤ 0) :
    closure (contourRadialFill (LittleContourSpace.lift γ (P.ancient s 0))) ⊆
      contourRadialFill (LittleContourSpace.lift γ (P.ancient s 1)) :=
  circularAncientMaterial_closure_nested hγ hγ1 P.ancient_continuous P.ancient_domain
    P.ancient_derivative P.ancient_samples_tendsto hs

theorem positive_vorticity_fourfold (t : ℝ) (x : R2) :
    P.positive.vorticity t (perpJ x) = P.positive.vorticity t x :=
  P.positive_fourfold.vorticity
    (circularPhasePatchPlanarVorticity_fourfold _ (P.ancient_fourfold 0 le_rfl)) t x

theorem positive_velocity_fourfold (t : ℝ) (x : R2) :
    P.positive.velocity t (perpJ x) = perpJ (P.positive.velocity t x) :=
  P.positive_fourfold.velocity
    (circularPhasePatchPlanarVorticity_fourfold _ (P.ancient_fourfold 0 le_rfl)) t x

theorem positive_integral_vorticity_zero (t : ℝ) :
    (∫ x, P.positive.vorticity t x) = 0 := by
  have hw := integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain 0 le_rfl)
  have hm : AEStronglyMeasurable (circularPhasePatchPlanarVorticity (P.ancient 0))
      (volume.map (P.positive.backward t)) := by
    rw [(P.positive.backward_area t).map_eq]
    exact hw.aestronglyMeasurable
  have he := integral_map (P.positive.backward_area t).aemeasurable hm
  rw [(P.positive.backward_area t).map_eq] at he
  exact he.symm.trans (integral_circularPhasePatchPlanarVorticity_zero hγ hγ1
    (P.ancient_domain 0 le_rfl) (P.ancient_area 0 le_rfl))

def positiveComplexVorticity (t : ℝ) (z : ℂ) : ℝ :=
  P.positive.vorticity t (complexPhysicalPlane z)

def positiveSpeedBound : ℝ :=
  planarBiotSavartMassBound (finiteContourPatchSupBound circularContourStrengths)
    (∫ x, ‖circularPhasePatchPlanarVorticity (P.ancient 0) x‖)

theorem positive_norm_velocity_le (t : ℝ) (x : R2) :
    ‖P.positive.velocity t x‖ ≤ P.positiveSpeedBound :=
  P.positive.norm_velocity_le
    (integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain 0 le_rfl))
    (norm_circularPhasePatchPlanarVorticity_le hγ hγ1 (P.ancient_domain 0 le_rfl)) t x

theorem positiveSpeedBound_nonneg : 0 ≤ P.positiveSpeedBound :=
  (norm_nonneg (P.positive.velocity 0 0)).trans (P.positive_norm_velocity_le 0 0)

theorem integrable_positiveComplexVorticity (t : ℝ) : Integrable (P.positiveComplexVorticity t) :=
  complexPhysicalPlane.measurePreserving.integrable_comp_of_integrable
    (P.positive.integrable_vorticity
      (integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain 0 le_rfl)) t)

theorem positiveComplexVorticity_fourfold (t : ℝ) (z : ℂ) :
    P.positiveComplexVorticity t (I * z) = P.positiveComplexVorticity t z := by
  simpa only [positiveComplexVorticity, complexPhysicalPlane_mul_I] using
    P.positive_vorticity_fourfold t (complexPhysicalPlane z)

theorem integral_positiveComplexVorticity_zero (t : ℝ) :
    (∫ z, P.positiveComplexVorticity t z) = 0 := by
  exact (complexPhysicalPlane.measurePreserving.integral_comp
    complexPhysicalPlane.toHomeomorph.measurableEmbedding (P.positive.vorticity t)).trans
      (P.positive_integral_vorticity_zero t)

theorem positiveComplexVorticity_support {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : 5 / 4 + P.positiveSpeedBound * t < ‖z‖) : P.positiveComplexVorticity t z = 0 := by
  by_contra hn
  have hb := P.positive.norm_le_of_vorticity_ne_zero
    (fun x => norm_le_of_circularPhasePatchPlanarVorticity_ne_zero hγ hγ1
      (P.ancient_domain 0 le_rfl) (x := x)) P.positive_norm_velocity_le ht hn
  exact (not_lt_of_ge (by simpa only [LinearIsometryEquiv.norm_map] using hb)) hz

theorem integral_abs_positiveComplexVorticity (t : ℝ) :
    (∫ z, |P.positiveComplexVorticity t z|) =
      ∫ x, ‖circularPhasePatchPlanarVorticity (P.ancient 0) x‖ := by
  have he := complexPhysicalPlane.measurePreserving.integral_comp
    complexPhysicalPlane.toHomeomorph.measurableEmbedding (fun x => ‖P.positive.vorticity t x‖)
  have hw := integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain 0 le_rfl)
  simpa only [positiveComplexVorticity, Real.norm_eq_abs] using
    he.trans (P.positive.integral_norm_vorticity hw t)

theorem positiveComplexVorticity_fourthAbsoluteMoment_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, ‖z‖ ^ 4 * |P.positiveComplexVorticity t z|) ≤
      (∫ x, ‖circularPhasePatchPlanarVorticity (P.ancient 0) x‖) *
        (5 / 4 + P.positiveSpeedBound * t) ^ 4 := by
  let R := 5 / 4 + P.positiveSpeedBound * t
  have hi := integrable_norm_pow_mul_of_supp (P.integrable_positiveComplexVorticity t)
    (fun z hz => P.positiveComplexVorticity_support ht hz) 4
  have hj : Integrable (fun z => R ^ 4 * |P.positiveComplexVorticity t z|) := by
    simpa only [Real.norm_eq_abs] using (P.integrable_positiveComplexVorticity t).norm.const_mul (R ^ 4)
  calc
    _ ≤ ∫ z, R ^ 4 * |P.positiveComplexVorticity t z| := by
      apply integral_mono hi hj
      intro z
      by_cases hz : P.positiveComplexVorticity t z = 0
      · simp only [hz, abs_zero, mul_zero, le_refl]
      · have hb : ‖z‖ ≤ R := not_lt.mp (fun h => hz (P.positiveComplexVorticity_support ht h))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb 4) (abs_nonneg _)
    _ = _ := by rw [integral_const_mul, P.integral_abs_positiveComplexVorticity]; ring

theorem momentN_positiveComplexVorticity {t : ℝ} (ht : 0 ≤ t) :
    momentN (P.positiveComplexVorticity t) 4 = P.moment t := by
  rw [P.moment_positive t ht]
  have he := planarFourthMoment_complex_density (P.positiveComplexVorticity t)
  simpa only [positiveComplexVorticity, LinearIsometryEquiv.apply_symm_apply, momentN] using he.symm

theorem exists_nonzero_transfer_ratio :
    ∃ b ∈ Ioo (0 : ℝ) (1 / 4), bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 := by
  obtain ⟨b, hb, hF⟩ := exists_scale_ratio P.laplace (5 / 4 : ℝ)
  exact ⟨b, hb, by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hF⟩

theorem transfer_coefficient_ne_zero {b ρ : ℝ}
    (hF : bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0) (hρ : ρ ≠ 0) :
    (ρ : ℂ) ^ 6 * Kstar * bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hρ)) Kstar_ne_zero) hF

theorem exists_nonzero_retarded_time {b ρ : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hF : bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0) (hρ : ρ ≠ 0) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧
      retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment s₀ ≠ 0 := by
  have hK : (ρ : ℂ) ^ 6 * Kstar ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hρ)) Kstar_ne_zero
  have hLam : (sigma : ℂ) + ((-3 / 4 : ℝ) : ℂ) * I = lamStar := by
    unfold lamStar
    push_cast
    ring
  have hz : ((sigma : ℂ) + ((-3 / 4 : ℝ) : ℂ) * I) + (2 : ℂ) * I =
      (sigma : ℂ) + 5 / 4 * I := by
    push_cast
    ring
  have hzLam : lamStar + (2 : ℂ) * I = (sigma : ℂ) + 5 / 4 * I := by
    rw [← hLam]
    exact hz
  have hfreq : bilateral P.moment ((b : ℂ) *
      (((sigma : ℂ) + ((-3 / 4 : ℝ) : ℂ) * I) + (2 : ℝ) * I)) ≠ 0 := by
    simpa only [Complex.ofReal_ofNat, hz] using hF
  obtain ⟨s₀, hs₀, hne, _⟩ := survival P.laplace hK (2 : ℝ) hb.1 (by linarith [hb.2])
    hfreq (B := 0) (ε := 1 / 4) le_rfl (by norm_num)
  exact ⟨s₀, hs₀, by simpa only [Complex.ofReal_ofNat, hLam, hzLam] using hne⟩

end CircularMaterialTransferProfile

end Euler2D

end
