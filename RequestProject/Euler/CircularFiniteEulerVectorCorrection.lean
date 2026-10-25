module

public import RequestProject.Euler.CircularFiniteTorusRadialCorrection
public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport
public import RequestProject.Euler.CircularFiniteUniformSupport

/-! The same actual torus correction has a full vector bound, rather
than only a radial bound. Normalization retains the cutoff-uniform
eighth-power factor and uses the conserved original L1 mass. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_uniform_actualEuler_correctionLabelField_cubic_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T),
      IsFourfoldBoundedEulerParticleSystem S → ∀ {w : R2 → ℝ} {a t : ℝ},
      w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ y, w (torusQuarterTurn y) = w y) → (∫ y in torusBox, f y) = 0 →
      0 < a → a ≤ 1 / 16 → t ∈ Icc (0 : ℝ) T →
      (∀ y ∈ torusBox, a < ‖y - torusCenter‖ → S.transportedScalar w t y = 0) →
      ∀ x : ℂ, ‖x‖ ≤ a →
        ‖S.correctionLabelField t (complexTorusPoint x)‖ ≤
          K * ‖x‖ ^ 3 * ∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y| := by
  obtain ⟨K, hK, hbound⟩ := actual_torusRemainderVelocity_cancellation (a := (1 / 16 : ℝ))
    (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro f T S hS w a t hwf hwper hwrot hm ha ha16 ht hsupp x hx
  have hs := S.physicalComplexSource_support hsupp
  have hs0 : ∀ y : ℂ, (1 / 16 : ℝ) < ‖y‖ → S.physicalComplexSource w t y = 0 :=
    fun y hy => hs y (ha16.trans_lt hy)
  have hsym := S.physicalComplexSource_fourfold hS hwper hwrot (by linarith) ht hsupp
  have hmass : (∫ y : ℂ, S.physicalComplexSource w t y) = 0 :=
    (S.integral_physicalComplexSource hwf t).trans hm
  have hn := hbound _ (S.integrable_physicalComplexSource hwf t) hs0 hsym hmass x (hx.trans ha16)
  change ‖actualTorusCorrectionVelocity (S.physicalComplexSource w t) x‖ ≤ _ at hn
  rw [S.actualTorusCorrectionVelocity_physicalComplexSource hwf ht] at hn
  simpa only [← complexPhysicalPlane_symm_eq_planeComplexEquiv, LinearIsometryEquiv.norm_map] using hn

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def normalizedCorrectionLabelVelocity (A r t θ : ℝ) (z : R2) : R2 :=
  planarRigidRotation (-θ) ((A * r)⁻¹ •
    S.correctionLabelField t (r • planarRigidRotation θ z + torusCenter))

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_normalizedCorrectionLabelVelocity_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {s A₀ b R ρ q T d : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      ρ ^ 2 < b → 0 < d → d * R ≤ 1 / 16 →
      ∀ N : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      (∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t y = 0) →
      ∀ k : ℕ, ∀ θ : ℝ, ∀ z : R2, radScale R ρ k * ‖z‖ ≤ d * R →
        ‖S.normalizedCorrectionLabelVelocity (ampScale A₀ b k) (radScale R ρ k) t θ z‖ ≤
          K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 *
            (b * ρ ^ 2) ^ k * ‖z‖ ^ 3 := by
  obtain ⟨K, hK, hcorrection⟩ := exists_uniform_actualEuler_correctionLabelField_cubic_bound
  refine ⟨K, hK, ?_⟩
  intro s A₀ b R ρ q T d _ hs hA hb hR hRmax hρ hρ1 hq hqE hsmall hd hdR N S hS t ht hsupp k θ z hz
  let w := P.finiteInitialPeriodicDensity s A₀ b R ρ N
  have hwf : w =ᵐ[μT] (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with y hy hybox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hybox).trans hy.symm
  have hm : (∫ y in torusBox, finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N y) = 0 :=
    (integral_congr_ae hwf).symm.trans
      (P.integral_finiteInitialPeriodicDensity_zero hs hR hRmax hρ hρ1 N)
  have hmass := S.physicalComplexSource_fourthAbsoluteMoment_le_initialL1 hwf hsupp
  have hf := P.integral_abs_finiteBaseCurlL2_le hs hA.le hb hR hρ hq hqE hsmall N
  rw [finiteBaseNormBound_one_eq] at hf
  have hfour : (∫ y : ℂ, ‖y‖ ^ 4 * |S.physicalComplexSource w t y|) ≤
      (d * R) ^ 4 * (circularFiniteL1Coefficient b ρ * (A₀ * R ^ 2)) :=
    hmass.trans (mul_le_mul_of_nonneg_left hf (by positivity))
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hAr : 0 < ampScale A₀ b k * radScale R ρ k := mul_pos hAk hrk
  let x := complexPhysicalPlane.symm (radScale R ρ k • planarRigidRotation θ z)
  have hxnorm : ‖x‖ = radScale R ρ k * ‖z‖ := by
    dsimp only [x]
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hrk,
      LinearIsometryEquiv.norm_map]
  have hxpoint : complexTorusPoint x = radScale R ρ k • planarRigidRotation θ z + torusCenter := by
    dsimp only [complexTorusPoint, x]
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hn := hcorrection S hS hwf
    (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
    (P.finiteInitialPeriodicDensity_quarterTurn hs N) hm (mul_pos hd hR) hdR ht hsupp x
    (by simpa only [hxnorm] using hz)
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hfour (by positivity))
  rw [hxpoint, hxnorm] at hn'
  rw [BoundedEulerParticleSystem.normalizedCorrectionLabelVelocity, LinearIsometryEquiv.norm_map,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hAr]
  refine (mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr hAr.le)).trans_eq ?_
  rw [mul_pow b (ρ ^ 2) k, show (ρ ^ 2) ^ k = (ρ ^ k) ^ 2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]]
  unfold ampScale radScale
  field_simp [hA.ne', hb.ne', hR.ne', hρ.ne']
  <;> ring

end CircularMaterialTransferProfile
end Euler2D

end
