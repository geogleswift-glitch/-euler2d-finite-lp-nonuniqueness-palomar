module

public import RequestProject.Euler.ClusterContourForcing

/-! Uniform physical scale bounds in the actual contour norm.
The full field has the sixth-power scale ratio; after subtracting
its true fourth moment, the remainder has the tenth-power ratio. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory
open scoped NNReal

namespace Euler2D

def cauchySpatialDerivativeBudget (p : ℕ) (M d : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (8 / (15 * Real.pi) * M / (d / 2) ^ p) / (d / 2) ^ m

def cauchyContourNormBudget (p : ℕ) (γ M d L : ℝ) : ℝ :=
  max (cauchySpatialDerivativeBudget p M d 0)
    (2 * (cauchySpatialDerivativeBudget p M d 1 + Real.pi ^ (1 - γ) *
      cauchySpatialDerivativeBudget p M d 2 * L) * L)

theorem cauchySpatialDerivativeBudget_nonneg (p : ℕ) {M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (m : ℕ) : 0 ≤ cauchySpatialDerivativeBudget p M d m := by
  unfold cauchySpatialDerivativeBudget
  positivity

theorem cauchyContourNormBudget_mono_length (p : ℕ) (γ : ℝ) {M d L K : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hL : 0 ≤ L) (hLK : L ≤ K) :
    cauchyContourNormBudget p γ M d L ≤ cauchyContourNormBudget p γ M d K := by
  have h₁ := cauchySpatialDerivativeBudget_nonneg p hM hd 1
  have h₂ := cauchySpatialDerivativeBudget_nonneg p hM hd 2
  have hK : 0 ≤ K := hL.trans hLK
  unfold cauchyContourNormBudget
  apply max_le_max le_rfl
  gcongr <;> positivity

theorem cauchyContourNormBudget_physical_scale (p : ℕ) (γ : ℝ) {M R d : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hd : 0 < d) (L : ℝ) :
    cauchyContourNormBudget p γ M (R * d) (R * L) =
      (M / R ^ p) * cauchyContourNormBudget p γ 1 d L := by
  have hfac : 0 ≤ M / R ^ p := by positivity
  unfold cauchyContourNormBudget
  rw [mul_max_of_nonneg _ _ hfac]
  apply congrArg₂ max
  · unfold cauchySpatialDerivativeBudget
    norm_num only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, div_one, mul_pow, div_pow]
    field_simp [hR.ne', hd.ne']
  · unfold cauchySpatialDerivativeBudget
    norm_num only [Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
      pow_one, one_mul, mul_pow, div_pow]
    field_simp [hR.ne', hd.ne']

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
  (P : CircularMaterialTransferProfile hγ hγ1)

/-- The actual full physical field has the paper's sixth-power
normalized interaction scale in the original C¹γ contour norm. -/
theorem exists_physical_scaled_contour_fieldC1_ratio {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    (t A : ℝ) {r R c L : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 < c)
    (hsep : 4 * r * P.physicalSupportRadius t ≤ c * R)
    (Z : ContourC1Space η) (hZ : ∀ x, c * R ≤ ‖ContourC1Space.toBCF η Z x‖)
    (hL : ‖Z‖ ≤ R * L) :
    ∃ Q : ContourC1Space η,
      (∀ θ, ContourC1Space.lift η Q θ =
        velocityC (scaledComplexDensity A r (P.physicalVorticity t)) (ContourC1Space.lift η Z θ)) ∧
      ‖Q‖ / R ≤
        (finiteContourPatchMassBound circularContourStrengths circularContourRadii *
          cauchyContourNormBudget 5 (η : ℝ) 1 c L) * |A| * (r / R) ^ 6 * P.physicalSupportRadius t ^ 4 := by
  obtain ⟨Q, hQ, hnorm⟩ := P.exists_physical_scaled_contour_fieldC1 hη t A hr (mul_pos hc hR) hsep Z hZ
  have hM : 0 ≤ P.physicalClusterMomentBudget t A r :=
    (integral_nonneg (fun z => by positivity)).trans (P.physicalClusterMomentBudget_bounds t A hr)
  change ‖Q‖ ≤ cauchyContourNormBudget 5 (η : ℝ) (P.physicalClusterMomentBudget t A r) (c * R) ‖Z‖ at hnorm
  have hbound := hnorm.trans (cauchyContourNormBudget_mono_length 5 (η : ℝ) hM
    (mul_pos hc hR) (norm_nonneg Z) hL)
  rw [mul_comm c R, cauchyContourNormBudget_physical_scale 5 (η : ℝ) hM hR hc L] at hbound
  refine ⟨Q, hQ, (div_le_div_of_nonneg_right hbound hR.le).trans_eq ?_⟩
  unfold physicalClusterMomentBudget
  field_simp [hR.ne']

/-- The actual field minus its exact N(t) fourth-moment term has
the tenth-power normalized scale in the original C¹γ contour norm. -/
theorem exists_physical_scaled_contour_remainderC1_ratio {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    (t A : ℝ) {r R c L : ℝ} (hr : 0 < r) (hR : 0 < R) (hc : 0 < c)
    (hsep : 4 * r * P.physicalSupportRadius t ≤ c * R)
    (Z : ContourC1Space η) (hZ : ∀ x, c * R ≤ ‖ContourC1Space.toBCF η Z x‖)
    (hL : ‖Z‖ ≤ R * L) :
    ∃ Q : ContourC1Space η,
      (∀ θ, ContourC1Space.lift η Q θ =
        velocityC (scaledComplexDensity A r (P.physicalVorticity t)) (ContourC1Space.lift η Z θ) -
          I / (2 * Real.pi) * ((A : ℂ) * (r : ℂ) ^ 6 * P.moment t) *
            (conj (ContourC1Space.lift η Z θ) ^ 5)⁻¹) ∧
      ‖Q‖ / R ≤
        (finiteContourPatchMassBound circularContourStrengths circularContourRadii *
          cauchyContourNormBudget 9 (η : ℝ) 1 c L) * |A| * (r / R) ^ 10 * P.physicalSupportRadius t ^ 8 := by
  obtain ⟨Q, hQ, hnorm⟩ := P.exists_physical_scaled_contour_remainderC1 hη t A hr (mul_pos hc hR) hsep Z hZ
  have hM : 0 ≤ P.physicalForcingMomentBudget t A r :=
    (integral_nonneg (fun z => by positivity)).trans (P.physicalForcingMomentBudget_bounds t A hr)
  change ‖Q‖ ≤ cauchyContourNormBudget 9 (η : ℝ) (P.physicalForcingMomentBudget t A r) (c * R) ‖Z‖ at hnorm
  have hbound := hnorm.trans (cauchyContourNormBudget_mono_length 9 (η : ℝ) hM
    (mul_pos hc hR) (norm_nonneg Z) hL)
  rw [mul_comm c R, cauchyContourNormBudget_physical_scale 9 (η : ℝ) hM hR hc L] at hbound
  refine ⟨Q, hQ, (div_le_div_of_nonneg_right hbound hR.le).trans_eq ?_⟩
  unfold physicalForcingMomentBudget
  field_simp [hR.ne']

end CircularMaterialTransferProfile

end Euler2D

end
