module

public import RequestProject.Euler.TorusPeriodization
public import RequestProject.Euler.MomentVariation

/-!
# The actual fixed annular fourth-moment test

A genuine smooth bump in squared radius selects the inner interface.
Its lattice periodization is globally periodic, and agrees with the
specified coordinate formula throughout the physical fundamental square.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff ComplexConjugate symmDiff

namespace Euler2D

def annularSqBump (η : ℝ) (hη : 0 < η) : ContDiffBump (3 / 5 : ℝ) :=
  ⟨η, 2 * η, hη, by linarith⟩

def annularSqCutoff (η : ℝ) (hη : 0 < η) (s : ℝ) : ℝ := annularSqBump η hη s

lemma contDiff_annularSqCutoff (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ∞ (annularSqCutoff η hη) := (annularSqBump η hη).contDiff

lemma annularSqCutoff_eq_one {η s : ℝ} (hη : 0 < η) (hs : |s - 3 / 5| ≤ η) :
    annularSqCutoff η hη s = 1 := by
  apply (annularSqBump η hη).one_of_mem_closedBall
  simpa only [mem_closedBall, Real.dist_eq, annularSqBump] using hs

lemma annularSqCutoff_eq_zero {η s : ℝ} (hη : 0 < η) (hs : 2 * η ≤ |s - 3 / 5|) :
    annularSqCutoff η hη s = 0 := by
  apply (annularSqBump η hη).zero_of_le_dist
  simpa only [Real.dist_eq, annularSqBump] using hs

lemma annularSqCutoff_ne_zero {η s : ℝ} (hη : 0 < η)
    (hs : annularSqCutoff η hη s ≠ 0) : 3 / 5 - 2 * η < s ∧ s < 3 / 5 + 2 * η := by
  have hmem : s ∈ Function.support (annularSqBump η hη) := hs
  rw [(annularSqBump η hη).support_eq, mem_ball, Real.dist_eq] at hmem
  have h := abs_lt.mp hmem
  change -(2 * η) < s - 3 / 5 ∧ s - 3 / 5 < 2 * η at h
  constructor <;> linarith

def normalizedRadiusSq (R : ℝ) (x : R2) : ℝ := ‖x - torusCenter‖ ^ 2 / R ^ 2

def normalizedConjCoordinate (R : ℝ) (x : R2) : ℂ :=
  (((x 0 - torusCenter 0 : ℝ) : ℂ) - Complex.I * ((x 1 - torusCenter 1 : ℝ) : ℂ)) / (R : ℂ)

lemma contDiff_normalizedRadiusSq (R : ℝ) : ContDiff ℝ ∞ (normalizedRadiusSq R) :=
  ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).div_const _

lemma contDiff_normalizedConjCoordinate (R : ℝ) : ContDiff ℝ ∞ (normalizedConjCoordinate R) := by
  have h0 : ContDiff ℝ ∞ (fun x : R2 => ((x 0 - torusCenter 0 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj 0 : R2 →L[ℝ] ℝ).contDiff.sub contDiff_const)
  have h1 : ContDiff ℝ ∞ (fun x : R2 => ((x 1 - torusCenter 1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj 1 : R2 →L[ℝ] ℝ).contDiff.sub contDiff_const)
  exact (h0.sub (contDiff_const.mul h1)).div_const _

def rawAnnularDepartureTest (η : ℝ) (hη : 0 < η) (R : ℝ) (x : R2) : ℂ :=
  (annularSqCutoff η hη (normalizedRadiusSq R x) : ℂ) * normalizedConjCoordinate R x ^ 4

lemma contDiff_rawAnnularDepartureTest (η : ℝ) (hη : 0 < η) (R : ℝ) :
    ContDiff ℝ ∞ (rawAnnularDepartureTest η hη R) :=
  (Complex.ofRealCLM.contDiff.comp
    ((contDiff_annularSqCutoff η hη).comp (contDiff_normalizedRadiusSq R))).mul
      ((contDiff_normalizedConjCoordinate R).pow 4)

lemma rawAnnularDepartureTest_eq_zero_of_one_le_norm {η R : ℝ} (hη : 0 < η)
    (hηmax : η < 1 / 5) (hR : 0 < R) (hR1 : R ≤ 1) (x : R2)
    (hx : 1 ≤ ‖x - torusCenter‖) : rawAnnularDepartureTest η hη R x = 0 := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hs : 1 ≤ normalizedRadiusSq R x := by
    unfold normalizedRadiusSq
    apply (le_div_iff₀ hR2).mpr
    nlinarith [norm_nonneg (x - torusCenter)]
  have hdist : 2 * η ≤ |normalizedRadiusSq R x - 3 / 5| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [rawAnnularDepartureTest, annularSqCutoff_eq_zero hη hdist]
  simp

def annularDepartureTest (η : ℝ) (hη : 0 < η) (R : ℝ) : R2 → ℂ :=
  torusPeriodize (rawAnnularDepartureTest η hη R)

lemma contDiff_annularDepartureTest {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) : ContDiff ℝ ∞ (annularDepartureTest η hη R) :=
  contDiff_torusPeriodize (contDiff_rawAnnularDepartureTest η hη R)
    (rawAnnularDepartureTest_eq_zero_of_one_le_norm hη hηmax hR hR1)

lemma isTorusPeriodic_annularDepartureTest (η : ℝ) (hη : 0 < η) (R : ℝ) :
    IsTorusPeriodic (annularDepartureTest η hη R) :=
  isTorusPeriodic_torusPeriodize _

lemma annularDepartureTest_eq_raw_on_box {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) {x : R2} (hx : x ∈ torusBox) :
    annularDepartureTest η hη R x = rawAnnularDepartureTest η hη R x :=
  torusPeriodize_eq_on_box (rawAnnularDepartureTest_eq_zero_of_one_le_norm hη hηmax hR hR1) hx

lemma annularDepartureTest_eq_quartic {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) {x : R2} (hx : x ∈ torusBox)
    (hband : |normalizedRadiusSq R x - 3 / 5| ≤ η) :
    annularDepartureTest η hη R x = normalizedConjCoordinate R x ^ 4 := by
  rw [annularDepartureTest_eq_raw_on_box hη hηmax hR hR1 hx,
    rawAnnularDepartureTest, annularSqCutoff_eq_one hη hband]
  simp

lemma annularDepartureTest_eq_zero_on_box {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) {x : R2} (hx : x ∈ torusBox)
    (hband : 2 * η ≤ |normalizedRadiusSq R x - 3 / 5|) :
    annularDepartureTest η hη R x = 0 := by
  rw [annularDepartureTest_eq_raw_on_box hη hηmax hR hR1 hx,
    rawAnnularDepartureTest, annularSqCutoff_eq_zero hη hband]
  simp

theorem isScalarTest_annularDepartureTest_re {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) : IsScalarTest (fun x => (annularDepartureTest η hη R x).re) := by
  refine ⟨Complex.reCLM.contDiff.comp (contDiff_annularDepartureTest hη hηmax hR hR1), ?_⟩
  intro x i
  exact congrArg Complex.re (isTorusPeriodic_annularDepartureTest η hη R x i)

theorem isScalarTest_annularDepartureTest_im {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) : IsScalarTest (fun x => (annularDepartureTest η hη R x).im) := by
  refine ⟨Complex.imCLM.contDiff.comp (contDiff_annularDepartureTest hη hηmax hR hR1), ?_⟩
  intro x i
  exact congrArg Complex.im (isTorusPeriodic_annularDepartureTest η hη R x i)

/-- The physical Euclidean plane and the complex plane, with their actual
Lebesgue measures. -/
def planeComplexEquiv : R2 ≃ᵐ ℂ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans Complex.measurableEquivPi.symm

@[simp] lemma planeComplexEquiv_apply (x : R2) :
    planeComplexEquiv x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := rfl

lemma measurePreserving_planeComplexEquiv : MeasurePreserving planeComplexEquiv :=
  (MeasurePreserving.symm Complex.measurableEquivPi Complex.volume_preserving_equiv_pi).comp
    (PiLp.volume_preserving_ofLp (ι := Fin 2))

lemma norm_planeComplexEquiv (x : R2) : ‖planeComplexEquiv x‖ = ‖x‖ := by
  have hsq : ‖planeComplexEquiv x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Complex.sq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (planeComplexEquiv x), norm_nonneg x]

def normalizedComplexCoordinate (R : ℝ) (x : R2) : ℂ :=
  planeComplexEquiv (R⁻¹ • (x - torusCenter))

lemma normalizedConjCoordinate_eq_conj (R : ℝ) (x : R2) :
    normalizedConjCoordinate R x = conj (normalizedComplexCoordinate R x) := by
  unfold normalizedConjCoordinate normalizedComplexCoordinate
  simp [PiLp.smul_apply, PiLp.sub_apply, div_eq_mul_inv, map_add, map_mul]
  ring

lemma normalizedRadiusSq_eq_norm (R : ℝ) (x : R2) :
    normalizedRadiusSq R x = ‖normalizedComplexCoordinate R x‖ ^ 2 := by
  rw [normalizedComplexCoordinate, norm_planeComplexEquiv, norm_smul]
  simp only [normalizedRadiusSq, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, div_eq_mul_inv]
  ring

lemma integral_normalizedComplexCoordinate {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) :
    (∫ x : R2, g (normalizedComplexCoordinate R x)) = R ^ 2 • ∫ z : ℂ, g z := by
  unfold normalizedComplexCoordinate
  rw [integral_sub_right_eq_self (fun y : R2 => g (planeComplexEquiv (R⁻¹ • y))) torusCenter,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun y : R2 => g (planeComplexEquiv y)) hR.le]
  rw [measurePreserving_planeComplexEquiv.integral_comp' g]
  simp

lemma integrable_normalizedComplexCoordinate {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : Integrable g) : Integrable (fun x : R2 => g (normalizedComplexCoordinate R x)) := by
  have hp := measurePreserving_planeComplexEquiv.integrable_comp_of_integrable hg
  have hs := hp.comp_smul (inv_ne_zero hR.ne')
  exact (measurePreserving_sub_right volume torusCenter).integrable_comp_of_integrable hs

lemma integral_quartic_domain {R : ℝ} (hR : 0 < R) {D : Set ℂ} (hD : MeasurableSet D) :
    (∫ x : R2, normalizedConjCoordinate R x ^ 4 *
      ((D.indicator (fun _ => (1 : ℝ)) (normalizedComplexCoordinate R x) : ℝ) : ℂ)) =
        R ^ 2 • momentJ D 4 := by
  simp_rw [normalizedConjCoordinate_eq_conj]
  rw [integral_normalizedComplexCoordinate hR
    (fun z => conj z ^ 4 * ((D.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ))]
  congr 1
  rw [momentJ, ← integral_indicator hD]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ D <;> simp [hz]

lemma momentJ_ball_four (r : ℝ) (hr : 0 < r) : momentJ (ball (0 : ℂ) r) 4 = 0 := by
  have hD : starDomain (fun _ => r) = ball (0 : ℂ) r := by
    ext z
    simp [starDomain]
  rw [← hD, momentJ_starDomain continuous_const (fun _ => hr) 4]
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  change (∫ θ in Ioo (-Real.pi) Real.pi,
    Complex.exp (-(4 * (θ : ℂ) * Complex.I)) * ((r ^ 6 / 6 : ℝ) : ℂ)) = 0
  have harg (θ : ℝ) : -(4 * (θ : ℂ) * Complex.I) = (-4 * Complex.I) * θ := by ring
  simp_rw [harg]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_mul_const, integral_exp_mul_complex (by simp [Complex.ext_iff])]
  have hp : Complex.exp (-4 * Complex.I * Real.pi) = 1 := by
    rw [show -4 * Complex.I * (Real.pi : ℂ) = ((-2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hm : Complex.exp (-4 * Complex.I * ((-Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show -4 * Complex.I * ((-Real.pi : ℝ) : ℂ) = ((2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hp, hm]
  simp

def complexDomainIndicator (D : Set ℂ) (z : ℂ) : ℝ := D.indicator (fun _ => (1 : ℝ)) z

lemma complexDomainIndicator_ne_iff {D E : Set ℂ} {z : ℂ} :
    complexDomainIndicator D z ≠ complexDomainIndicator E z ↔ z ∈ D ∆ E := by
  by_cases hD : z ∈ D <;> by_cases hE : z ∈ E <;>
    simp [complexDomainIndicator, Set.mem_symmDiff, hD, hE]

def scaledInnerIndicatorDifference (R : ℝ) (D : Set ℂ) (x : R2) : ℝ :=
  complexDomainIndicator D (normalizedComplexCoordinate R x) -
    complexDomainIndicator (ball 0 cellA) (normalizedComplexCoordinate R x)

def physicalAnnularDifference (A R : ℝ) (D E : Set ℂ) (desc : R2 → ℝ) (x : R2) : ℝ :=
  A * ((5 / 2 : ℝ) * scaledInnerIndicatorDifference R D x -
    (3 / 2 : ℝ) * (complexDomainIndicator E (normalizedComplexCoordinate R x) -
      complexDomainIndicator (ball 0 1) (normalizedComplexCoordinate R x))) + desc x

lemma inner_band_subset_unitBall {η : ℝ} (hηmax : η < 1 / 5) {D : Set ℂ}
    (hinner : ∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ η) : D ⊆ ball 0 1 := by
  intro z hz
  by_cases hb : z ∈ ball (0 : ℂ) cellA
  · exact (ball_subset_ball cellA_lt_one.le) hb
  · have hs := hinner z (by simp [Set.mem_symmDiff, hz, hb])
    have hs' := (abs_le.mp hs).2
    rw [mem_ball_zero_iff]
    nlinarith [norm_nonneg z]

lemma scaledInnerIndicatorDifference_mem_box {η R : ℝ} (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) {D : Set ℂ}
    (hinner : ∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ η)
    {x : R2} (hx : scaledInnerIndicatorDifference R D x ≠ 0) : x ∈ torusBox := by
  have hz : normalizedComplexCoordinate R x ∈ D ∆ ball 0 cellA :=
    complexDomainIndicator_ne_iff.mp (sub_ne_zero.mp hx)
  have hs := hinner _ hz
  rw [← normalizedRadiusSq_eq_norm] at hs
  have hs' : normalizedRadiusSq R x < 1 := by linarith [(abs_le.mp hs).2]
  have hns : ‖x - torusCenter‖ ^ 2 < R ^ 2 :=
    (div_lt_one (sq_pos_of_pos hR)).mp hs'
  have hn : ‖x - torusCenter‖ < 1 := by nlinarith [norm_nonneg (x - torusCenter)]
  intro i
  have hc : |x i - Real.pi| < 1 := by
    simpa only [PiLp.sub_apply, torusCenter_apply] using (abs_coord_le _ i).trans_lt hn
  have hc' := abs_lt.mp hc
  constructor <;> linarith [Real.pi_gt_three]

lemma integrable_quartic_domain {R : ℝ} (hR : 0 < R) {D : Set ℂ} (hD : MeasurableSet D)
    (hDb : D ⊆ ball 0 1) :
    Integrable (fun x : R2 => normalizedConjCoordinate R x ^ 4 *
      ((complexDomainIndicator D (normalizedComplexCoordinate R x) : ℝ) : ℂ)) := by
  have hg : Integrable (fun z : ℂ => conj z ^ 4 * ((complexDomainIndicator D z : ℝ) : ℂ)) := by
    have hi : IntegrableOn (fun z : ℂ => conj z ^ 4) D :=
      ((Complex.continuous_conj.pow 4).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) 1)).mono_set (hDb.trans ball_subset_closedBall)
    have heq : (fun z : ℂ => conj z ^ 4 * ((complexDomainIndicator D z : ℝ) : ℂ)) =
        D.indicator (fun z => conj z ^ 4) := by
      funext z
      by_cases hz : z ∈ D <;> simp [complexDomainIndicator, hz]
    rw [heq]
    exact hi.integrable_indicator hD
  simpa only [normalizedConjCoordinate_eq_conj] using integrable_normalizedComplexCoordinate hR hg

lemma integral_quartic_inner_difference {η R : ℝ} (hηmax : η < 1 / 5) (hR : 0 < R)
    {D : Set ℂ} (hD : MeasurableSet D)
    (hinner : ∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ η) :
    (∫ x : R2, normalizedConjCoordinate R x ^ 4 *
      ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ)) = R ^ 2 • momentJ D 4 := by
  have hiD := integrable_quartic_domain hR hD (inner_band_subset_unitBall hηmax hinner)
  have hiB := integrable_quartic_domain hR measurableSet_ball (ball_subset_ball cellA_lt_one.le)
  have hDInt : (∫ x : R2, normalizedConjCoordinate R x ^ 4 *
      ((complexDomainIndicator D (normalizedComplexCoordinate R x) : ℝ) : ℂ)) =
        R ^ 2 • momentJ D 4 := integral_quartic_domain hR hD
  have hBInt : (∫ x : R2, normalizedConjCoordinate R x ^ 4 *
      ((complexDomainIndicator (ball 0 cellA) (normalizedComplexCoordinate R x) : ℝ) : ℂ)) =
        R ^ 2 • momentJ (ball 0 cellA) 4 := integral_quartic_domain hR measurableSet_ball
  simp_rw [scaledInnerIndicatorDifference, Complex.ofReal_sub, mul_sub]
  rw [integral_sub hiD hiB, hDInt, hBInt, momentJ_ball_four cellA cellA_pos]
  simp

/-- Outer-interface and descendant differences vanish against the real
fixed test by support separation; on the inner difference its cutoff is one. -/
lemma annularDepartureTest_pairing_pointwise {η R : ℝ} (hη : 0 < η) (hηmax : η < 1 / 5)
    (hR : 0 < R) (hR1 : R ≤ 1) (A : ℝ) {D E : Set ℂ} {desc : R2 → ℝ}
    (hinner : ∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ η)
    (houter : ∀ z ∈ E ∆ ball 0 1, 2 * η ≤ |‖z‖ ^ 2 - 3 / 5|)
    (hdesc : ∀ x ∈ torusBox, desc x ≠ 0 → 2 * η ≤ |normalizedRadiusSq R x - 3 / 5|)
    {x : R2} (hx : x ∈ torusBox) :
    annularDepartureTest η hη R x * ((physicalAnnularDifference A R D E desc x : ℝ) : ℂ) =
      ((5 / 2 * A : ℝ) : ℂ) * (normalizedConjCoordinate R x ^ 4 *
        ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ)) := by
  have hi : annularDepartureTest η hη R x *
      ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ) =
        normalizedConjCoordinate R x ^ 4 * ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ) := by
    by_cases hz : scaledInnerIndicatorDifference R D x = 0
    · simp [hz]
    · have hz' : normalizedComplexCoordinate R x ∈ D ∆ ball 0 cellA :=
        complexDomainIndicator_ne_iff.mp (sub_ne_zero.mp hz)
      have hs := hinner _ hz'
      rw [← normalizedRadiusSq_eq_norm] at hs
      rw [annularDepartureTest_eq_quartic hη hηmax hR hR1 hx hs]
  have ho : annularDepartureTest η hη R x *
      (((complexDomainIndicator E (normalizedComplexCoordinate R x) -
        complexDomainIndicator (ball 0 1) (normalizedComplexCoordinate R x)) : ℝ) : ℂ) = 0 := by
    by_cases hz : complexDomainIndicator E (normalizedComplexCoordinate R x) =
        complexDomainIndicator (ball 0 1) (normalizedComplexCoordinate R x)
    · simp [hz]
    · have hs := houter _ (complexDomainIndicator_ne_iff.mp hz)
      rw [← normalizedRadiusSq_eq_norm] at hs
      rw [annularDepartureTest_eq_zero_on_box hη hηmax hR hR1 hx hs, zero_mul]
  have hd : annularDepartureTest η hη R x * (desc x : ℂ) = 0 := by
    by_cases hz : desc x = 0
    · simp [hz]
    · rw [annularDepartureTest_eq_zero_on_box hη hηmax hR hR1 hx (hdesc x hx hz), zero_mul]
  calc
    _ = ((5 / 2 * A : ℝ) : ℂ) * (annularDepartureTest η hη R x *
          ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ)) -
        ((3 / 2 * A : ℝ) : ℂ) * (annularDepartureTest η hη R x *
          (((complexDomainIndicator E (normalizedComplexCoordinate R x) -
            complexDomainIndicator (ball 0 1) (normalizedComplexCoordinate R x)) : ℝ) : ℂ)) +
        annularDepartureTest η hη R x * (desc x : ℂ) := by
      unfold physicalAnnularDifference
      push_cast
      ring
    _ = _ := by rw [hi, ho, hd]; ring

/-- The actual total-vorticity pairing is exactly the physical area
factor times the fourth moment of the normalized inner domain. -/
theorem integral_annularDepartureTest_physical_difference {η R : ℝ}
    (hη : 0 < η) (hηmax : η < 1 / 5) (hR : 0 < R) (hR1 : R ≤ 1) (A : ℝ)
    {D E : Set ℂ} {desc : R2 → ℝ} (hD : MeasurableSet D)
    (hinner : ∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ η)
    (houter : ∀ z ∈ E ∆ ball 0 1, 2 * η ≤ |‖z‖ ^ 2 - 3 / 5|)
    (hdesc : ∀ x ∈ torusBox, desc x ≠ 0 → 2 * η ≤ |normalizedRadiusSq R x - 3 / 5|) :
    (∫ x in torusBox, annularDepartureTest η hη R x *
      ((physicalAnnularDifference A R D E desc x : ℝ) : ℂ)) =
        ((5 / 2 * A * R ^ 2 : ℝ) : ℂ) * momentJ D 4 := by
  calc
    _ = ∫ x in torusBox, ((5 / 2 * A : ℝ) : ℂ) * (normalizedConjCoordinate R x ^ 4 *
          ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_torusBox
      intro x hx
      exact annularDepartureTest_pairing_pointwise hη hηmax hR hR1 A hinner houter hdesc hx
    _ = ∫ x : R2, ((5 / 2 * A : ℝ) : ℂ) * (normalizedConjCoordinate R x ^ 4 *
          ((scaledInnerIndicatorDifference R D x : ℝ) : ℂ)) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hi : scaledInnerIndicatorDifference R D x = 0 := by
        by_contra hn
        exact hx (scaledInnerIndicatorDifference_mem_box hηmax hR hR1 hinner hn)
      simp [hi]
    _ = _ := by
      rw [integral_const_mul, integral_quartic_inner_difference hηmax hR hD hinner]
      simp only [Complex.real_smul]
      push_cast
      ring

theorem norm_integral_annularDepartureTest_physical_difference {η R A : ℝ}
    (hη : 0 < η) (hηmax : η < 1 / 5) (hR : 0 < R) (hR1 : R ≤ 1) (hA : 0 ≤ A)
    {D E : Set ℂ} {desc : R2 → ℝ} (hD : MeasurableSet D)
    (hinner : ∀ z ∈ D ∆ ball 0 cellA, |‖z‖ ^ 2 - 3 / 5| ≤ η)
    (houter : ∀ z ∈ E ∆ ball 0 1, 2 * η ≤ |‖z‖ ^ 2 - 3 / 5|)
    (hdesc : ∀ x ∈ torusBox, desc x ≠ 0 → 2 * η ≤ |normalizedRadiusSq R x - 3 / 5|) :
    ‖∫ x in torusBox, annularDepartureTest η hη R x *
      ((physicalAnnularDifference A R D E desc x : ℝ) : ℂ)‖ =
        (5 / 2 * A * R ^ 2) * ‖momentJ D 4‖ := by
  rw [integral_annularDepartureTest_physical_difference hη hηmax hR hR1 A hD hinner houter hdesc,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma support_rawAnnularDepartureTest_subset_annulus (η : ℝ) (hη : 0 < η) (R : ℝ) :
    Function.support (rawAnnularDepartureTest η hη R) ⊆
      {x | 3 / 5 - 2 * η < normalizedRadiusSq R x ∧
        normalizedRadiusSq R x < 3 / 5 + 2 * η} := by
  intro x hx
  have hc : annularSqCutoff η hη (normalizedRadiusSq R x) ≠ 0 := by
    intro hz
    apply hx
    simp [rawAnnularDepartureTest, hz]
  exact annularSqCutoff_ne_zero hη hc

lemma tsupport_rawAnnularDepartureTest_subset_annulus (η : ℝ) (hη : 0 < η) (R : ℝ) :
    tsupport (rawAnnularDepartureTest η hη R) ⊆ normalizedRadiusSq R ⁻¹'
      Icc (3 / 5 - 2 * η) (3 / 5 + 2 * η) := by
  apply closure_minimal
  · intro x hx
    have h := support_rawAnnularDepartureTest_subset_annulus η hη R hx
    exact ⟨h.1.le, h.2.le⟩
  · exact isClosed_Icc.preimage (contDiff_normalizedRadiusSq R).continuous

/-- The local test and its full closed support stay strictly inside the
fundamental square, with a positive margin at every face. -/
lemma tsupport_rawAnnularDepartureTest_subset_boxInterior {η R : ℝ}
    (hη : 0 < η) (hηmax : η < 1 / 5) (hR : 0 < R) (hR1 : R ≤ 1) :
    tsupport (rawAnnularDepartureTest η hη R) ⊆
      {x | ∀ i : Fin 2, 0 < x i ∧ x i < 2 * Real.pi} := by
  have hsupp : Function.support (rawAnnularDepartureTest η hη R) ⊆
      closedBall torusCenter 1 := by
    intro x hx
    have hn : ‖x - torusCenter‖ < 1 := by
      by_contra hn
      exact hx (rawAnnularDepartureTest_eq_zero_of_one_le_norm hη hηmax hR hR1 x
        (le_of_not_gt hn))
    simpa only [mem_closedBall, dist_eq_norm] using hn.le
  have hts := closure_minimal hsupp (isClosed_closedBall : IsClosed (closedBall torusCenter 1))
  intro x hx i
  have hn : ‖x - torusCenter‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hts hx
  have hc : |x i - Real.pi| ≤ 1 := by
    simpa only [PiLp.sub_apply, torusCenter_apply] using (abs_coord_le _ i).trans hn
  have hcc := abs_le.mp hc
  constructor <;> linarith [Real.pi_gt_three]

end Euler2D

end
