module

public import RequestProject.Euler.TorusCancellation
public import RequestProject.Euler.TorusGreenSymmetry
public import RequestProject.Euler.AnnularDepartureTest

/-!
# Cancellation for the Fourier-constructed torus correction

The coordinate map is the real linear isometry from the complex plane to
the genuine Euclidean physical plane.  We transfer the actual Laplacian,
the proved harmonicity of the constructed remainder, and its proved
quarter-turn symmetry before invoking the cancellation theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Metric Set Filter Topology
open scoped ContDiff
open Laplacian

namespace Euler2D

/-- The isometric real-coordinate realization of the complex plane. -/
def complexPhysicalPlane : ℂ ≃ₗᵢ[ℝ] R2 := Complex.orthonormalBasisOneI.repr

@[simp] lemma complexPhysicalPlane_apply (z : ℂ) :
    complexPhysicalPlane z = torusVec z.re z.im := by
  ext i
  fin_cases i <;> simp [complexPhysicalPlane, Complex.orthonormalBasisOneI_repr_apply, torusVec]

@[simp] lemma complexPhysicalPlane_one :
    complexPhysicalPlane 1 = EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [EuclideanSpace.single_apply, torusVec]

@[simp] lemma complexPhysicalPlane_I :
    complexPhysicalPlane I = EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [EuclideanSpace.single_apply, torusVec]

lemma complexPhysicalPlane_eq_planeComplexEquiv_symm (z : ℂ) :
    complexPhysicalPlane z = planeComplexEquiv.symm z := by
  apply planeComplexEquiv.injective
  simp [planeComplexEquiv_apply, torusVec, Complex.re_add_im]

lemma complexPhysicalPlane_mul_I (z : ℂ) :
    complexPhysicalPlane (I * z) = perpJ (complexPhysicalPlane z) := by
  ext i
  fin_cases i <;> simp [torusVec, perpJ]

/-- Physical coordinates centered at the actual pole of the Green kernel. -/
def complexTorusPoint (z : ℂ) : R2 := complexPhysicalPlane z + torusCenter

lemma complexTorusPoint_smooth : ContDiff ℝ ∞ complexTorusPoint :=
  complexPhysicalPlane.toContinuousLinearEquiv.contDiff.add contDiff_const

lemma norm_complexTorusPoint_sub_center (z : ℂ) :
    ‖complexTorusPoint z - torusCenter‖ = ‖z‖ := by
  simp only [complexTorusPoint, add_sub_cancel_right, LinearIsometryEquiv.norm_map]

lemma torusQuarterTurn_complexTorusPoint (z : ℂ) :
    torusQuarterTurn (complexTorusPoint z) = complexTorusPoint (I * z) := by
  unfold torusQuarterTurn complexTorusPoint
  rw [add_sub_cancel_right, complexPhysicalPlane_mul_I]
  exact add_comm _ _

/-- The intrinsic Laplacian is preserved by the actual real-plane coordinate
isometry.  This is proved with the two actual orthonormal bases. -/
theorem laplacian_comp_complexPhysicalPlane {f : R2 → ℝ}
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    Δ (f ∘ complexPhysicalPlane) z = Δ f (complexPhysicalPlane z) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  have hiter := complexPhysicalPlane.toLinearIsometry.toContinuousLinearMap.iteratedFDeriv_comp_right
    hf z (i := 2) (by norm_num)
  change iteratedFDeriv ℝ 2 (f ∘ complexPhysicalPlane) z = _ at hiter
  rw [hiter]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  have hOne : (fun i : Fin 2 => complexPhysicalPlane.toLinearIsometry.toContinuousLinearMap
      (![(1 : ℂ), 1] i)) =
      ![(EuclideanSpace.single 0 1 : R2), EuclideanSpace.single 0 1] := by
    funext i
    fin_cases i <;> exact complexPhysicalPlane_one
  have hI : (fun i : Fin 2 => complexPhysicalPlane.toLinearIsometry.toContinuousLinearMap
      (![I, I] i)) =
      ![(EuclideanSpace.single 1 1 : R2), EuclideanSpace.single 1 1] := by
    funext i
    fin_cases i <;> exact complexPhysicalPlane_I
  simp only [Fin.sum_univ_two, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    EuclideanSpace.basisFun_apply, hOne, hI]
  rfl

theorem laplacian_comp_add_right_physical (f : R2 → ℝ) (c x : R2) :
    Δ (fun y => f (y + c)) x = Δ f (x + c) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin 2) ℝ), iteratedFDeriv_comp_add_right]

theorem laplacian_comp_complexTorusPoint {f : R2 → ℝ}
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    Δ (f ∘ complexTorusPoint) z = Δ f (complexTorusPoint z) := by
  change Δ ((fun y => f (y + torusCenter)) ∘ complexPhysicalPlane) z = _
  have htrans : ContDiff ℝ 2 (fun y => f (y + torusCenter)) :=
    hf.comp (contDiff_id.add contDiff_const)
  calc
    _ = Δ (fun y => f (y + torusCenter)) (complexPhysicalPlane z) :=
      laplacian_comp_complexPhysicalPlane htrans z
    _ = Δ f (complexPhysicalPlane z + torusCenter) :=
      laplacian_comp_add_right_physical f torusCenter _
    _ = _ := rfl

/-- Coordinate harmonicity for a genuine globally `C²` physical function. -/
theorem harmonicOnNhd_comp_complexTorusPoint {f : R2 → ℝ} {r : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hh : InnerProductSpace.HarmonicOnNhd f (ball torusCenter r)) :
    InnerProductSpace.HarmonicOnNhd (f ∘ complexTorusPoint) (ball 0 r) := by
  intro z hz
  have hp : complexTorusPoint z ∈ ball torusCenter r := by
    simpa only [mem_ball, dist_eq_norm, norm_complexTorusPoint_sub_center,
      sub_zero] using hz
  refine ⟨(hf.comp (complexTorusPoint_smooth.of_le (by decide))).contDiffAt, ?_⟩
  have hlim : Tendsto complexTorusPoint (𝓝 z) (𝓝 (complexTorusPoint z)) :=
    complexTorusPoint_smooth.continuous.continuousAt
  filter_upwards [hlim.eventually (hh _ hp).2] with y hy
  change Δ (f ∘ complexTorusPoint) y = 0
  rw [laplacian_comp_complexTorusPoint hf]
  exact hy

/-- The actual constructed harmonic remainder in centered complex coordinates. -/
def actualComplexHarmonicRemainder : ℂ → ℝ :=
  torusGreenHarmonicRemainder ∘ complexTorusPoint

theorem harmonicOnNhd_actualComplexHarmonicRemainder :
    InnerProductSpace.HarmonicOnNhd actualComplexHarmonicRemainder (ball 0 (1 / 2)) :=
  harmonicOnNhd_comp_complexTorusPoint
    (torusGreenHarmonicRemainder_smooth.of_le (by decide))
    harmonicOnNhd_torusGreenHarmonicRemainder

theorem actualComplexHarmonicRemainder_fourfold (z : ℂ) :
    actualComplexHarmonicRemainder (I * z) = actualComplexHarmonicRemainder z := by
  change torusGreenHarmonicRemainder (complexTorusPoint (I * z)) = _
  rw [← torusQuarterTurn_complexTorusPoint, torusGreenHarmonicRemainder_quarterTurn]
  rfl

/-- The smooth correction of the actual Fourier-constructed Green kernel,
in the centered complex coordinates used by the cancellation estimate. -/
def actualComplexGreenCorrection : ℂ → ℝ := torusGreenCorrection ∘ complexTorusPoint

lemma torusGreenQuadratic_complexTorusPoint (z : ℂ) :
    torusGreenQuadratic (complexTorusPoint z) = ‖z‖ ^ 2 / (4 * (2 * Real.pi) ^ 2) := by
  simp only [torusGreenQuadratic, norm_complexTorusPoint_sub_center]

lemma actualComplexGreenCorrection_eq_quadratic_add_harmonic (z : ℂ) :
    actualComplexGreenCorrection z =
      -((4 * (2 * Real.pi) ^ 2)⁻¹) * ‖z‖ ^ 2 + actualComplexHarmonicRemainder z := by
  change torusGreenCorrection (complexTorusPoint z) =
    -((4 * (2 * Real.pi) ^ 2)⁻¹) * ‖z‖ ^ 2 +
      (torusGreenCorrection (complexTorusPoint z) + torusGreenQuadratic (complexTorusPoint z))
  rw [torusGreenQuadratic_complexTorusPoint]
  simp only [div_eq_mul_inv]
  ring

/-- Cubic cancellation for the actual constructed torus correction.
All harmonic and symmetry properties have been proved for this concrete
kernel, and the constant is strictly positive. -/
theorem actual_torusGreenCorrection_cancellation {a : ℝ}
    (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ K : ℝ, 0 < K ∧ ∀ ζ : ℂ → ℝ, Integrable ζ →
      (∀ y, a < ‖y‖ → ζ y = 0) → (∀ y, ζ (I * y) = ζ y) →
      (∫ y, ζ y) = 0 → ∀ x : ℂ, ‖x‖ ≤ a →
        ‖fderiv ℝ (fun x => ∫ y, actualComplexGreenCorrection (x - y) * ζ y) x‖ ≤
          K * ‖x‖ ^ 3 * ∫ y, ‖y‖ ^ 4 * |ζ y| := by
  have hh : InnerProductSpace.HarmonicOnNhd actualComplexHarmonicRemainder (ball 0 (8 * a)) :=
    harmonicOnNhd_actualComplexHarmonicRemainder.mono (by
      intro z hz
      rw [mem_ball_zero_iff] at hz ⊢
      exact hz.trans_le (by linarith))
  obtain ⟨K, hK⟩ := periodic_remainder_cancellation (-((4 * (2 * Real.pi) ^ 2)⁻¹)) ha hh
    (fun z _ => actualComplexHarmonicRemainder_fourfold z)
  refine ⟨|K| + 1, by positivity, fun ζ hζ hsupp hsym hmass x hx => ?_⟩
  have hbound := hK ζ hζ hsupp hsym hmass x hx
  simp_rw [← actualComplexGreenCorrection_eq_quadratic_add_harmonic] at hbound
  apply hbound.trans
  have hweight : 0 ≤ ∫ y, ‖y‖ ^ 4 * |ζ y| :=
    integral_nonneg (fun y => mul_nonneg (pow_nonneg (norm_nonneg _) _) (abs_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((le_abs_self K).trans (by linarith [abs_nonneg K]))
      (pow_nonneg (norm_nonneg _) _)) hweight

end Euler2D

end
