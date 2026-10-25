module

public import RequestProject.Euler.RadialProfileBounds
public import RequestProject.Euler.SmoothSobolev

/-!
# Sobolev regularity of the actual two-interface velocity

The forward-averaged radial velocities have a uniform pointwise first
 derivative bound on the actual fundamental square. Weak compactness of
those derivatives then proves Sobolev regularity of the nonsmooth
circular velocity itself.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

lemma W1pBoundedBy.congr_ae {q : ENNReal} {M : ℝ} {u v : R2 → R2}
    (hu : W1pBoundedBy q M u) (huv : u =ᵐ[μT] v) : W1pBoundedBy q M v := by
  obtain ⟨humem, hubound, G, hG, hGtest⟩ := hu
  refine ⟨(memLp_congr_ae huv).mp humem, ?_, G, hG, ?_⟩
  · rwa [← eLpNorm_congr_ae huv]
  · intro i j ψ hψ
    calc
      (∫ x in torusBox, v x j * pd i ψ x) = ∫ x in torusBox, u x j * pd i ψ x := by
        apply integral_congr_ae
        filter_upwards [huv] with x hx
        rw [hx]
      _ = -∫ x in torusBox, G i j x * ψ x := hGtest i j ψ hψ

lemma abs_sub_torusCenter_le_pi (x : R2) (hx : x ∈ torusBox) (i : Fin 2) :
    |(x - torusCenter) i| ≤ Real.pi := by
  change |x i - torusCenter i| ≤ _
  rw [torusCenter_apply, abs_le]
  constructor <;> linarith [(hx i).1, (hx i).2]

lemma norm_sub_torusCenter_le_six (x : R2) (hx : x ∈ torusBox) : ‖x - torusCenter‖ ≤ 6 := by
  have hcoord (i : Fin 2) : ‖(x - torusCenter) i‖ ^ 2 ≤ Real.pi ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) Real.pi_pos.le).mpr
    simpa only [Real.norm_eq_abs] using abs_sub_torusCenter_le_pi x hx i
  have hsq : ‖x - torusCenter‖ ^ 2 ≤ 2 * Real.pi ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    linarith [hcoord 0, hcoord 1]
  have hpisq : Real.pi ^ 2 < 16 := by
    have h := (sq_lt_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 4)).mpr Real.pi_lt_four
    norm_num at h ⊢
    exact h
  nlinarith [norm_nonneg (x - torusCenter)]

lemma norm_radialAverage_cellVelocity_le {ε : ℝ} (hε : 0 < ε)
    (x : R2) (hx : x ∈ torusBox) :
    ‖radialVelocity (profileAverage cellOmegaSq ε) torusCenter x‖ ≤ 3 := by
  unfold radialVelocity
  rw [norm_smul, norm_perpJ]
  calc
    ‖profileAverage cellOmegaSq ε (‖x - torusCenter‖ ^ 2)‖ * ‖x - torusCenter‖ ≤
        (1 / 2 : ℝ) * 6 :=
      mul_le_mul (norm_profileAverage_cellOmegaSq_le_half hε (sq_nonneg _))
        (norm_sub_torusCenter_le_six x hx) (norm_nonneg _) (by norm_num)
    _ = 3 := by norm_num

lemma norm_pd_radialAverage_cellVelocity_le {ε : ℝ} (hε : 0 < ε)
    (x : R2) (hx : x ∈ torusBox) (i : Fin 2) :
    ‖pd i (radialVelocity (profileAverage cellOmegaSq ε) torusCenter) x‖ ≤ 217 := by
  have hd := norm_deriv_profileAverage_cellOmegaSq_le_three hε (‖x - torusCenter‖ ^ 2)
  have hf := norm_profileAverage_cellOmegaSq_le_half hε (sq_nonneg ‖x - torusCenter‖)
  have hz := norm_sub_torusCenter_le_six x hx
  have hinner : |inner ℝ (x - torusCenter) (EuclideanSpace.single i 1)| ≤ 6 := by
    calc
      |inner ℝ (x - torusCenter) (EuclideanSpace.single i 1)| ≤
          ‖x - torusCenter‖ * ‖EuclideanSpace.single i 1‖ := abs_real_inner_le_norm _ _
      _ = ‖x - torusCenter‖ := by simp
      _ ≤ 6 := hz
  unfold pd
  rw [fderiv_radialVelocity_apply
    ((contDiff_profileAverage continuous_cellOmegaSq ε).differentiable one_ne_zero)]
  calc
    ‖(2 * deriv (profileAverage cellOmegaSq ε) (‖x - torusCenter‖ ^ 2) *
          inner ℝ (x - torusCenter) (EuclideanSpace.single i 1)) • perpJ (x - torusCenter) +
        profileAverage cellOmegaSq ε (‖x - torusCenter‖ ^ 2) • perpJ (EuclideanSpace.single i 1)‖ ≤
        ‖(2 * deriv (profileAverage cellOmegaSq ε) (‖x - torusCenter‖ ^ 2) *
          inner ℝ (x - torusCenter) (EuclideanSpace.single i 1)) • perpJ (x - torusCenter)‖ +
        ‖profileAverage cellOmegaSq ε (‖x - torusCenter‖ ^ 2) • perpJ (EuclideanSpace.single i 1)‖ :=
      norm_add_le _ _
    _ = (2 * ‖deriv (profileAverage cellOmegaSq ε) (‖x - torusCenter‖ ^ 2)‖ *
          |inner ℝ (x - torusCenter) (EuclideanSpace.single i 1)|) * ‖x - torusCenter‖ +
        ‖profileAverage cellOmegaSq ε (‖x - torusCenter‖ ^ 2)‖ := by
      rw [norm_smul, norm_smul, norm_perpJ, norm_perpJ]
      simp [norm_mul, Real.norm_eq_abs]
    _ ≤ (2 * 3 * 6) * 6 + (1 / 2 : ℝ) := by gcongr
    _ ≤ 217 := by norm_num

/-- A fixed explicit bound controls every genuine smooth radial
approximation, independently of the averaging scale. -/
theorem w1pBoundedBy_radialApproxLp_cell (q : ENNReal) (n : ℕ) :
    W1pBoundedBy q (torusSobolevBound q 256) (radialApproxLp cellOmegaSq continuous_cellOmegaSq n) := by
  have hε := radialApproxScale_pos n
  have hraw := w1pBoundedBy_of_C1_bounds
    (contDiff_radialVelocity (contDiff_profileAverage continuous_cellOmegaSq (radialApproxScale n))
      torusCenter)
    (radialVelocity_matchesTorusFaces (fun s hs =>
      profileAverage_eq_zero continuous_cellOmegaSq cellOmegaSq_eq_zero_of_one_le hε hs)) q
    (B := 256)
    (fun x hx => (norm_radialAverage_cellVelocity_le hε x hx).trans (by norm_num))
    (fun i j x hx => (abs_coord_le _ j).trans
      ((norm_pd_radialAverage_cellVelocity_le hε x hx i).trans (by norm_num)))
  exact hraw.congr_ae (radialApproxLp_ae cellOmegaSq continuous_cellOmegaSq n).symm

/-- The actual piecewise circular velocity retains the same explicit
Sobolev bound as its smooth approximations for every exponent at least two. -/
theorem w1pBoundedBy_centeredCellVelocityLp {q : ENNReal} (hq : 2 ≤ q) :
    W1pBoundedBy q (torusSobolevBound q 256) centeredCellVelocityLp :=
  w1pBoundedBy_of_tendsto hq
    (tendsto_radialApproxLp continuous_cellOmegaSq cellOmegaSq_eq_zero_of_one_le
      centeredCellVelocityLp_ae_radial) (w1pBoundedBy_radialApproxLp_cell q)

/-- The actual two-interface velocity belongs to all torus Sobolev
spaces in the project's original distributional sense, including `W¹,∞`. -/
theorem memW1p_centeredCellVelocityLp (q : ENNReal) : MemW1p q centeredCellVelocityLp := by
  by_cases hq : 2 ≤ q
  · exact (w1pBoundedBy_centeredCellVelocityLp hq).memW1p
  · exact (w1pBoundedBy_centeredCellVelocityLp (q := 2) le_rfl).memW1p.mono_exponent
      (le_of_lt (lt_of_not_ge hq))

end Euler2D

end
