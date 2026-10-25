module

public import RequestProject.Euler.ContourCauchyPrincipalValue

/-!
# Genuine weighted Cauchy principal values

The weighted truncated integral is decomposed on each genuine truncated
domain.  Every term is integrable there.  The actual integrable density
increment and the actual kernel principal value are then passed to the
limit separately.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace Euler2D

/-- A genuine weighted truncated singular integral in the relative parameter. -/
def symmetricWeightedTruncated (g f : ℝ → ℂ) (θ r ε : ℝ) : ℂ :=
  ∫ τ in symmetricContourTruncation r ε, g τ * f (θ + τ)

theorem integrableOn_symmetricWeightedTruncated {g f : ℝ → ℂ} {θ r ε : ℝ}
    (hε : 0 < ε)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r))
    (hinc : IntegrableOn (fun τ => g τ * (f (θ + τ) - f θ)) (Icc (-r) r)) :
    IntegrableOn (fun τ => g τ * f (θ + τ)) (symmetricContourTruncation r ε) := by
  have hi := (hinc.mono_set (symmetricContourTruncation_subset r ε)).add
    ((integrableOn_symmetricContourTruncation_of_integrable_remainder hε hR).mul_const (f θ))
  have heq : (fun τ => g τ * (f (θ + τ) - f θ)) + (fun τ => g τ * f θ) =
      fun τ => g τ * f (θ + τ) := by
    ext τ
    dsimp only [Pi.add_apply]
    ring
  rw [heq] at hi
  exact hi

/-- An exact decomposition of the genuine, integrable truncated weighted kernel. -/
theorem symmetricWeightedTruncated_eq {g f : ℝ → ℂ} {θ r ε : ℝ}
    (hε : 0 < ε)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r))
    (hinc : IntegrableOn (fun τ => g τ * (f (θ + τ) - f θ)) (Icc (-r) r)) :
    symmetricWeightedTruncated g f θ r ε =
      (∫ τ in symmetricContourTruncation r ε, g τ) * f θ +
        ∫ τ in symmetricContourTruncation r ε, g τ * (f (θ + τ) - f θ) := by
  have hg := integrableOn_symmetricContourTruncation_of_integrable_remainder hε hR
  have hi := hinc.mono_set (symmetricContourTruncation_subset r ε)
  have heq : (fun τ => g τ * f (θ + τ)) =
      (fun τ => g τ * f θ) + (fun τ => g τ * (f (θ + τ) - f θ)) := by
    ext τ
    dsimp only [Pi.add_apply]
    ring
  unfold symmetricWeightedTruncated
  rw [heq]
  change (∫ τ in symmetricContourTruncation r ε,
    g τ * f θ + g τ * (f (θ + τ) - f θ)) = _
  rw [integral_add (hg.mul_const (f θ)) hi, integral_mul_const]

/-- The true weighted principal value is its kernel PV times the base density plus the increment. -/
theorem tendsto_symmetricWeightedTruncated {g f : ℝ → ℂ} {θ r : ℝ}
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r))
    (hinc : IntegrableOn (fun τ => g τ * (f (θ + τ) - f θ)) (Icc (-r) r)) :
    Tendsto (symmetricWeightedTruncated g f θ r) (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ τ in Icc (-r) r, g τ + (τ : ℂ)⁻¹) * f θ +
        ∫ τ in Icc (-r) r, g τ * (f (θ + τ) - f θ))) := by
  have hlim := ((tendsto_principalValue_of_integrable_remainder hR).mul_const (f θ)).add
    (tendsto_integral_symmetricContourTruncation hinc)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (symmetricWeightedTruncated_eq hε hR hinc).symm

theorem tendsto_symmetricWeightedTruncated_filter
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} {g f : ℝ → ℂ} {θ r : ℝ}
    (hε : Tendsto ε l (𝓝 (0 : ℝ))) (hpos : ∀ᶠ i in l, 0 < ε i)
    (hR : IntegrableOn (fun τ => g τ + (τ : ℂ)⁻¹) (Icc (-r) r))
    (hinc : IntegrableOn (fun τ => g τ * (f (θ + τ) - f θ)) (Icc (-r) r)) :
    Tendsto (fun i => symmetricWeightedTruncated g f θ r (ε i)) l
      (𝓝 ((∫ τ in Icc (-r) r, g τ + (τ : ℂ)⁻¹) * f θ +
        ∫ τ in Icc (-r) r, g τ * (f (θ + τ) - f θ))) :=
  (tendsto_symmetricWeightedTruncated hR hinc).comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ε hε hpos)

/-- The literal weighted contour-kernel truncation. -/
def contourCauchyWeightedTruncated (z dz f : ℝ → ℂ) (θ r ε : ℝ) : ℂ :=
  symmetricWeightedTruncated (fun τ => dz (θ + τ) / (z θ - z (θ + τ))) f θ r ε

/-- Actual C¹ Hölder contours and actual Hölder densities have genuine weighted principal values. -/
theorem tendsto_contourC1CauchyWeightedTruncated {γ : ℝ≥0} (Z : ContourC1Space γ)
    (f : ContourHolderSpace γ) {c : ℝ} (hγ : 0 < (γ : ℝ)) (hc : 0 < c)
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤
      ‖ContourC1Space.lift γ Z θ - ContourC1Space.lift γ Z (θ + τ)‖) (θ : ℝ) :
    Tendsto (contourCauchyWeightedTruncated (ContourC1Space.lift γ Z)
      (deriv (ContourC1Space.lift γ Z)) (fun t : ℝ => f (t : ContourCircle)) θ Real.pi)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ τ in Icc (-Real.pi) Real.pi,
        contourCauchyPoleIntegrand (ContourC1Space.lift γ Z)
          (deriv (ContourC1Space.lift γ Z)) θ τ) * f (θ : ContourCircle) +
            contourC1CauchyIncrement Z f θ)) := by
  have hdz : Continuous (deriv (ContourC1Space.lift γ Z)) :=
    (contDiff_one_iff_deriv.mp (ContourC1Space.contDiff_lift Z)).2
  have hR := integrableOn_contourCauchyPoleIntegrand
    (ContourC1Space.contDiff_lift Z).continuous hdz hγ (norm_nonneg Z) hc Real.pi_pos.le
    (fun s => (ContourC1Space.hasDerivAt_lift Z s).differentiableAt.hasDerivAt)
    (norm_contourC1_deriv_lift_sub_le Z) hchord θ
  have hi := integrableOn_contourC1CauchyIncrementIntegrand Z f hγ hc
    (fun τ hτ => hchord θ τ (abs_le.mpr hτ))
  exact tendsto_symmetricWeightedTruncated hR hi

end Euler2D
