module

public import RequestProject.Euler.ContourDerivativePhaseContinuity
public import RequestProject.Euler.LittleContourSpace

/-!
# Genuine smooth approximation with a uniform positive chord bound

The approximants are selected from the actual smooth-loop subspace whose
closure defines the little Hölder space.  Their errors are bounded by
`min (c/2) (1/(n+1))`, so every approximant has chord constant `c/2`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D.LittleContourSpace

local instance (priority := 2000) smoothApprox_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) smoothApprox_c1NormedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

variable {γ : ℝ≥0}

/-- An actual sequence of smooth periodic little contours, with a common
positive short-chord lower bound, converges in the genuine little norm. -/
theorem exists_smooth_chord_approximation (Z : LittleContourSpace γ) {c : ℝ}
    (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z.val c) :
    ∃ u : ℕ → LittleContourSpace γ,
      (∀ n, ContDiff ℝ ∞ (lift γ (u n))) ∧
      (∀ n, ContourC1Space.HasChordArcLower (u n).val (c / 2)) ∧
      (∀ n, ‖u n - Z‖ < min (c / 2) (1 / ((n : ℝ) + 1))) ∧
      Tendsto u atTop (𝓝 Z) := by
  have happrox (n : ℕ) : ∃ g : ContourC1Space γ,
      ContDiff ℝ ∞ (ContourC1Space.lift γ g) ∧
      ‖Z.val - g‖ < min (c / 2) (1 / ((n : ℝ) + 1)) :=
    exists_smooth_approximation Z (lt_min (half_pos hc) (by positivity))
  choose u hs hu using happrox
  let v : ℕ → LittleContourSpace γ := fun n => ofSmooth γ (u n) (hs n)
  have herr (n : ℕ) : ‖v n - Z‖ < min (c / 2) (1 / ((n : ℝ) + 1)) := by
    change ‖u n - Z.val‖ < _
    rw [norm_sub_rev]
    exact hu n
  have hchord (n : ℕ) : ContourC1Space.HasChordArcLower (v n).val (c / 2) := by
    apply ContourC1Space.hasChordArcLower_of_mem_ball (v n).val Z.val hZ
    rw [Metric.mem_ball, @dist_eq_norm (ContourC1Space γ) inferInstance]
    exact (herr n).trans_le (min_le_left _ _)
  have hlim : Tendsto v atTop (𝓝 Z) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (herr n).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨v, hs, hchord, herr, hlim⟩

/-- The actual smooth approximation also converges after applying the
literal phase `conj Z'/Z'` in the Hölder norm.  Every open norm ball
containing the limit eventually contains the same approximants. -/
theorem exists_smooth_chord_phase_approximation (Z : LittleContourSpace γ) {c : ℝ}
    (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z.val c) :
    ∃ u : ℕ → LittleContourSpace γ,
      (∀ n, ContDiff ℝ ∞ (lift γ (u n))) ∧
      ∃ hu : ∀ n, ContourC1Space.HasChordArcLower (u n).val (c / 2),
        Tendsto u atTop (𝓝 Z) ∧
        Tendsto (fun n => contourDerivativePhase (u n).val (half_pos hc) (hu n))
          atTop (𝓝 (contourDerivativePhase Z.val hc hZ)) ∧
        ∀ (reference : LittleContourSpace γ) (ρ : ℝ), Z ∈ ball reference ρ →
          ∀ᶠ n in atTop, u n ∈ ball reference ρ := by
  obtain ⟨u, hs, hu, _, hlim⟩ := exists_smooth_chord_approximation Z hc hZ
  have hZhalf : ContourC1Space.HasChordArcLower Z.val (c / 2) :=
    ContourC1Space.hasChordArcLower_mono Z.val hZ (by linarith)
  have hval : Tendsto (fun n => (u n).val) atTop (𝓝 Z.val) :=
    ((inclusion γ).continuous.tendsto Z).comp hlim
  have hp := tendsto_contourDerivativePhase (half_pos hc) hu hZhalf hval
  rw [contourDerivativePhase_independent_lower Z.val (half_pos hc) hc hZhalf hZ] at hp
  refine ⟨u, hs, hu, hlim, hp, ?_⟩
  intro reference ρ hball
  exact hlim (isOpen_ball.mem_nhds hball)

end Euler2D.LittleContourSpace

end
