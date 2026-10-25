module

public import RequestProject.Euler.ContourDerivativePhase
public import RequestProject.Euler.ContourHolderInverseContinuity
public import RequestProject.Euler.ContourAdmissibility

/-!
# Hölder-norm continuity of the actual contour derivative phase

The phase is literally `conj Z' / Z'`.  Positive short-chord bounds give
the common positive lower derivative bound needed for genuine Hölder-norm
inversion.  Its value is independent of the chosen chord constant.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) contourPhase_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

variable {γ : ℝ≥0}

theorem contourDerivativePhase_eq_phaseOfNormLower (Z : ContourC1Space γ)
    {c : ℝ} (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z c) :
    contourDerivativePhase Z hc hZ =
      HolderFunctionSpace.phaseOfNormLower (ContourC1Space.derivative γ Z)
        hc (contourC1_derivative_norm_lower Z hZ) := rfl

theorem contourDerivativePhase_independent_lower (Z : ContourC1Space γ)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hZc : ContourC1Space.HasChordArcLower Z c)
    (hZd : ContourC1Space.HasChordArcLower Z d) :
    contourDerivativePhase Z hc hZc = contourDerivativePhase Z hd hZd := by
  apply HolderFunctionSpace.ext
  intro x
  rfl

/-- Actual contour convergence and a common chord lower bound imply
convergence of the literal derivative phases in the Hölder norm. -/
theorem tendsto_contourDerivativePhase {ι : Type*} {l : Filter ι}
    {u : ι → ContourC1Space γ} {Z : ContourC1Space γ} {c : ℝ}
    (hc : 0 < c) (hu : ∀ i, ContourC1Space.HasChordArcLower (u i) c)
    (hZ : ContourC1Space.HasChordArcLower Z c) (hlim : Tendsto u l (𝓝 Z)) :
    Tendsto (fun i => contourDerivativePhase (u i) hc (hu i)) l
      (𝓝 (contourDerivativePhase Z hc hZ)) := by
  have hd := ((ContourC1Space.derivative γ).continuous.tendsto Z).comp hlim
  exact HolderFunctionSpace.tendsto_phaseOfNormLower hc
    (fun i => contourC1_derivative_norm_lower (u i) (hu i))
    (contourC1_derivative_norm_lower Z hZ) hd

theorem continuous_contourDerivativePhase_of_chord {A : Type*} [TopologicalSpace A]
    (Z : A → ContourC1Space γ) (hZ : Continuous Z) {c : ℝ} (hc : 0 < c)
    (hchord : ∀ a, ContourC1Space.HasChordArcLower (Z a) c) :
    Continuous (fun a => contourDerivativePhase (Z a) hc (hchord a)) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact tendsto_contourDerivativePhase hc hchord (hchord a) (hZ.tendsto a)

/-- The actual open positive-chord locus. -/
abbrev PositiveChordContour (γ : ℝ≥0) :=
  {Z : ContourC1Space γ // ContourC1Space.HasPositiveChordArc Z}

def positiveChordConstant (Z : PositiveChordContour γ) : ℝ := Z.property.choose

theorem positiveChordConstant_pos (Z : PositiveChordContour γ) :
    0 < positiveChordConstant Z := Z.property.choose_spec.1

theorem hasChordArcLower_positiveChordConstant (Z : PositiveChordContour γ) :
    ContourC1Space.HasChordArcLower Z.val (positiveChordConstant Z) :=
  Z.property.choose_spec.2

/-- A canonical presentation of the genuine phase on the positive-chord
locus.  Changing the selected quantitative constant does not change it. -/
def positiveContourDerivativePhase (Z : PositiveChordContour γ) : ContourHolderSpace γ :=
  contourDerivativePhase Z.val (positiveChordConstant_pos Z)
    (hasChordArcLower_positiveChordConstant Z)

theorem positiveContourDerivativePhase_eq (Z : PositiveChordContour γ) {c : ℝ}
    (hc : 0 < c) (hZ : ContourC1Space.HasChordArcLower Z.val c) :
    positiveContourDerivativePhase Z = contourDerivativePhase Z.val hc hZ :=
  contourDerivativePhase_independent_lower Z.val (positiveChordConstant_pos Z) hc
    (hasChordArcLower_positiveChordConstant Z) hZ

/-- Continuity in the genuine Hölder norm, on the entire actual positive
chord locus; no globally uniform chord constant is assumed. -/
theorem continuous_positiveContourDerivativePhase (γ : ℝ≥0) :
    Continuous (positiveContourDerivativePhase (γ := γ)) := by
  apply continuous_iff_continuousAt.mpr
  intro Z
  let c := positiveChordConstant Z
  have hc : 0 < c := positiveChordConstant_pos Z
  have hZ : ContourC1Space.HasChordArcLower Z.val c :=
    hasChordArcLower_positiveChordConstant Z
  let S : Set (PositiveChordContour γ) :=
    {W | ‖W.val - Z.val‖ < c / 2}
  have hcommon (W : S) : ContourC1Space.HasChordArcLower W.val.val (c / 2) := by
    apply ContourC1Space.hasChordArcLower_of_mem_ball W.val.val Z.val hZ
    rw [Metric.mem_ball, @dist_eq_norm (ContourC1Space γ) inferInstance]
    exact W.property
  have hcont : Continuous (fun W : S =>
      contourDerivativePhase W.val.val (half_pos hc) (hcommon W)) :=
    continuous_contourDerivativePhase_of_chord (fun W : S => W.val.val)
      (continuous_subtype_val.comp continuous_subtype_val) (half_pos hc) hcommon
  have hrestrict : Continuous (S.restrict positiveContourDerivativePhase) := by
    apply hcont.congr
    intro W
    exact (positiveContourDerivativePhase_eq W.val (half_pos hc) (hcommon W)).symm
  have hSopen : IsOpen S :=
    isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const
  have hZS : Z ∈ S := by
    change ‖Z.val - Z.val‖ < c / 2
    simpa only [sub_self, norm_zero] using half_pos hc
  exact (continuousOn_iff_continuous_restrict.mpr hrestrict).continuousAt (hSopen.mem_nhds hZS)

end Euler2D

end
