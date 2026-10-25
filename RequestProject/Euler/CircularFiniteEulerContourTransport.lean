module

public import RequestProject.Euler.CircularFiniteContourIdentification
public import RequestProject.Euler.CircularFiniteCommonActiveWindow
public import RequestProject.Euler.CircularFiniteQuarterEntrance

/-! Genuine material contours for the same finite torus Euler system.
The flow, its neighborhood, the active-particle estimate and the density
identification are all supplied by the previous constructions. The local
interval may depend on the finite cutoff. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) circularTransportLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularTransportLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularTransportC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_finiteEuler_localContourTransport {s A₀ b R ρ q T a : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρb : ρ < b)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (hT : 0 < T) (hRa : (5 / 4) * R < a) (ha16 : a ≤ 1 / 16)
    (hsize : R * max ‖P.ancient s‖ ‖littleCircularReference hγ hγ1‖ < a / 4)
    (N : ℕ)
    (hZ : IsAdmissibleLittleContourFamily
      (finiteCircularReferenceC1 hγ hγ1 R ρ : FiniteCircularIndex N → ContourC1Space γ)
      (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N))
    (hquarter : ∀ p : FiniteCircularIndex N,
      ‖(finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val -
        finiteCircularReferenceC1 hγ hγ1 R ρ p‖ < finiteCircularInterfaceRadius R ρ p / 4)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) :
    ∃ δ > 0, δ ≤ T ∧ ∃ Z : ℝ → FiniteCircularIndex N → ContourC1Space γ,
      Z 0 = (fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val) ∧
      (∀ p, ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) δ)) ∧
      ∃ hsmall : ∀ t ∈ Icc (0 : ℝ) δ, ∀ p,
          ‖Z t p - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ finiteCircularInterfaceRadius R ρ p / 4,
        (∀ t ∈ Icc (0 : ℝ) δ, ∀ p θ,
          HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
            (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
              planeComplexEquiv (S.correctionLabelField t
                (complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)))) t) ∧
        (∀ t ∈ Icc (0 : ℝ) δ, ∀ p θ,
          S.forward t (complexTorusPoint (ContourC1Space.lift γ (Z 0 p) θ)) =
            complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)) ∧
        ∀ t (ht : t ∈ Icc (0 : ℝ) δ), ∀ x ∈ torusBox,
          S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
            finiteContourC1PatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z t)
              (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
              (finiteCircularInterfaceRadius_pos hR hρ)
              (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (hsmall t ht)
              (centeredComplexHomeomorph.symm x) := by
  obtain ⟨ε, hε, hεT, hactive⟩ :=
    P.exists_common_finiteEuler_active_window hA hb hρ hρ1 hρb hT
  obtain ⟨D, hD, hDT, W, hW0, hWc, _hWmem, hWd⟩ :=
    P.exists_finiteEuler_localContourFlow hs hR hRmax hρ hρ1 hq hqE hT hRa ha16 hsize N hZ S hS
  obtain ⟨d, hd, hdD, hsmallW⟩ := exists_short_quarter_contour_interval W
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) hD hWc
    (by simpa only [hW0] using hquarter)
  let δ := min d ε
  have hδ : 0 < δ := lt_min hd hε
  have hδD : δ ≤ D := (min_le_left _ _).trans hdD
  have hδε : δ ≤ ε := min_le_right _ _
  have hδT : δ ≤ T := hδD.trans hDT
  have htD {t : ℝ} (ht : t ∈ Icc (0 : ℝ) δ) : t ∈ Icc (0 : ℝ) D :=
    ⟨ht.1, ht.2.trans hδD⟩
  let Z : ℝ → FiniteCircularIndex N → ContourC1Space γ := fun t p => (W t p).val
  have hZ0 : Z 0 = fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val := by
    change (fun p => (W 0 p).val) = _
    rw [hW0]
  have hZc (p : FiniteCircularIndex N) : ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) δ) := by
    have hWp : ContinuousOn (fun t => W t p) (Icc (0 : ℝ) δ) :=
      (continuous_apply p).comp_continuousOn (hWc.mono (fun _ ht => htD ht))
    exact (LittleContourSpace.inclusion γ).continuous.comp_continuousOn hWp
  have hsmall : ∀ t ∈ Icc (0 : ℝ) δ, ∀ p,
      ‖Z t p - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ finiteCircularInterfaceRadius R ρ p / 4 := by
    intro t ht p
    exact (hsmallW t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ p).le
  have hmat : ∀ t ∈ Icc (0 : ℝ) δ, ∀ p θ,
      HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
        (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)))) t := by
    intro t ht p θ
    exact hWd t (htD ht) p θ
  have hR6 : R ≤ 1 / 6 := by linarith
  have hactiveS := (hactive hs hq hqE hR hR6 N S).2.2
  have hagree := P.finiteEuler_contour_agreement hs hR hRmax hρ hρ1 hq hqE hδ.le hδT
    (by linarith : (5 / 4) * R < 1) N S Z hZ0 hsmall hZc hmat
    (fun t ht => hactiveS t ⟨ht.1, ht.2.trans hδε⟩)
  refine ⟨δ, hδ, hδT, Z, hZ0, hZc, hsmall, hmat, ?_, ?_⟩
  · intro t ht
    exact (hagree t ht).1
  · intro t ht
    exact (hagree t ht).2.2

end CircularMaterialTransferProfile
end Euler2D

end
