module

public import RequestProject.Euler.CircularFiniteTorusRadialCorrection
public import RequestProject.Euler.EulerStageRadialSupport

/-! The actual finite Euler particle radial feedback, with all
outer-label terms, true inner self-speed and the genuine periodic
correction filled. The geometry bundle contains only real material
contours, their tube distances and their actual domain images. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

structure FiniteOuterMaterialTube (s R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t c δ : ℝ) where
  contours : FiniteCircularIndex N → ContourC1Space γ
  reference : FiniteCircularIndex N → ContourC1Space γ
  shifts : FiniteCircularIndex N → ℝ
  reference_lift : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
    ContourC1Space.lift γ (reference (j, i)) = refCircle (circularContourRadii i * radScale R ρ j)
  quarter_tube : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
    ‖contourParameterShiftC1 (shifts (j, i)) (contours (j, i)) - reference (j, i)‖ ≤
      circularContourRadii i * radScale R ρ j / 4
  relative_tube : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
    ‖contourParameterShiftC1 (shifts (j, i)) (contours (j, i)) - reference (j, i)‖ ≤ radScale R ρ j * δ
  core : ∀ i, c ≤ 3 * circularContourRadii i / 4
  fourfold : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i θ,
    ContourC1Space.lift γ (contours (j, i)) (θ + Real.pi / 2) = I * ContourC1Space.lift γ (contours (j, i)) θ
  initial_box : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
    complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) ⊆ torusBox
  current_box : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
    complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (contours (j, i))) ⊆ torusBox
  images : ∀ j : Fin (N + 1), (j : ℕ) ≤ k → ∀ i,
    S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (contours (j, i)))

theorem exists_uniform_actualFiniteEuler_realRadial_feedback :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {s A₀ b R ρ q T c d δ : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (_hA : 0 < A₀) (_hb : 0 < b)
        (hR : 0 < R) (_hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (_hρ1 : ρ ≤ 1)
        (_hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (_hsmall : ρ ^ 2 < b) (_houter : b * ρ ^ 2 < 1)
        (_hc : 0 < c) (_hd : 0 < d) (_hd16 : d * R ≤ 1 / 16) (_hδ : 0 ≤ δ),
      ∀ N k : ℕ, k ≤ N → ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      (∀ y ∈ torusBox, d * R < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t y = 0) →
      P.FiniteOuterMaterialTube s R ρ N k S t c δ →
      ∀ x : ℂ, ‖x‖ ≤ c * radScale R ρ k / 2 → ‖x‖ ≤ d * R →
      inner ℝ (complexTorusPoint x - torusCenter)
        (particleVelocityRepresentative
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
          S.backward S.backward_area t (complexTorusPoint x)) ≤
        ‖x‖ * (C * ampScale A₀ b k * radScale R ρ k * (ρ / b) / (1 - ρ / b) +
          (((32 / (15 * c ^ 4) * circularRadialPerturbationWeight) * δ / (1 - b * ρ ^ 2) +
            K * d ^ 4 * circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ k) *
            (ampScale A₀ b k / radScale R ρ k ^ 2)) * ‖x‖ ^ 3) := by
  obtain ⟨C, hC, hplanar⟩ := P.exists_uniform_physicalFiniteDensity_planarRadial_feedback
  obtain ⟨K, hK, hcorr⟩ := P.exists_finiteEuler_uniformRadialCorrection_bound
  refine ⟨C, K, hC, hK, ?_⟩
  intro s A₀ b R ρ q T c d δ _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hsmall houter hc hd hd16 hδ
    N k hk S hS t ht hsupp G x hx hxchart
  have hp := hplanar hs hA.le hb hR hRmax hρ hρ1 hρb houter N k hk S
    G.contours G.reference G.shifts ht hc hδ G.reference_lift G.quarter_tube G.relative_tube G.core
    G.fourfold G.initial_box G.current_box G.images x hx
  have hq' := hcorr hs hA hb hR hRmax hρ hρ1 hq hqE hsmall hd hd16 N S hS t ht hsupp k x hxchart
  exact hq'.trans ((add_le_add hp le_rfl).trans_eq (by ring))

end CircularMaterialTransferProfile
end Euler2D

end
