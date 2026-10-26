module

public import RequestProject.Euler.CircularFiniteRetardedForcingBudget
public import RequestProject.Euler.CircularFiniteActivePhysicalGauge

/-! A genuine same-S material trajectory has the full retarded
forcing budget in its original normalized rotating equation. The
forcing and the equation are both constructed from its actual source
and its true derivative; no error equation or forcing bound is an
input. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric Filter
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def finiteRetardedContourResponseBudget (η Ctorus b R ρ c B L δ Cb D e d : ℝ) (k : ℕ) : ℝ :=
  (interiorContourNormBudget η 1 c B L * (4 * Real.pi * circularRadialPerturbationWeight)) *
    (δ * (b * ρ ^ 2) / (1 - b * ρ ^ 2)) +
  (finiteLabelMassBound * cauchyContourNormBudget 5 η 1 e L) *
    Cb ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) +
  Ctorus * torusCorrectionContourBudget η L * d ^ 4 *
    circularFiniteL1Coefficient b ρ * R ^ 8 * (b * ρ ^ 2) ^ k

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualRetardedPhysical_derivative_budget :
    ∃ Ctorus : ℝ, 0 < Ctorus ∧ ∀ {s A₀ b R ρ q T c B L δ δ₀ Cb D e d : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
        (hsmall : ρ ^ 2 < b) (houter : b * ρ ^ 2 < 1)
        (hc : 0 < c) (hB : 0 < B) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
        (hCb : 0 ≤ Cb) (hD : 0 ≤ D) (he : 0 < e) (hd : 0 < d) (hd16 : d * R ≤ 1 / 16),
      ∀ (N k : ℕ) (hk : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x ∈ torusBox, d * R < ‖x - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0) →
      P.FiniteOuterMaterialTube s R ρ N (k - 1) S t c δ →
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ₀,
      Cb * ρ * radScale R ρ k * (1 + D) < 1 →
      (∀ x ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) →
      8 * B * ρ ≤ c → 8 * (Cb * ρ * (1 + D)) ≤ e →
      (L + 1) * radScale R ρ k ≤ (d * R) / 2 →
      ∀ W Qt V : Fin 2 → LittleContourSpace γ,
      W ∈ circularQuarterPhaseDomain hγ hγ1 →
      (∀ i, G.contours (⟨k, Nat.lt_succ_of_le hk⟩, i) = radScale R ρ k • (W i).val) →
      (∀ i x, ‖ContourC1Space.toBCF γ (W i).val x‖ ≤ B) →
      (∀ i x, e ≤ ‖ContourC1Space.toBCF γ (W i).val x‖) →
      ‖W‖ ≤ L →
      (∀ i θ, ∀ j : Fin k, ‖radScale R ρ k • LittleContourSpace.lift γ (W i) θ‖ ≤
        cellA * radScale R ρ j) →
      (∀ i θ, LittleContourSpace.lift γ (Qt i) θ =
        planeComplexEquiv (S.correctionLabelField t
          (complexTorusPoint (radScale R ρ k • LittleContourSpace.lift γ (W i) θ)))) →
      (∀ i θ, LittleContourSpace.lift γ (V i) θ =
        velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
          (radScale R ρ k • LittleContourSpace.lift γ (W i) θ) +
        planeComplexEquiv (S.correctionLabelField t
          (complexTorusPoint (radScale R ρ k • LittleContourSpace.lift γ (W i) θ)))) →
      ∀ z : ℝ → Fin 2 → LittleContourSpace γ, HasDerivAt z V t →
      z t = radScale R ρ k • W → ∀ entrance τ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t →
      let y := fun u => rigidRotationGauge (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) 0 u •
        normalizedPhysicalCurve (ampScale A₀ b k) (radScale R ρ k) entrance z u
      ∃ p : Fin 2 → LittleContourSpace γ,
        HasDerivAt y (circularBanachField hγ hγ1 (y τ) + p) τ ∧
        ‖p‖ ≤ finiteRetardedContourResponseBudget (γ : ℝ) Ctorus b R ρ c B L δ Cb D e d k := by
  obtain ⟨Ctorus, hCtorus, hbudget⟩ := P.exists_uniform_actualRetardedContourForcing_budget
  refine ⟨Ctorus, hCtorus, ?_⟩
  intro s A₀ b R ρ q T c B L δ δ₀ Cb D e d _ hs hA hb hR hRmax hρ hρ1 hq hqE
    hsmall houter hc hB hL hδ hCb hD he hd hd16 N k hk S hS t ht hsupp Ganc G
    ha1 hinner hsepOut hsepIn hgeom W Qt V hWdom hscale hWout hWin hWnorm hx hQt hV
    z hz hzt entrance τ htime
  have hr : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hden : 0 < ampScale A₀ b k * radScale R ρ k := mul_pos hAk hr
  let Budget := finiteRetardedContourResponseBudget (γ : ℝ) Ctorus b R ρ c B L δ Cb D e d k
  have hex : ∀ i : Fin 2, ∃ Qa Qi : LittleContourSpace γ,
      (∀ θ, LittleContourSpace.lift γ Qa θ =
        ∑ j : Fin k, velocityC
          (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (finiteAncestorIndex hk j) S t)
          (radScale R ρ k • LittleContourSpace.lift γ (W i) θ)) ∧
      (∀ θ, LittleContourSpace.lift γ Qi θ =
        velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
          (radScale R ρ k • LittleContourSpace.lift γ (W i) θ)) ∧
      ‖Qa + Qi + Qt i‖ / (ampScale A₀ b k * radScale R ρ k) ≤ Budget := by
    intro i
    have hW : ‖radScale R ρ k • W i‖ ≤ radScale R ρ k * L := by
      letI : NormSMulClass ℝ (LittleContourSpace γ) :=
        @NormedSpace.toNormSMulClass ℝ (LittleContourSpace γ) _ _
          (rigidGaugeLittle_space γ)
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm W i).trans hWnorm) hr.le
    have hwo (x : ContourCircle) :
        ‖ContourC1Space.toBCF γ (radScale R ρ k • W i).val x‖ ≤ B * radScale R ρ k := by
      change ‖radScale R ρ k • ContourC1Space.toBCF γ (W i).val x‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      nlinarith [mul_le_mul_of_nonneg_left (hWout i x) hr.le]
    have hwi (x : ContourCircle) :
        e * radScale R ρ k ≤ ‖ContourC1Space.toBCF γ (radScale R ρ k • W i).val x‖ := by
      change _ ≤ ‖radScale R ρ k • ContourC1Space.toBCF γ (W i).val x‖
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      nlinarith [mul_le_mul_of_nonneg_left (hWin i x) hr.le]
    obtain ⟨Qa, Qi, hQa, hQi, hn⟩ := hbudget hs hA hb hR hRmax hρ hρ1 hq hqE hsmall
      houter hc hB hL hδ hCb hD he hd hd16 N k hk S hS t ht hsupp Ganc ha1 hinner
      hsepOut hsepIn hgeom hγ1.le (radScale R ρ k • W i) (Qt i) hwo hwi hW (hQt i)
    exact ⟨Qa, Qi, hQa, hQi, hn⟩
  choose Qa Qi hQa hQi hnorm using hex
  have hBudget : 0 ≤ Budget :=
    (div_nonneg (norm_nonneg (Qa 0 + Qi 0 + Qt 0)) hden.le).trans (hnorm 0)
  have hsum : ‖Qa + Qi + Qt‖ / (ampScale A₀ b k * radScale R ρ k) ≤ Budget := by
    apply (div_le_iff₀ hden).mpr
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hBudget hden.le)).mpr
    intro i
    exact (div_le_iff₀ hden).mp (hnorm i)
  have hderiv := P.hasDerivAt_activePhysicalNormalizedRotatedCurve hs hA hb hR hRmax hρ hρ1
    N k hk S G.contours t ht W hWdom hscale
    (G.initial_box _ le_rfl) (G.current_box _ le_rfl) (G.images _ le_rfl) hx
    V Qa Qi Qt hV hQa hQi hQt z hz hzt entrance τ htime
  let p := rigidRotationGauge (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) 0 τ •
    ((ampScale A₀ b k * radScale R ρ k)⁻¹ • (Qa + Qi + Qt))
  refine ⟨p, hderiv.1, ?_⟩
  change ‖rigidRotationGauge _ 0 τ • ((ampScale A₀ b k * radScale R ρ k)⁻¹ • (Qa + Qi + Qt))‖ ≤ _
  rw [norm_normalizedPhysicalRotatedForcing hAk hr]
  exact hsum

end CircularMaterialTransferProfile
end Euler2D

end
