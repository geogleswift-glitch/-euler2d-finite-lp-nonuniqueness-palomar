module

public import RequestProject.Euler.CircularFiniteCurrentFamilyForcing
public import RequestProject.Euler.CircularActualPrefixRotatedDerivative

/-! The current cell's actual derivative and genuine complete forcing
budget on its single stage clock, with one fixed entrance gauge. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCurrent_sameGauge_derivative_budget :
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧
      ∀ {s A₀ b R ρ c B δ e a L Cb D C₀ K Δ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < B → 0 < e →
      0 ≤ L → 0 ≤ Cb → 0 ≤ D → 1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 8 * B * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (γ : ℝ) c B L +
        Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      ∀ (N k : ℕ) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) →
      ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ x : ℕ → Fin 2 → LittleContourSpace γ,
      weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ v ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖v - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t v = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ e →
      ∀ W : Fin 2 → LittleContourSpace γ,
      W ∈ circularQuarterPhaseDomain hγ hγ1 →
      (∀ i, G.contours (⟨k, Nat.lt_succ_of_le hkN⟩, i) = radScale R ρ k • (W i).val) →
      (∀ i v, ‖ContourC1Space.toBCF γ (W i).val v‖ ≤ B) →
      (∀ i v, e ≤ ‖ContourC1Space.toBCF γ (W i).val v‖) → ‖W‖ ≤ L →
      (∀ i θ, ∀ j : Fin k,
        ‖radScale R ρ k • LittleContourSpace.lift γ (W i) θ‖ ≤ cellA * radScale R ρ j) →
      ∀ V : Fin 2 → LittleContourSpace γ,
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
        ‖p‖ ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 * ‖x k‖ +
          (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) e L Cb b Cd + Δ) * ρ ^ 6 * (1 + D) ^ 4 := by
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualCurrent_family_forcing_budget
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro s A₀ b R ρ c B δ e a L Cb D C₀ K Δ hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB he hL hCb hD hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN f T S hS hwf t ht G x hx hq hgeom hchart hsupp hsep
    W hWdom hscale hWmax hWmin hWL hpoint V hV z hz hzt entrance τ htime
  have hr : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hex (i : Fin 2) : ‖radScale R ρ k • W i‖ ≤ radScale R ρ k * L := by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm W i).trans hWL) hr.le
  have hmax (i : Fin 2) (v : ContourCircle) :
      ‖ContourC1Space.toBCF γ (radScale R ρ k • W i).val v‖ ≤ B * radScale R ρ k := by
    change ‖radScale R ρ k • ContourC1Space.toBCF γ (W i).val v‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith only [mul_le_mul_of_nonneg_left (hWmax i v) hr.le]
  have hmin (i : Fin 2) (v : ContourCircle) :
      e * radScale R ρ k ≤ ‖ContourC1Space.toBCF γ (radScale R ρ k • W i).val v‖ := by
    change _ ≤ ‖radScale R ρ k • ContourC1Space.toBCF γ (W i).val v‖
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith only [mul_le_mul_of_nonneg_left (hWmin i v) hr.le]
  obtain ⟨Q, hQ, hn⟩ := hsource hγ1.le hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB he hL hCb hD hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN S hS t ht G x hx hq hgeom hchart hsupp hsep
    (radScale R ρ k • W) hmax hmin hex
  have hd := P.hasDerivAt_actualPrefix_sameGauge_currentClock
    hs hA hb hR hRmax hρ hρ1 N k k le_rfl hkN S hwf G.contours t ht W hWdom hscale
    (G.initial_box _ le_rfl) (G.current_box _ le_rfl) (G.images _ le_rfl) hpoint
    V Q hV hQ z hz hzt entrance τ htime
  refine ⟨rigidRotationGauge (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) 0 τ •
    ((ampScale A₀ b k * radScale R ρ k)⁻¹ • Q), ?_, hd.2.trans_le hn⟩
  simpa only [Nat.sub_self, pow_zero, one_smul] using hd.1

end CircularMaterialTransferProfile
end Euler2D

end
