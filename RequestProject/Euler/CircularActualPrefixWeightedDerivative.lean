module

public import RequestProject.Euler.CircularFinitePrefixWeightedFamilyForcing
public import RequestProject.Euler.CircularActualPrefixRotatedDerivative

/-! The same actual material path satisfies the original isolated
circular equation plus its complete, quantitatively constructed
weighted forcing, on one fixed entrance gauge and current clock. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)
theorem exists_uniform_actualPrefix_sameGauge_weighted_derivative :
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧
      ∀ {s A₀ b R ρ c B δ e a L Cb D C₀ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 < b →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < B → 0 < e →
      0 ≤ L → 0 ≤ Cb → 0 ≤ D → 1 < C₀ → C₀ * ρ ^ 8 < 1 →
      ∀ (N k : ℕ) (j : Fin k) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ x : ℕ → Fin 2 → LittleContourSpace γ,
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (∀ l : Fin (k + 1), (j : ℕ) < l → 10 * radScale R ρ l ≤ e * radScale R ρ j) →
      (∀ l : Fin (k + 1), (l : ℕ) < j → 8 * (B * radScale R ρ j) ≤ c * radScale R ρ l) →
      (∀ l : Fin (k + 1), (5 / 4 : ℝ) * radScale R ρ l ≤ a) →
      (L + 1) * radScale R ρ j ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ z ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖z - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t z = 0) →
      8 * (Cb * ρ * radScale R ρ k * (1 + D)) ≤ e * radScale R ρ j →
      ∀ V : Fin 2 → LittleContourSpace γ,
      (∀ i z, ‖ContourC1Space.toBCF γ (V i).val z‖ ≤ B * radScale R ρ j) →
      (∀ i z, e * radScale R ρ j ≤ ‖ContourC1Space.toBCF γ (V i).val z‖) →
      (∀ i, ‖V i‖ ≤ radScale R ρ j * L) →
      ∀ W : Fin 2 → LittleContourSpace γ, W ∈ circularQuarterPhaseDomain hγ hγ1 →
      V = radScale R ρ j • W →
      P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) →
      ∀ Z : FiniteCircularIndex N → ContourC1Space γ,
      (∀ i, Z (⟨j, Nat.lt_succ_of_le (j.isLt.le.trans hkN)⟩, i) = radScale R ρ j • (W i).val) →
      (∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
          (⟨j, Nat.lt_succ_of_le (j.isLt.le.trans hkN)⟩, i)).val) ⊆ torusBox) →
      (∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (Z (⟨j, Nat.lt_succ_of_le (j.isLt.le.trans hkN)⟩, i))) ⊆ torusBox) →
      (∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill
        (ContourC1Space.lift γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
          (⟨j, Nat.lt_succ_of_le (j.isLt.le.trans hkN)⟩, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
          (Z (⟨j, Nat.lt_succ_of_le (j.isLt.le.trans hkN)⟩, i)))) →
      (∀ i θ, ∀ l : Fin (j : ℕ), ‖radScale R ρ j • LittleContourSpace.lift γ (W i) θ‖ ≤
        cellA * radScale R ρ l) →
      ∀ Dvel : Fin 2 → LittleContourSpace γ,
      (∀ i θ, LittleContourSpace.lift γ (Dvel i) θ =
        velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
          (radScale R ρ j • LittleContourSpace.lift γ (W i) θ) +
        planeComplexEquiv (S.correctionLabelField t
          (complexTorusPoint (radScale R ρ j • LittleContourSpace.lift γ (W i) θ)))) →
      ∀ z : ℝ → Fin 2 → LittleContourSpace γ,
      HasDerivAt z Dvel t → z t = V → ∀ aTime τ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) aTime τ = t →
      ∃ Q : Fin 2 → LittleContourSpace γ,
        (∀ i θ, LittleContourSpace.lift γ (Q i) θ =
          P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k (j.isLt.le.trans hkN) S t
            (LittleContourSpace.lift γ (V i) θ)) ∧
        let A := ampScale A₀ b k
        let r := radScale R ρ j
        let Ω := finiteAncestorAngularVelocity A₀ b j
        let y := fun u => rigidRotationGauge (Ω / A) 0 u • normalizedPhysicalCurve A r aTime z u
        let p := rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • Q)
        let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) e L
        let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) c B L
        let CtR := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
        HasDerivAt y ((b ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (y τ) + p) τ ∧
        ‖p‖ ≤ (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
          ((CtR * b + weightedInteractionRowFeedback b (Cu + CtR) (Cl + CtR) C₀ ρ) *
            weightedFamilyNorm (C₀ * ρ ^ 6) k x + (Cu + CtR) / C₀ * ‖x k‖ +
            finitePrefixCompleteDeepBudget (γ : ℝ) e L Cd Cb b R ρ D) := by
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualPrefix_weighted_family_forcing
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro s A₀ b R ρ c B δ e a L Cb D C₀ hs hA hb hb1 hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀ hζ N k j hkN f T S hS t ht G x hq
    hsepU hsepL hradius hgeom hchart hsupp hsep V hVmax hVmin hVL W hW hVW hwf Z hscale
    hstartbox hendbox himages hx Dvel hDvel z hz hzt aTime τ htime
  obtain ⟨Q, hQ, hn⟩ := hsource hγ1.le hs hA hb hb1 hR hRmax hρ hρ1 hsmall
    ha ha16 hc hB he hL hCb hD hC₀ hζ N k j hkN S hS t ht G x hq
    hsepU hsepL hradius hgeom hchart hsupp hsep V hVmax hVmin hVL
  have hQ' : ∀ i θ, LittleContourSpace.lift γ (Q i) θ =
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k (j.isLt.le.trans hkN) S t
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ) := by
    intro i θ
    rw [hQ i θ, hVW]
    rfl
  obtain ⟨hyd, hpnorm⟩ := P.hasDerivAt_actualPrefix_sameGauge_currentClock hs hA hb hR hRmax hρ hρ1
    N j k j.isLt.le hkN S hwf Z t ht W hW hscale hstartbox hendbox himages hx Dvel Q hDvel hQ'
    z hz (hzt.trans hVW) aTime τ htime
  refine ⟨Q, hQ, hyd, ?_⟩
  exact hpnorm.trans_le hn

end CircularMaterialTransferProfile
end Euler2D

end
