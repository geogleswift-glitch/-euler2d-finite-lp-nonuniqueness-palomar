module

public import RequestProject.Euler.CircularCanonicalTargetBounds
public import RequestProject.Euler.CircularFinitePrefixWeightedFamilyForcing
public import RequestProject.Euler.CircularCanonicalAbsoluteDynamics
public import RequestProject.Euler.CompleteWeightedFeedbackAbsorption
public import RequestProject.Euler.CircularWeightedDeepPolynomialBudget

/-! Complete actual ancestor dynamics on the original canonical path.
Every forcing term is constructed from the same transported labels;
the fixed planar rows and the small periodic addition are kept separate. -/

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

theorem exists_uniform_actualCanonicalAncestor_derivative_budget :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧
      ∀ {s A₀ b R ρ c δ a Cb Dt C₀ Hglob D : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 → (5 / 4 : ℝ) * ρ ≤ cellA →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 ≤ Cb → 0 ≤ Dt → 2 ≤ C₀ →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 10 * ρ ≤ cellA / 2 → 8 * L * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 ≤ 1 →
      ∀ (N k : ℕ) (j : Fin k) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S → Hglob ≤ T →
      P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn
        (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceStrength A₀ b))
        (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) D X →
      ∀ t ∈ Icc (0 : ℝ) D,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      (∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val) →
      ∀ x : ℕ → Fin 2 → LittleContourSpace γ,
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (L + 1) * radScale R ρ j ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + Dt) ≤ a →
      (∀ v ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + Dt) < ‖v - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t v = 0) →
      8 * (Cb * ρ * (1 + Dt)) ≤ cellA / 2 →
      ∀ entrance τ : ℝ, physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t → Dt ≤ τ →
      let y := fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X u j.castSucc
      let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
      let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L
      let CtR := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      ∃ p : Fin 2 → LittleContourSpace γ,
        HasDerivAt y ((b ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (y τ) + p) τ ∧
        ‖p‖ ≤ (C₀ * ρ ^ 6) ^ (k - (j : ℕ)) *
          ((3 * CtR + weightedInteractionRowFeedback b Cu Cl C₀ ρ) * weightedFamilyNorm (C₀ * ρ ^ 6) k x +
            (Cu + 1) / C₀ * ‖x k‖ +
            finitePrefixUniformDeepCoefficient (γ : ℝ) (cellA / 2) L Cd Cb b * ρ ^ 6 * (1 + τ) ^ 4) := by
  dsimp only
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualPrefix_weighted_family_forcing
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro s A₀ b R ρ c δ a Cb Dt C₀ Hglob D hs hA hb hb1 hR hRmax hρ hρ1 hhalf hcore
    ha ha16 hc hCb hDt hC₀ hζ hsepU hsepL hRchart hCtR1
    N k j hkN f T S hS hglobT hwf X hX t ht G hG x hq hgeom hchart hsupp hsep entrance τ htime hDtτ
  let L := circularCanonicalCellNormBudget hγ hγ1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hmem := hX.mem t ht
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, hmem.1.2.trans hglobT⟩
  have htarget := finiteCircular_quarter_cell_target_bounds hγ hγ1 hR hρ (X t)
    hmem.2.2.2.1 j.castSucc
  have hU (l : Fin (k + 1)) (hjl : (j : ℕ) < l) :
      10 * radScale R ρ l ≤ (cellA / 2) * radScale R ρ j := by
    have hh := radScale_le_ratio_of_lt hR hρ hρ1 hjl
    nlinarith only [hh, mul_le_mul_of_nonneg_right hsepU (radScale_pos hR hρ j).le]
  have hLsep (l : Fin (k + 1)) (hlj : (l : ℕ) < j) :
      8 * (L * radScale R ρ j) ≤ c * radScale R ρ l := by
    have hh := radScale_le_ratio_of_lt hR hρ hρ1 hlj
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 8 * L)
    nlinarith only [hh', mul_le_mul_of_nonneg_right hsepL (radScale_pos hR hρ l).le]
  have hrad (l : Fin (k + 1)) : (5 / 4 : ℝ) * radScale R ρ l ≤ a :=
    (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)) (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans hRchart
  have hsep' : 8 * (Cb * ρ * radScale R ρ k * (1 + Dt)) ≤ (cellA / 2) * radScale R ρ j := by
    have hrkj : radScale R ρ k ≤ radScale R ρ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 (by omega : (j : ℕ) ≤ k)) hR.le
    have hh := mul_le_mul_of_nonneg_left hrkj (by positivity : 0 ≤ 8 * (Cb * ρ * (1 + Dt)))
    nlinarith only [hh, mul_le_mul_of_nonneg_right hsep (radScale_pos hR hρ j).le]
  obtain ⟨Q, hQ, hn⟩ := hsource (C₀ := C₀) (B := L) (e := cellA / 2) (L := L)
    hγ1.le hs hA hb hb1 hR hRmax hρ hρ1 (by linarith)
    ha ha16 hc hL (half_pos cellA_pos) hL.le hCb hDt (by linarith) (by linarith)
    N k j hkN S hS t htT G x hq hU hLsep hrad hgeom hchart hsupp hsep'
    (fun i => X t (j.castSucc, i)) htarget.1 htarget.2.1 htarget.2.2
  have hd := P.actualCanonicalPrefix_absolute_hasDerivAt hs hA hb hR hRmax hρ hρ1 hcore
    hkN S hglobT hwf X hX t ht G hG j.castSucc Q hQ entrance τ htime
  refine ⟨_, hd.1, hd.2.trans_le (hn.trans ?_)⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have htor : 0 ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 := by
    exact mul_nonneg (mul_nonneg hCt.le (finiteTorusLabelLittleRowCoefficient_nonneg hL.le)) (by positivity)
  have hf := completeWeighted_rhs_le_fixed_rows
    (Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L)
    (Cd := finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L)
    (D := finitePrefixCompleteDeepBudget (γ : ℝ) (cellA / 2) L Cd Cb b R ρ Dt)
    hb.le hb1 htor hCtR1 hC₀ hζ
    (show 0 ≤ weightedFamilyNorm (C₀ * ρ ^ 6) k x from norm_nonneg _) (norm_nonneg (x k))
  have hdeep := finitePrefixCompleteDeepBudget_le_uniform_polynomial (η := (γ : ℝ)) (Cb := Cb)
    (half_pos cellA_pos) hL.le
    hCd.le hb hR.le (hRmax.trans (by norm_num)) hhalf hDt hDtτ
  exact hf.trans (add_le_add le_rfl hdeep)

end CircularMaterialTransferProfile
end Euler2D

end
