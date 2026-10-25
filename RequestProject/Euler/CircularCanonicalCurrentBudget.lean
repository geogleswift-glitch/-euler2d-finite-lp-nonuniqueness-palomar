module

public import RequestProject.Euler.CircularCanonicalTargetBounds
public import RequestProject.Euler.CircularFiniteCurrentFamilyForcing
public import RequestProject.Euler.CircularCanonicalAbsoluteDynamics

/-! The actual canonical current cell has its genuine complete
forcing budget. Its physical derivative, isolated domain and target
geometry are consequences of the same canonical X. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonicalCurrent_derivative_budget :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧
      ∀ {s A₀ b R ρ c δ a Cb Dt C₀ K Δ Hglob D : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 → (5 / 4 : ℝ) * ρ ≤ cellA →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 ≤ Cb → 0 ≤ Dt → 1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 8 * L * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (γ : ℝ) c L L +
        Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ Δ →
      ∀ (N k : ℕ) (hkN : k ≤ N),
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
      weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ K →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + Dt) ≤ a →
      (∀ v ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + Dt) < ‖v - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t v = 0) →
      8 * (Cb * ρ * (1 + Dt)) ≤ cellA / 2 →
      ∀ entrance τ : ℝ, physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t →
      let y := fun u => canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X u (Fin.last k)
      ∃ p : Fin 2 → LittleContourSpace γ,
        HasDerivAt y (circularBanachField hγ hγ1 (y τ) + p) τ ∧
        ‖p‖ ≤ Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8 * ‖x k‖ +
          (finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + Δ) *
            ρ ^ 6 * (1 + Dt) ^ 4 := by
  dsimp only
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualCurrent_family_forcing_budget
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro s A₀ b R ρ c δ a Cb Dt C₀ K Δ Hglob D hs hA hb hb1 hR hRmax hρ hρ1 hhalf hcore
    ha ha16 hc hCb hDt hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN f T S hS hglobT hwf X hX t ht G hG x hx hq hgeom hchart hsupp hsep entrance τ htime
  let L := circularCanonicalCellNormBudget hγ hγ1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hmem := hX.mem t ht
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, hmem.1.2.trans hglobT⟩
  have htarget := finiteCircular_quarter_cell_target_bounds hγ hγ1 hR hρ (X t)
    hmem.2.2.2.1 (Fin.last k)
  obtain ⟨Q, hQ, hn⟩ := hsource hγ1.le hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hL (half_pos cellA_pos) hL.le hCb hDt hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN S hS t htT G x hx hq hgeom hchart hsupp hsep
    (fun i => X t (Fin.last k, i)) htarget.1 htarget.2.1 htarget.2.2
  have hd := P.actualCanonicalPrefix_absolute_hasDerivAt hs hA hb hR hRmax hρ hρ1 hcore
    hkN S hglobT hwf X hX t ht G hG (Fin.last k) Q hQ entrance τ htime
  have hd1 := hd.1
  simp only [Fin.val_last, Nat.sub_self, pow_zero, one_smul] at hd1
  exact ⟨_, hd1, hd.2.trans_le hn⟩

end CircularMaterialTransferProfile
end Euler2D

end
