module

public import RequestProject.Euler.MaterialTransferErrorSmallness
public import RequestProject.Euler.CircularActualMaterialGrowingEquation

/-! The complete physical force and the strong equation of the SAME
original canonical Euler trajectory are now composed. On the child
clock the actual growing coordinate has the observed fourth-moment
leading source, with a cutoff-independent rho^8 error. Neither a
scalar ODE nor a total projected-force estimate is supplied as input. -/

@[expose] public section

set_option maxHeartbeats 30000000
set_option maxRecDepth 8500

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem norm_canonicalPrefixMaterialCurrent_sub_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (σ : ℝ) :
    ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ - littleCircularReference hγ hγ1‖ =
      ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
        littleCircularMaterialContours hγ hγ1 σ‖ := by
  rw [← norm_contourParameterShiftFamilyCLM
    (fun i => -(circularContourAngularVelocities i * σ))
    (canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
      littleCircularMaterialContours hγ hγ1 σ), map_sub,
    materialUnshift_circularMaterialContours]
  rfl

theorem canonicalPrefixMaterialCurrent_near_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (A₀ b R ρ : ℝ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ) (σ : ℝ)
    (i : Fin 2) (u : ℝ) :
    ‖LittleContourSpace.lift γ (canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ i) u -
        refCircle (circularContourRadii i) u‖ ≤
      ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
        littleCircularMaterialContours hγ hγ1 σ‖ := by
  rw [← norm_canonicalPrefixMaterialCurrent_sub_reference hγ hγ1]
  change ‖LittleContourSpace.eval γ (u : ContourCircle)
      ((canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ - littleCircularReference hγ hγ1) i)‖ ≤ _
  exact (LittleContourSpace.norm_eval_le _ _).trans (norm_le_pi_norm _ i)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_material_forced_equation
    {b c B L Cb C₀ Kw Kcur : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hB : 0 < B) (hL : 0 ≤ L) (hCb : 0 ≤ Cb)
    (hC₀ : 1 ≤ C₀) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ C > 0, ∃ r > 0,
      ∀ {s A₀ R ρ a δ D η Hglob H : ℝ},
      s ≤ 0 → 0 < A₀ → ∀ (hR : 0 < R), R ≤ 1 / 2 → R ≤ ρ →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 →
      0 < a → a ≤ 1 / 16 → 0 ≤ D → 0 ≤ η →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 8 * B * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (5 / 4 : ℝ) * ρ ≤ cellA →
      ∀ (N k : ℕ) (hkN : k ≤ N), k + 1 ≤ N →
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      Hglob ≤ T → P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S H X →
      ∀ t ∈ Icc (0 : ℝ) H,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      (∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val) →
      ∀ x : ℕ → Fin 2 → LittleContourSpace γ,
      weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ Kw * (C₀ * ρ ^ 6) →
      ‖x k‖ ≤ Kcur * (C₀ * ρ ^ 6) →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) -
            G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤ radScale R ρ l * ‖x l‖) →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      Cb * ρ * radScale R ρ k * (1 + D) < 1 →
      (∀ y ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖y - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t y = 0) →
      (∀ z, Cb * radScale R ρ (k + 1) * (1 + D) < ‖z‖ →
        boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t) z = 0) →
      (∀ z, Cb * radScale R ρ (k + 1) * (1 + D) < ‖z‖ →
        P.finiteInnerClusterComplexSource s A₀ b R ρ N (k + 1) S t z = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      ∀ σ₀ τ θc : ℝ, let σ := σ₀ + b * τ;
      physicalTimeFromNormalized (ampScale A₀ b k) 0 σ = t →
      ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
        littleCircularMaterialContours hγ hγ1 σ‖ ≤ r →
      ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
        littleCircularMaterialContours hγ hγ1 σ‖ ≤ Kcur * (C₀ * ρ ^ 6) →
      (∀ i z, ‖ContourC1Space.toBCF γ
        (canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ i).val z‖ ≤ B) →
      (∀ i z, cellA / 2 ≤ ‖ContourC1Space.toBCF γ
        (canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ i).val z‖) →
      (∀ i, ‖canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ i‖ ≤ L) →
      ∀ M : ℂ,
      (‖momentN (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t)) 4 -
        (ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6 *
          Complex.exp (-(4 * (θc : ℂ) * I)) * M‖ ≤
        ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * η) →
      ∃ E : ℂ, ‖E‖ ≤ C * (ρ ^ 8 * (1 + D) ^ 8 + ρ ^ 6 * η) ∧
        HasDerivAt
          (fun u => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X (σ₀ + b * u))
          ((b : ℂ) * lamStar * canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X σ +
            (ρ : ℂ) ^ 6 * Kstar * Complex.exp
              (4 * (((t * finiteAncestorAngularVelocity A₀ b k - θc : ℝ) : ℂ)) * I) * M + E) τ := by
  obtain ⟨Cs, hCs, hsource⟩ := P.exists_uniform_actualCurrent_complete_projected_leading
    hb hb1 hc hB hL hCb hC₀ hKw hKcur
  obtain ⟨Cn, hCn, r, hr, hscalar⟩ := P.exists_uniform_actualCanonical_material_growing_equation
  let K := Kcur * C₀
  have hC₀0 : 0 ≤ C₀ := (by norm_num : (0 : ℝ) ≤ 1).trans hC₀
  have hK : 0 ≤ K := mul_nonneg hKcur hC₀0
  let C := Cs * (3 + K) + b * Cn * K ^ 2 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, r, hr, ?_⟩
  intro s A₀ R ρ a δ D η Hglob H hs hA hR hRmax hRρ hρ hρ1 hhalf ha ha16 hD hη hζ
    hsepL hRchart hρcore N k hkN hkchild f T S hS hglobT hwf X hX t ht G hG x hx hcur hq
    hgeom hchart ha1 hsupp hchild hdeep hsep σ₀ τ θc
  dsimp only
  intro htime hsmall hfine hZmax hZmin hZL M hclose
  let σ := σ₀ + b * τ
  let e := ‖canonicalPrefixAbsoluteCell A₀ b R ρ k 0 X σ (Fin.last k) -
    littleCircularMaterialContours hγ hγ1 σ‖
  let θp := t * finiteAncestorAngularVelocity A₀ b k
  let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k X σ
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, (hX.mem t ht).1.2.trans hglobT⟩
  obtain ⟨Q, hQ, hproject⟩ := hsource hs hA hR hRmax hRρ hρ hρ1 hhalf ha ha16 hD
    (norm_nonneg _) hη hζ hsepL hRchart N k hkN hkchild S hS t htT G x hx hcur hq
    hgeom hchart ha1 hsupp hchild hdeep hsep θp θc M hclose Z hZmax hZmin hZL
    (canonicalPrefixMaterialCurrent_near_reference hγ hγ1 A₀ b R ρ k X σ)
  obtain ⟨En, hEn, hd⟩ := hscalar hs hA hb hR hRmax hρ hρ1 hρcore hkN S hglobT hwf
    X hX t ht G hG σ htime hsmall Q hQ
  let lead := (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M
  let E := ((b : ℂ) * circularUnstableCoordinateCLM γ Q - lead) + (b : ℂ) * En
  have hE : ‖E‖ ≤ Cs * (ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * e +
      ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η + ρ ^ 14 * (1 + D) ^ 4) + b * Cn * e ^ 2 := by
    calc
      _ ≤ ‖(b : ℂ) * circularUnstableCoordinateCLM γ Q - lead‖ + ‖(b : ℂ) * En‖ :=
        norm_add_le _ _
      _ = ‖(b : ℂ) * circularUnstableCoordinateCLM γ Q - lead‖ + b * ‖En‖ := by
        rw [norm_mul (b : ℂ) En, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
      _ ≤ _ := by
        have hprod := mul_le_mul_of_nonneg_left hEn hb.le
        simpa only [lead, e, mul_assoc] using add_le_add hproject hprod
  have he : e ≤ K * ρ ^ 6 := by simpa only [K, mul_assoc] using hfine
  have he0 : 0 ≤ e := norm_nonneg _
  have hbudget := material_transfer_error_le_rhoEight hCs.le hCn.le hb.le hK hρ.le hρ1 hD hη
    he he0 he
  have hbudgetC : ‖E‖ ≤ C * (ρ ^ 8 * (1 + D) ^ 8 + ρ ^ 6 * η) := by
    apply (hE.trans hbudget).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [C]
    linarith
  have haff : HasDerivAt (fun u : ℝ => σ₀ + b * u) b τ := by
    simpa only [mul_one, zero_add] using
      (hasDerivAt_const τ σ₀).add ((hasDerivAt_id τ).const_mul b)
  have hdchild := hd.scomp τ haff
  have hdchild' : HasDerivAt
      (fun u => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X (σ₀ + b * u))
      ((b : ℂ) * (lamStar * canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k X σ +
        circularUnstableCoordinateCLM γ Q + En)) τ := by
    simpa only [Function.comp_def, Complex.real_smul] using hdchild
  refine ⟨E, hbudgetC, ?_⟩
  convert hdchild' using 1 <;> dsimp only [E, lead, θp] <;> ring

end CircularMaterialTransferProfile
end Euler2D

end
