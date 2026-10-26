module

public import RequestProject.Euler.CircularCurrentNonclusterForcing
public import RequestProject.Euler.CurrentNonclusterSmallness
public import RequestProject.Euler.LittleContourComplexScalar

/-! The actual same-S noncluster source in the rotating normalized
coordinates of the current contour. Fine actual ancestor and current
controls yield a true rho^14 bound, with one constant before all
physical scales, cutoff, stage, time and rotation angle. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) normalizedNonclusterLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) normalizedNonclusterLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCurrent_normalized_noncluster_rhoFourteen
    {b c B L Cb C₀ Kw Kcur : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hB : 0 < B) (hL : 0 ≤ L) (hCb : 0 ≤ Cb)
    (hC₀ : 1 ≤ C₀) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ C > 0, ∀ {s A₀ R ρ a δ D : ℝ},
      s ≤ 0 → 0 < A₀ → ∀ (hR : 0 < R), R ≤ 1 / 2 → R ≤ ρ →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 →
      0 < a → a ≤ 1 / 16 → 0 ≤ D → C₀ * ρ ^ 8 ≤ 1 / 2 →
      8 * B * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      ∀ (N k : ℕ) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
      ∀ t ∈ Icc (0 : ℝ) T,
      ∀ G : P.FiniteOuterMaterialTube s R ρ N k S t c δ,
      ∀ x : ℕ → Fin 2 → LittleContourSpace γ,
      weightedFamilyNorm (C₀ * ρ ^ 6) k x ≤ Kw * (C₀ * ρ ^ 6) →
      ‖x k‖ ≤ Kcur * (C₀ * ρ ^ 6) →
      (∀ (l : Fin (k + 1)) i,
        ‖contourParameterShiftC1 (G.shifts (finitePrefixForcingIndex hkN l, i))
          (G.contours (finitePrefixForcingIndex hkN l, i)) - G.reference (finitePrefixForcingIndex hkN l, i)‖ ≤
          radScale R ρ l * ‖x l‖) →
      (L + 1) * radScale R ρ k ≤ a / 2 →
      Cb * ρ * radScale R ρ k * (1 + D) ≤ a →
      (∀ y ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖y - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t y = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      ∀ θ : ℝ, ∀ Z : Fin 2 → LittleContourSpace γ,
      (∀ i z, ‖ContourC1Space.toBCF γ (Z i).val z‖ ≤ B) →
      (∀ i z, cellA / 2 ≤ ‖ContourC1Space.toBCF γ (Z i).val z‖) →
      (∀ i, ‖Z i‖ ≤ L) →
      ∃ Q : Fin 2 → LittleContourSpace γ,
        (∀ i u, LittleContourSpace.lift γ (Q i) u =
          Complex.exp (-((θ : ℂ) * I)) * ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
            P.finiteCurrentNonclusterPhysicalField s A₀ b R ρ N k hkN S t
              (radScale R ρ k • (Complex.exp ((θ : ℂ) * I) * LittleContourSpace.lift γ (Z i) u)))) ∧
        ‖Q‖ ≤ C * ρ ^ 14 * (1 + D) ^ 4 := by
  letI : NormSMulClass ℝ (LittleContourSpace γ) :=
    @NormedSpace.toNormSMulClass ℝ (LittleContourSpace γ) _ _
      (normalizedNonclusterLittle_space γ)
  obtain ⟨Ct, Cd, hCt, hCd, hsource⟩ := P.exists_uniform_actualCurrent_noncluster_family_forcing_budget
  let O := finiteOuterLabelLittleRowCoefficient (γ : ℝ) c B L
  let V := Ct * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let J := Cd * torusCorrectionContourBudget (γ : ℝ) L * finiteLabelMassBound
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hInt : 0 ≤ interiorContourNormBudget (γ : ℝ) 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB 0).trans (le_max_left _ _)
  have hO : 0 ≤ O := by dsimp only [O, finiteOuterLabelLittleRowCoefficient]; positivity
  have hV : 0 ≤ V := mul_nonneg hCt.le (finiteTorusLabelLittleRowCoefficient_nonneg hL)
  have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by unfold torusCorrectionContourBudget; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity [finiteLabelMassBound_nonneg]
  have hC₀0 : 0 ≤ C₀ := (by norm_num : (0 : ℝ) ≤ 1).trans hC₀
  let Cbase := V * Kcur * C₀ + 2 * b * C₀ ^ 2 * Kw * (O + V) + (2 / b) * J * Cb ^ 4
  let C := Cbase + 1
  have hCbase : 0 ≤ Cbase := by dsimp only [Cbase]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCbaseC : Cbase ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro s A₀ R ρ a δ D hs hA hR hRmax hRρ hρ hρ1 hhalf ha ha16 hD hζ hsepL hRchart
    N k hkN f T S hS t ht G x hx hcur hq hgeom hchart hsupp hsep θ Z hZmax hZmin hZL
  let r := radScale R ρ k
  let A := ampScale A₀ b k
  let phase := Complex.exp ((θ : ℂ) * I)
  let invphase := Complex.exp (-((θ : ℂ) * I))
  let W : Fin 2 → LittleContourSpace γ := fun i => r • LittleContourSpace.complexScale phase (Z i)
  have hr : 0 < r := radScale_pos hR hρ k
  have hApos : 0 < A := div_pos hA (pow_pos hb k)
  have hAr : 0 < A * r := mul_pos hApos hr
  have hphase : ‖phase‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hinvphase : ‖invphase‖ = 1 := by
    change ‖Complex.exp (-((θ : ℂ) * I))‖ = 1
    rw [show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hWmax (i : Fin 2) (z : ContourCircle) : ‖ContourC1Space.toBCF γ (W i).val z‖ ≤ B * r := by
    change ‖r • (phase * ContourC1Space.toBCF γ (Z i).val z)‖ ≤ _
    rw [norm_smul, norm_mul, hphase, one_mul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (hZmax i z) hr.le).trans_eq (mul_comm r B)
  have hWmin (i : Fin 2) (z : ContourCircle) : (cellA / 2) * r ≤ ‖ContourC1Space.toBCF γ (W i).val z‖ := by
    change _ ≤ ‖r • (phase * ContourC1Space.toBCF γ (Z i).val z)‖
    rw [norm_smul, norm_mul, hphase, one_mul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (hZmin i z) hr.le).trans_eq' (mul_comm r (cellA / 2))
  have hWL (i : Fin 2) : ‖W i‖ ≤ r * L := by
    rw [show W i = r • LittleContourSpace.complexScale phase (Z i) from rfl,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr, LittleContourSpace.norm_complexScale_eq,
      hphase, one_mul]
    exact mul_le_mul_of_nonneg_left (hZL i) hr.le
  let K := Kw * (C₀ * ρ ^ 6)
  let Δ := (2 * b * C₀ * K * (O + V)) * ρ ^ 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hΔ : 0 ≤ Δ := by dsimp only [Δ]; positivity
  obtain ⟨Qraw, hQraw, hnraw⟩ := hsource hγ1.le hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB (half_pos cellA_pos) hL hCb hD hC₀ hK hΔ hζ hsepL hRchart le_rfl
    N k hkN S hS t ht G x hx hq hgeom hchart hsupp hsep W hWmax hWmin hWL
  have hn : ‖Qraw‖ / (A * r) ≤ Cbase * ρ ^ 14 * (1 + D) ^ 4 := by
    exact hnraw.trans (current_noncluster_budget_le_rhoFourteen hb hC₀0 hKw hKcur hO hV hJ
      hR.le hRρ hρ.le hD hcur)
  let Q : Fin 2 → LittleContourSpace γ := fun i =>
    LittleContourSpace.complexScale invphase ((A * r)⁻¹ • Qraw i)
  have hQnorm (i : Fin 2) : ‖Q i‖ = (A * r)⁻¹ * ‖Qraw i‖ := by
    rw [show Q i = LittleContourSpace.complexScale invphase ((A * r)⁻¹ • Qraw i) from rfl,
      LittleContourSpace.norm_complexScale_eq, hinvphase, one_mul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hAr)]
  have hnQ : ‖Q‖ ≤ ‖Qraw‖ / (A * r) := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg Qraw) hAr.le)).mpr
    intro i
    calc
      ‖Q i‖ = (A * r)⁻¹ * ‖Qraw i‖ := by
        simpa only [Q] using hQnorm i
      _ ≤ (A * r)⁻¹ * ‖Qraw‖ :=
        mul_le_mul_of_nonneg_left (norm_le_pi_norm Qraw i) (inv_pos.mpr hAr).le
      _ = ‖Qraw‖ / (A * r) := by rw [div_eq_mul_inv, mul_comm]
  refine ⟨Q, ?_, (hnQ.trans hn).trans ?_⟩
  · intro i u
    change invphase * ((A * r)⁻¹ • LittleContourSpace.lift γ (Qraw i) u) = _
    rw [hQraw]
    rfl
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbaseC (by positivity)) (by positivity)

end CircularMaterialTransferProfile
end Euler2D

end
