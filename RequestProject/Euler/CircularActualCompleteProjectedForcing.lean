module

public import RequestProject.Euler.CircularNormalizedNonclusterSmallness
public import RequestProject.Euler.CircularActualAdjacentProjectedForcing

/-! The complete actual off-self force has the observed child's
rho^6 growing-coordinate leading term. The source split and every
remainder are constructed from one and the same original finite
Euler system; no total projected-force estimate is assumed. -/

@[expose] public section

set_option maxHeartbeats 28000000
set_option maxRecDepth 8000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) actualCompleteProjectedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) actualCompleteProjectedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCurrent_complete_projected_leading
    {b c B L Cb C₀ Kw Kcur : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hB : 0 < B) (hL : 0 ≤ L) (hCb : 0 ≤ Cb)
    (hC₀ : 1 ≤ C₀) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ C > 0, ∀ {s A₀ R ρ a δ D ε η : ℝ},
      s ≤ 0 → 0 < A₀ → ∀ (hR : 0 < R), R ≤ 1 / 2 → R ≤ ρ →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 →
      0 < a → a ≤ 1 / 16 → 0 ≤ D → 0 ≤ ε → 0 ≤ η →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 8 * B * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      ∀ (N k : ℕ) (hkN : k ≤ N), k + 1 ≤ N →
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
      Cb * ρ * radScale R ρ k * (1 + D) < 1 →
      (∀ y ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖y - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t y = 0) →
      (∀ z, Cb * radScale R ρ (k + 1) * (1 + D) < ‖z‖ →
        boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t) z = 0) →
      (∀ z, Cb * radScale R ρ (k + 1) * (1 + D) < ‖z‖ →
        P.finiteInnerClusterComplexSource s A₀ b R ρ N (k + 1) S t z = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      ∀ θp θc : ℝ, ∀ M : ℂ,
      (‖momentN (boxedComplexDensity
          (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (k + 1)) t)) 4 -
        (ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6 *
          Complex.exp (-(4 * (θc : ℂ) * I)) * M‖ ≤
        ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * η) →
      ∀ Z : Fin 2 → LittleContourSpace γ,
      (∀ i z, ‖ContourC1Space.toBCF γ (Z i).val z‖ ≤ B) →
      (∀ i z, cellA / 2 ≤ ‖ContourC1Space.toBCF γ (Z i).val z‖) →
      (∀ i, ‖Z i‖ ≤ L) →
      (∀ i u, ‖LittleContourSpace.lift γ (Z i) u - refCircle (circularContourRadii i) u‖ ≤ ε) →
      ∃ Q : Fin 2 → LittleContourSpace γ,
        (∀ i u, LittleContourSpace.lift γ (Q i) u =
          Complex.exp (-((θp : ℂ) * I)) * ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
            P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t
              (radScale R ρ k • (Complex.exp ((θp : ℂ) * I) * LittleContourSpace.lift γ (Z i) u)))) ∧
        ‖(b : ℂ) * circularUnstableCoordinateCLM γ Q -
          (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M‖ ≤
          C * (ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε +
            ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η + ρ ^ 14 * (1 + D) ^ 4) := by
  obtain ⟨Ci, hCi, hinner⟩ := P.exists_uniform_actualFinite_adjacent_projected_leading hb hCb
  obtain ⟨Cr, hCr, hrest⟩ := P.exists_uniform_actualCurrent_normalized_noncluster_rhoFourteen
    hb hb1 hc hB hL hCb hC₀ hKw hKcur
  let Co := b * ‖circularUnstableCoordinateCLM γ‖ * Cr
  let C := Ci + Co + 1
  have hCo : 0 ≤ Co := by dsimp only [Co]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCiC : Ci ≤ C := by dsimp only [C]; linarith only [hCo]
  have hCoC : Co ≤ C := by dsimp only [C]; linarith only [hCi]
  refine ⟨C, hC, ?_⟩
  intro s A₀ R ρ a δ D ε η hs hA hR hRmax hRρ hρ hρ1 hhalf ha ha16 hD hε hη hζ hsepL hRchart
    N k hkN hkchild f T S hS t ht G x hx hcur hq hgeom hchart ha1 hsupp hchild hdeep hsep θp θc M hclose
    Z hZmax hZmin hZL hnear
  have hRs : Cb * radScale R ρ (k + 1) * (1 + D) = Cb * ρ * radScale R ρ k * (1 + D) := by
    rw [radScale_succ_eq_mul]
    ring
  obtain ⟨Qi, hQi, hpi⟩ := hinner hs hA hR hRmax hρ hρ1 hhalf hD hε hη N k hkchild S hS t ht θp θc M
    (by rwa [hRs]) (by simpa only [hRs] using hsupp) hchild hdeep hclose hsep Z hZmin hnear
  obtain ⟨Qr, hQr, hnr⟩ := hrest hs hA hR hRmax hRρ hρ hρ1 hhalf ha ha16 hD hζ hsepL hRchart
    N k hkN S hS t ht G x hx hcur hq hgeom hchart hsupp hsep θp Z hZmax hZmin hZL
  let E := ρ ^ 10 * (1 + D) ^ 8 + ρ ^ 6 * (1 + D) ^ 4 * ε + ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η
  let Er := ρ ^ 14 * (1 + D) ^ 4
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hEr : 0 ≤ Er := by dsimp only [Er]; positivity
  have hpr : ‖(b : ℂ) * circularUnstableCoordinateCLM γ Qr‖ ≤ Co * Er := by
    calc
      _ = b * ‖circularUnstableCoordinateCLM γ Qr‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
      _ ≤ b * (‖circularUnstableCoordinateCLM γ‖ * ‖Qr‖) :=
        mul_le_mul_of_nonneg_left ((circularUnstableCoordinateCLM γ).le_opNorm Qr) hb.le
      _ ≤ b * (‖circularUnstableCoordinateCLM γ‖ * (Cr * ρ ^ 14 * (1 + D) ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnr (norm_nonneg _)) hb.le
      _ = _ := by dsimp only [Co, Er]; ring
  refine ⟨Qi + Qr, ?_, ?_⟩
  · intro i u
    change LittleContourSpace.eval γ (u : ContourCircle) (Qi i + Qr i) = _
    rw [map_add]
    change LittleContourSpace.lift γ (Qi i) u + LittleContourSpace.lift γ (Qr i) u = _
    rw [hQi, hQr, P.finiteCurrentOffSelf_eq_inner_add_noncluster N k hkN S t]
    simp only [smul_add, mul_add]
  · have hdiff : (b : ℂ) * circularUnstableCoordinateCLM γ (Qi + Qr) -
        (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M =
        ((b : ℂ) * circularUnstableCoordinateCLM γ Qi -
          (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M) +
          (b : ℂ) * circularUnstableCoordinateCLM γ Qr := by rw [map_add]; ring
    rw [hdiff]
    calc
      _ ≤ ‖(b : ℂ) * circularUnstableCoordinateCLM γ Qi -
          (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M‖ +
          ‖(b : ℂ) * circularUnstableCoordinateCLM γ Qr‖ := norm_add_le _ _
      _ ≤ Ci * E + Co * Er := add_le_add hpi hpr
      _ ≤ C * E + C * Er := add_le_add (mul_le_mul_of_nonneg_right hCiC hE)
        (mul_le_mul_of_nonneg_right hCoC hEr)
      _ = _ := by dsimp only [E, Er]; ring

end CircularMaterialTransferProfile
end Euler2D

end
