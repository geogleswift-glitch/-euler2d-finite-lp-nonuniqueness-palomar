module

public import RequestProject.Euler.CircularFiniteCurrentForcingBudget

/-! The actual external forcing with the inner planar velocity kept
separate. Only the true ancestor rows and periodic corrections enter
the remainder bound. The inner planar leading term is never included
in, or subtracted from, a bound for the total force. -/

@[expose] public section

set_option maxHeartbeats 18000000
set_option maxRecDepth 7000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) currentNonclusterLittle_group (η : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace η) := Submodule.normedAddCommGroup (LittleContourSpace η)
local instance (priority := 2000) currentNonclusterLittle_space (η : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace η) := Submodule.normedSpace (LittleContourSpace η)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteCurrentNonclusterPhysicalField (s A₀ b R ρ : ℝ) (N k : ℕ) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) : ℂ :=
  P.finitePrefixPlanarRowField s A₀ b R ρ N k k hkN S t x +
    P.finitePrefixTorusRowField s A₀ b R ρ N k S t x +
      actualTorusCorrectionVelocity (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x

theorem finiteCurrentOffSelf_eq_inner_add_noncluster
    {s A₀ b R ρ : ℝ} (N k : ℕ) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) (x : ℂ) :
    P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N k k hkN S t x =
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x +
        P.finiteCurrentNonclusterPhysicalField s A₀ b R ρ N k hkN S t x := by
  rw [P.finitePrefixOffSelfPhysicalField_eq_rows N k k hkN le_rfl S t]
  unfold finiteCurrentNonclusterPhysicalField
  ring

theorem exists_uniform_actualCurrent_noncluster_family_forcing_budget :
    ∃ Ct Cd : ℝ, 0 < Ct ∧ 0 < Cd ∧ ∀ {η : ℝ≥0}, (η : ℝ) ≤ 1 →
      ∀ {s A₀ b R ρ c B δ e a L Cb D C₀ K Δ : ℝ},
      s ≤ 0 → 0 < A₀ → 0 < b → b ≤ 1 → ∀ (hR : 0 < R), R ≤ 1 / 2 →
      ∀ (hρ : 0 < ρ), ρ ≤ 1 → ρ ^ 2 ≤ b / 2 →
      0 < a → a ≤ 1 / 16 → 0 < c → 0 < B → 0 < e →
      0 ≤ L → 0 ≤ Cb → 0 ≤ D → 1 ≤ C₀ → 0 ≤ K → 0 ≤ Δ →
      C₀ * ρ ^ 8 ≤ 1 / 2 → 8 * B * ρ ≤ c → (5 / 4 : ℝ) * R ≤ a →
      (2 * b * C₀ * K * (finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L +
        Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L)) * ρ ^ 2 ≤ Δ →
      ∀ (N k : ℕ) (hkN : k ≤ N),
      ∀ {f : Lp ℝ 2 μT} {T : ℝ},
      ∀ S : BoundedEulerParticleSystem f T, IsFourfoldBoundedEulerParticleSystem S →
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
      (∀ y ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖y - torusCenter‖ →
        P.finiteInnerClusterSource s A₀ b R ρ N k S t y = 0) →
      8 * (Cb * ρ * (1 + D)) ≤ e →
      ∀ W : Fin 2 → LittleContourSpace η,
      (∀ i z, ‖ContourC1Space.toBCF η (W i).val z‖ ≤ B * radScale R ρ k) →
      (∀ i z, e * radScale R ρ k ≤ ‖ContourC1Space.toBCF η (W i).val z‖) →
      (∀ i, ‖W i‖ ≤ radScale R ρ k * L) →
      ∃ Q : Fin 2 → LittleContourSpace η,
        (∀ i θ, LittleContourSpace.lift η (Q i) θ =
          P.finiteCurrentNonclusterPhysicalField s A₀ b R ρ N k hkN S t (LittleContourSpace.lift η (W i) θ)) ∧
        ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
          Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L * R ^ 8 * ‖x k‖ +
            Δ * ρ ^ 6 * (1 + D) ^ 4 +
            (2 / b) * (Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound) *
              Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 := by
  obtain ⟨Ct, hCt, htorus⟩ := P.exists_uniform_finitePrefix_torus_contourLittle_rows
  obtain ⟨Cd, hCd, hdeep⟩ := P.exists_uniform_finiteInnerCluster_torus_weighted_contourLittle
  refine ⟨Ct, Cd, hCt, hCd, ?_⟩
  intro η hη s A₀ b R ρ c B δ e a L Cb D C₀ K Δ hs hA hb hb1 hR hRmax hρ hρ1 hhalf
    ha ha16 hc hB he hL hCb hD hC₀ hK hΔ hζ hsepL hRchart hsmall
    N k hkN f T S hS t ht G x hx hq hgeom hchart hsupp hsep W hWmax hWmin hWL
  have hρsmall : ρ ^ 2 < b := by linarith
  have hC₀pos : 0 < C₀ := by linarith
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hr (l : ℕ) : 0 < radScale R ρ l := radScale_pos hR hρ l
  let den := ampScale A₀ b k * radScale R ρ k
  have hden : 0 < den := mul_pos hAk (hr k)
  have hsepU (l : Fin (k + 1)) (hl : k < (l : ℕ)) : 10 * radScale R ρ l ≤ e * radScale R ρ k := by
    have hh := l.isLt
    omega
  have hsepL' (l : Fin (k + 1)) (hl : (l : ℕ) < k) :
      8 * (B * radScale R ρ k) ≤ c * radScale R ρ l := by
    have hh := radScale_le_ratio_of_lt hR hρ hρ1 hl
    calc
      _ = (8 * B) * radScale R ρ k := by ring
      _ ≤ (8 * B) * (ρ * radScale R ρ l) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := by convert mul_le_mul_of_nonneg_right hsepL (hr l).le using 1 <;> ring
  have hrad (l : Fin (k + 1)) : (5 / 4 : ℝ) * radScale R ρ l ≤ a :=
    (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1))
      (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans hRchart
  let O := finiteOuterLabelLittleRowCoefficient (η : ℝ) c B L
  let V := Ct * finiteTorusLabelLittleRowCoefficient (η : ℝ) L
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hInt : 0 ≤ interiorContourNormBudget (η : ℝ) 1 c B L :=
    (interiorSpatialDerivativeBudget_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB 0).trans (le_max_left _ _)
  have hO : 0 ≤ O := by unfold O finiteOuterLabelLittleRowCoefficient; positivity
  have hV : 0 ≤ V := mul_nonneg hCt.le (finiteTorusLabelLittleRowCoefficient_nonneg hL)
  have hR8 : R ^ 8 ≤ 1 := pow_le_one₀ hR.le (by linarith only [hRmax])
  have hrows := current_prefix_rows_le_polynomial_margin
    (U := finiteInnerLabelLittleRowCoefficient (η : ℝ) e L) hO hV hR8 hb hb1 hC₀pos hρ hζ hK hΔ
    k x hx hsmall hD
  let Bd := (2 / b) * (Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound) *
    Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4
  have hdenHalf : b / 2 ≤ b * (1 - ρ ^ 2 / b) := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne']
    linarith only [hhalf]
  have hdeepBound : Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound *
      Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) ≤ Bd := by
    have htor : 0 ≤ torusCorrectionContourBudget (η : ℝ) L := by unfold torusCorrectionContourBudget; positivity
    calc
      _ ≤ (Cd * torusCorrectionContourBudget (η : ℝ) L * finiteLabelMassBound *
          Cb ^ 4 * R ^ 8 * ρ ^ 6 * (1 + D) ^ 4) / (b / 2) :=
        div_le_div_of_nonneg_left (by positivity [finiteLabelMassBound_nonneg]) (half_pos hb) hdenHalf
      _ = _ := by dsimp only [Bd]; ring
  let Budget := V * R ^ 8 * ‖x k‖ + Δ * ρ ^ 6 * (1 + D) ^ 4 + Bd
  have hex (i : Fin 2) : ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        P.finiteCurrentNonclusterPhysicalField s A₀ b R ρ N k hkN S t (LittleContourSpace.lift η (W i) θ)) ∧
      ‖Q‖ / den ≤ Budget := by
    obtain ⟨Qp, hQp, hnp⟩ := P.exists_finitePrefix_planar_contourLittle_rows hη hs hA hb hR hRmax hρ hρ1
      N k k hkN le_rfl S t ht G (fun l => ‖x l‖) (fun _ => norm_nonneg _) hq hc hB he hsepU hsepL'
      (W i) (hWmax i) (hWmin i) (hWL i)
    obtain ⟨Qt, hQt, hnt⟩ := htorus hη hs hA hb hR hRmax hρ hρ1 ha ha16
      N k k hkN S t ht G (fun l => ‖x l‖) (fun _ => norm_nonneg _) hq hrad hL hgeom
      (W i) (by simpa only [mul_comm L] using hWL i)
    obtain ⟨Qdt, hQdt, hndt⟩ := hdeep hη hs hA hb hR hRmax hρ hρ1 hρsmall ha ha16 hCb hD hC₀
      N k k le_rfl S hS t ht hchart hsupp hL hgeom (W i) (by simpa only [mul_comm L] using hWL i)
    simp only [Nat.sub_self, pow_zero, one_mul] at hndt
    refine ⟨Qp + Qt + Qdt, ?_, ?_⟩
    · intro θ
      change LittleContourSpace.eval η (θ : ContourCircle) (Qp + Qt + Qdt) = _
      simp only [map_add]
      change LittleContourSpace.lift η Qp θ + LittleContourSpace.lift η Qt θ +
        LittleContourSpace.lift η Qdt θ = _
      rw [hQp, hQt, hQdt]
      rfl
    · calc
        _ ≤ (‖Qp‖ + ‖Qt‖ + ‖Qdt‖) / den :=
          div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) hden.le
        _ = ‖Qp‖ / den + ‖Qt‖ / den + ‖Qdt‖ / den := by ring
        _ ≤ _ := add_le_add (add_le_add hnp hnt) hndt
        _ ≤ Budget := add_le_add hrows hdeepBound
  classical
  choose Qi hQi hn using hex
  refine ⟨Qi, hQi, ?_⟩
  have hBudget0 : 0 ≤ Budget := (div_nonneg (norm_nonneg (Qi 0)) hden.le).trans (hn 0)
  change ‖Qi‖ / den ≤ Budget
  apply (div_le_iff₀ hden).mpr
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hBudget0 hden.le)).mpr
  intro i
  exact (div_le_iff₀ hden).mp (hn i)

end CircularMaterialTransferProfile
end Euler2D

end
