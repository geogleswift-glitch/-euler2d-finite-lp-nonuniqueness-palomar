module

public import RequestProject.Euler.CircularFiniteActivePrefix
public import RequestProject.Euler.CircularFiniteInnerInitialRadius
public import RequestProject.Euler.CircularFiniteInnerLabelForcing
public import RequestProject.Euler.TorusPartialCanonicalLocalFlow

/-! A genuine local start for every actual active prefix, retaining
the ancient sample at the original cutoff. The inner support window,
all source bounds, and the separated target geometry follow from
the original finite datum; none is supplied as a forcing assumption. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) prefixStartLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) prefixStartLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) prefixStartC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) prefixStartC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_actualPrefix_canonical_local_start
    {s A₀ b R ρ q T a η : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ128 : ρ ≤ cellA / 128)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T)
    (hRa : (5 / 4) * R < a) (ha16 : a ≤ 1 / 16)
    (hη : 0 ≤ η) (hηa : η ≤ cellA / 16) (hηgap : η ≤ (1 - cellA) / 16)
    (hsize : R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4)
    (hancient : ∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η)
    {N k : ℕ} (hk : k ≤ N)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) :
    ∃ δ > 0, δ ≤ T ∧ ∃ Z : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      Z 0 = (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (finiteCircularPrefixIndex hk p)) ∧
      ContinuousOn Z (Icc (0 : ℝ) δ) ∧
      (∀ t ∈ Icc (0 : ℝ) δ, HasDerivAt Z
        (finiteContourPhaseFieldTotal hγ hγ1 (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceStrength A₀ b) (Z t) +
            S.actualPartialContourForcing (P.finiteInnerInitialLabel s A₀ b R ρ N k) t (Z t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) δ,
        IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t) ∧ ‖Z t‖ < a / 4 ∧
        IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceRadius R ρ) (Z t)) ∧
      ∀ t ∈ Icc (0 : ℝ) δ, ∀ p θ,
        HasDerivAt (fun u => LittleContourSpace.lift γ (Z u p) θ)
          (contourBoundaryField (finiteCircularInterfaceStrength A₀ b)
              (fun j => LittleContourSpace.lift γ (Z t j)) p θ +
            S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) t
              (LittleContourSpace.lift γ (Z t p) θ)) t := by
  have hρ1 : ρ ≤ 1 := by linarith only [hρ128, cellA_lt_one]
  have hρa : ρ ≤ cellA / 4 := by linarith only [hρ128, cellA_pos]
  have ha : 0 < a := (by positivity : 0 < (5 / 4 : ℝ) * R).trans hRa
  have ha1 : a < 1 := by linarith only [ha16]
  let rk := radScale R ρ k
  let ai₀ := (5 / 4 : ℝ) * ρ * rk
  let ai := (cellA / 64) * rk
  have hrk : 0 < rk := radScale_pos hR hρ k
  have hrkR : rk ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hai₀ : 0 ≤ ai₀ := by dsimp only [ai₀]; positivity
  have hai : 0 ≤ ai := mul_nonneg (div_nonneg cellA_pos.le (by norm_num)) hrk.le
  have hbuffer : ai₀ < ai := by
    have hh := mul_le_mul_of_nonneg_right hρ128 hrk.le
    dsimp only [ai₀, ai]
    nlinarith only [hh, mul_pos cellA_pos hrk]
  have hai1 : ai < 1 := by
    have hh := mul_le_mul_of_nonneg_right cellA_lt_one.le hrk.le
    dsimp only [ai]
    nlinarith only [hh, hrkR, hRmax]
  have hsep (p : FiniteCircularIndex k) : 32 * ai ≤ finiteCircularInterfaceRadius R ρ p := by
    have hp : p.1.val ≤ k := Nat.le_of_lt_succ p.1.isLt
    have hrr : rk ≤ radScale R ρ p.1 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 hp) hR.le
    have h₁ := mul_le_mul_of_nonneg_left hrr cellA_pos.le
    have h₂ := mul_le_mul_of_nonneg_right (circularContourRadii_bounds p.2).2.1
      (radScale_pos hR hρ p.1).le
    dsimp only [ai, finiteCircularInterfaceRadius]
    nlinarith only [h₁, h₂, mul_nonneg cellA_pos.le hrk.le]
  have hf := P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N
  have hB : ∀ᵐ x ∂μT,
      ‖finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x‖ ≤
          finiteInitialDensityBound A₀ b N := by
    filter_upwards [hf] with x hx
    rw [hx]
    exact P.norm_finiteInitialPlanarDensity_le hs N _
  have hqzero : ∀ x ∈ torusBox, ai₀ < ‖x - torusCenter‖ →
      P.finiteInnerInitialLabel s A₀ b R ρ N k x = 0 := by
    intro x hx hn
    apply Finset.sum_eq_zero
    intro j hj
    by_contra hne
    have hh := P.norm_sub_center_le_of_finiteInnerActiveInitialLabels
      hs hR hRmax hρ hρ1 N k ⟨hx, j, hj, hne⟩
    exact (not_le.mpr hn) hh
  have hshort : ∃ ε > 0, ε ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      ai < ‖x - torusCenter‖ → S.transportedScalar
        (P.finiteInnerInitialLabel s A₀ b R ρ N k) t x = 0 := by
    exact @BoundedEulerParticleSystem.exists_short_time_transported_support
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N)
      T S (P.finiteInnerInitialLabel s A₀ b R ρ N k)
      (finiteInitialDensityBound A₀ b N) ai₀ ai hT
      (finiteInitialDensityBound_nonneg A₀ b N) hB hai₀ hbuffer hai1 hqzero
  obtain ⟨εi, hεi, hεiT, hinneri⟩ := hshort
  have hglobalShort : ∃ ε > 0, ε ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar
        (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0 := by
    exact P.exists_finiteEuler_short_support
      (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 hq hqE hT hRa ha1 N S
  obtain ⟨εg, hεg, hεgT, hglobalg⟩ := hglobalShort
  let ε := min εi εg
  have hε : 0 < ε := lt_min hεi hεg
  have hεT : ε ≤ T := (min_le_left _ _).trans hεiT
  have hinner : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      ai < ‖x - torusCenter‖ → S.transportedScalar
        (P.finiteInnerInitialLabel s A₀ b R ρ N k) t x = 0 := by
    intro t ht
    exact hinneri t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hglobal : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar
        (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x = 0 := by
    intro t ht
    exact hglobalg t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  let Zinit : FiniteCircularIndex k → LittleContourSpace γ := fun p =>
    finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hk p)
  have hclose (p : FiniteCircularIndex k) :
      ‖(Zinit p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ η * radScale R ρ p.1 :=
    finiteCircular_initial_close hγ hγ1 hR hρ hη (P.ancient s) hancient N
      (finiteCircularPrefixIndex hk p)
  have hZadmissible := admissible_scaledCircular_family_of_close hγ hγ1
    hR hρ hρ1 hρa hη hηa hηgap Zinit hclose
  have hZphase : IsPhaseAdmissibleLittleContourFamily
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) Zinit := by
    refine ⟨0, ?_⟩
    simpa only [neg_zero, contourParameterShiftFamilyCLM_zero] using hZadmissible
  have htube : ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
      ‖contourParameterShiftC1 (β p) (Zinit p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
        η * radScale R ρ p.1 := by
    refine ⟨0, ?_⟩
    intro p
    simpa only [Pi.zero_apply, contourParameterShiftC1_zero] using hclose p
  have hZnorm : ‖Zinit‖ < a / 4 :=
    (norm_finiteCircular_closedPhaseTube_le hγ hγ1 hR hρ hρ1 hη
      (N := k) (Z := Zinit) htube).trans_lt hsize
  have hZquarter : IsQuarterPhaseLittleContourFamily
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) Zinit := by
    refine ⟨0, ?_⟩
    intro p
    simp only [Pi.zero_apply, contourParameterShiftC1_zero]
    have hradius : η < circularContourRadii p.2 / 4 := by
      linarith only [hηa, cellA_pos, (circularContourRadii_bounds p.2).2.1]
    have hh := mul_lt_mul_of_pos_right hradius (radScale_pos hR hρ p.1)
    exact (hclose p).trans_lt (by dsimp only [finiteCircularInterfaceRadius]; nlinarith only [hh])
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_torusBox] with x hfx hx
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx).trans hfx.symm
  have hmean : (∫ x in torusBox,
      finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N x) = 0 :=
    (integral_congr_ae hwf).symm.trans
      (P.integral_finiteInitialPeriodicDensity_zero hs hR hRmax hρ hρ1 N)
  obtain ⟨hqlp, hqper, hqbound⟩ := P.finiteInnerInitialLabel_bounds hs hA hb hR hRmax hρ hρ1 N k
  obtain ⟨δ, hδ, hδε, Z, hZ0, hZc, hZd, hZmem, hZmat⟩ :=
    S.exists_local_finiteCircular_actual_partial hS hwf
      (P.isTorusPeriodic_finiteInitialPeriodicDensity s A₀ b R ρ N)
      (P.finiteInitialPeriodicDensity_quarterTurn hs N) hmean
      hqlp hqper (P.finiteInnerInitialLabel_quarterTurn hs N k)
      (P.integral_finiteInnerInitialLabel_zero hs hA hb hR hRmax hρ hρ1 N k) hqbound
      hε hεT ha ha16 hglobal hai hai1 hinner hγ hγ1 hR hρ hρ1 hη hηa hsize hsep
      (finiteCircularInterfaceStrength A₀ b) Zinit ⟨hZphase, hZnorm, hZquarter⟩
  exact ⟨δ, hδ, hδε.trans hεT, Z, hZ0, hZc, hZd, hZmem, hZmat⟩

end CircularMaterialTransferProfile
end Euler2D

end
