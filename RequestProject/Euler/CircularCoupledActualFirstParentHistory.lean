module

public import RequestProject.Euler.CircularActualFirstParentHistory
public import RequestProject.Euler.CircularCoupledActualJointMaterialEquation

/-! Integrate the SAME actual first-parent equation and literal child
moment history with R=rho^10, A0=cA*(1+xi). The original zero growing
coordinate, physical lookback clock and entry error are retained. -/

@[expose] public section

set_option maxHeartbeats 40000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFirstParent_coupled_past_history_bound
    {b Chistory ηctrl : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hChistory : 0 ≤ Chistory) (hηctrl : 0 ≤ ηctrl) :
    ∃ C > 0,
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        ∀ k : ℕ,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) (k + 1)) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ (Nat.le_succ k) S H Y →
        ∀ e exit : ℝ, 0 ≤ e → e ≤ exit →
        (∀ u ∈ Icc (0 : ℝ) e,
          physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u ∈ Icc (0 : ℝ) H) →
        (∀ u ∈ Icc (0 : ℝ) e,
          let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (b * u);
          weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h) →
        (∀ u ∈ Icc (0 : ℝ) e, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k,
          ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u) z - torusCenter‖ ≤
            2 * ρ * radScale R ρ k) →
        (∀ u ∈ Icc (0 : ℝ) e,
          let t := physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u;
          ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) (k + 1)) t)) 4‖ ≤
            ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * Chistory * ηctrl *
              Real.exp (-sigma * (exit - u))) →
        ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (b * e)‖ ≤
          (ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma) *
              Real.exp (-sigma * (exit - e)) +
            (C * ρ ^ 8) * e * Real.exp (b * sigma * e) := by
  obtain ⟨C, hC, hjoint⟩ := P.exists_eventually_actualFirstParent_coupled_material_forced_equation
    hb hb1.le (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨C, hC, ?_⟩
  intro s cA q T _ hs hcA hq hqE hT
  filter_upwards [hjoint (D := 0) hs hcA hq hqE hT (by norm_num), eventually_ge_atTop (0 : ℝ)] with ξ hjointξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro k S hS H hH Y hY e exit he heexit hwindow hcontrols hparticles hmoment
  let childTime := fun u : ℝ => physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u
  let scale : ℂ := (ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6
  let source := fun u : ℝ => momentN (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) (k + 1)) (childTime u))) 4
  let M := fun u : ℝ => source u / scale
  let W := fun u : ℝ => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (b * u)
  let F := fun u : ℝ => (ρ : ℂ) ^ 6 * Kstar *
    Complex.exp (4 * (((childTime u * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I) * M u
  let c : ℂ := (b : ℂ) * lamStar
  let A := ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl
  let ε := C * ρ ^ 8
  have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hb (k + 1))
  have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hrad : 0 < radScale R ρ (k + 1) := radScale_pos hR hρ (k + 1)
  have hscale : scale ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hAmp.ne')
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hrad.ne'))
  have hscaleNorm : ‖scale‖ = ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 := by
    simp only [scale, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hAmp, abs_of_pos hrad]
  have hscalePos : 0 < ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 := by positivity
  have hM (u : ℝ) (hu : u ∈ Icc (0 : ℝ) e) :
      ‖M u‖ ≤ Chistory * ηctrl * Real.exp (-sigma * (exit - u)) := by
    dsimp only [M]
    rw [norm_div, hscaleNorm]
    apply (div_le_iff₀ hscalePos).mpr
    simpa only [source, childTime, mul_assoc, mul_comm, mul_left_comm] using hmoment u hu
  have hMexact (u : ℝ) : scale * M u = source u := by
    dsimp only [M]
    field_simp [hscale] <;> ring
  have hclock (u : ℝ) :
      physicalTimeFromNormalized (ampScale A₀ b k) 0 (0 + b * u) = childTime u := by
    dsimp only [childTime, physicalTimeFromNormalized]
    rw [ampScale_succ_eq_div]
    field_simp [hAmpParent.ne', hb.ne'] <;> ring
  have hW : ∀ u ∈ Icc (0 : ℝ) e, ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt W (c * W u + F u + E) u := by
    intro u hu
    have hclose : ‖source u - (ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6 *
        Complex.exp (-(4 * ((0 : ℝ) : ℂ) * I)) * M u‖ ≤
        ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * (0 : ℝ) := by
      simpa only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one,
        ← hMexact u, scale, sub_self, norm_zero, le_refl]
    obtain ⟨E, hE, hd⟩ := hjointξ k S hS hH Y hY (childTime u) (hwindow u hu) 0 u 0
      (hclock u) (by simpa only [zero_add, one_mul] using (hcontrols u hu).1)
      (by simpa only [zero_add, one_mul] using (hcontrols u hu).2)
      (by simpa only [add_zero, mul_one] using hparticles u hu) 0 (by norm_num) (M u) hclose
    refine ⟨E, ?_, ?_⟩
    · simpa only [ε, add_zero, one_pow, mul_one, mul_zero] using hE
    · simpa only [W, F, c, zero_add, sub_zero] using hd
  have hF (u : ℝ) (hu : u ∈ Icc (0 : ℝ) e) :
      ‖F u‖ ≤ A * Real.exp (-sigma * (exit - u)) := by
    have hphase : ‖Complex.exp (4 * (((childTime u * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I)‖ = 1 := by
      rw [show 4 * (((childTime u * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ)) * I =
        (((4 * (childTime u * finiteAncestorAngularVelocity A₀ b k) : ℝ) : ℂ)) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    calc
      _ = ρ ^ 6 * ‖Kstar‖ * ‖M u‖ := by
        simp only [F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hphase, mul_one]
      _ ≤ ρ ^ 6 * ‖Kstar‖ * (Chistory * ηctrl * Real.exp (-sigma * (exit - u))) :=
        mul_le_mul_of_nonneg_left (hM u hu) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have hW0 : W 0 = 0 := by
    dsimp only [W]
    rw [mul_zero]
    exact P.actualCanonicalPrefix_initial_materialGrowing_zero hR hρ (Nat.le_succ k) le_rfl S Y hY
  have hc : c.re = b * sigma := by dsimp only [c]; simp [lamStar]
  have hc0 : 0 ≤ c.re := by rw [hc]; exact mul_nonneg hb.le sigma_pos.le
  have hgap : 0 < sigma - c.re := by
    rw [hc, show sigma - b * sigma = sigma * (1 - b) by ring]
    exact mul_pos sigma_pos (sub_pos.mpr hb1)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hbound := norm_linear_forced_history_le (σ := sigma) (D := exit)
    hc0 hgap hA0 hε he W F hW hF
  rw [hW0, norm_zero, zero_mul, zero_add, hc] at hbound
  exact hbound

theorem exists_eventually_actualFirstParent_coupled_physical_lookback_history
    {b Chistory ηctrl : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hChistory : 0 ≤ Chistory) (hηctrl : 0 ≤ ηctrl) :
    ∃ C > 0,
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        ∀ k : ℕ,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) (k + 1)) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ (Nat.le_succ k) S H Y →
        ∀ exit Lback d : ℝ, 0 ≤ Lback → Lback ≤ exit →
        let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
        entrance ≤ H →
        (∀ t ∈ Icc (0 : ℝ) entrance,
          let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t);
          weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h) →
        (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k,
          ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
        (∀ u ∈ Icc (0 : ℝ) (exit - Lback),
          let t := physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u;
          ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) (k + 1)) t)) 4‖ ≤
            ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * Chistory * ηctrl *
              Real.exp (-sigma * (exit - u))) →
        Real.exp (b * sigma * (Lback + d)) *
          ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (b * (exit - Lback))‖ ≤
          (ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma) *
              Real.exp (-(sigma - b * sigma) * Lback) * Real.exp (b * sigma * d) +
            (C * ρ ^ 8) * (exit - Lback) * Real.exp (b * sigma * (exit + d)) := by
  obtain ⟨C, hC, hpast⟩ := P.exists_eventually_actualFirstParent_coupled_past_history_bound
    hb hb1 hChistory hηctrl
  refine ⟨C, hC, ?_⟩
  intro s cA q T _ hs hcA hq hqE hT
  filter_upwards [hpast hs hcA hq hqE hT, eventually_ge_atTop (0 : ℝ)] with ξ hpastξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro k S hS H hH Y hY exit Lback d hLback hLexit hentranceH hcontrols hparticles hmoment
  let entrance := (exit - Lback) / ampScale A₀ b (k + 1)
  let childTime := fun u : ℝ => physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 u
  have hAmp : 0 < ampScale A₀ b (k + 1) := div_pos hA (pow_pos hb (k + 1))
  have hAmpParent : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have htime (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (exit - Lback)) : childTime u ∈ Icc (0 : ℝ) entrance := by
    change 0 ≤ 0 + u / ampScale A₀ b (k + 1) ∧
      0 + u / ampScale A₀ b (k + 1) ≤ (exit - Lback) / ampScale A₀ b (k + 1)
    simpa only [zero_add] using
      And.intro (div_nonneg hu.1 hAmp.le) (div_le_div_of_nonneg_right hu.2 hAmp.le)
  have hclock (u : ℝ) : ampScale A₀ b k * childTime u = b * u := by
    dsimp only [childTime, physicalTimeFromNormalized]
    rw [ampScale_succ_eq_div]
    field_simp [hAmpParent.ne', hb.ne'] <;> ring
  have hbound := hpastξ k S hS hH Y hY (exit - Lback) exit (sub_nonneg.mpr hLexit)
    (sub_le_self _ hLback)
    (by intro u hu; exact ⟨(htime u hu).1, (htime u hu).2.trans hentranceH⟩)
    (by
      intro u hu
      have hc := hcontrols (childTime u) (htime u hu)
      rw [hclock] at hc
      exact hc)
    (by intro u hu; exact hparticles (childTime u) (htime u hu)) hmoment
  have hphase : Real.exp (b * sigma * (Lback + d)) *
      Real.exp (-sigma * (exit - (exit - Lback))) =
      Real.exp (-(sigma - b * sigma) * Lback) * Real.exp (b * sigma * d) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have herr : Real.exp (b * sigma * (Lback + d)) * Real.exp (b * sigma * (exit - Lback)) =
      Real.exp (b * sigma * (exit + d)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (b * sigma * (Lback + d)) *
        ((ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma) *
          Real.exp (-sigma * (exit - (exit - Lback))) +
            (C * ρ ^ 8) * (exit - Lback) * Real.exp (b * sigma * (exit - Lback))) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (ρ ^ 6 * ‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma) *
        (Real.exp (b * sigma * (Lback + d)) * Real.exp (-sigma * (exit - (exit - Lback)))) +
          (C * ρ ^ 8) * (exit - Lback) *
            (Real.exp (b * sigma * (Lback + d)) * Real.exp (b * sigma * (exit - Lback))) := by ring
    _ = _ := by rw [hphase, herr]; ring

end CircularMaterialTransferProfile
end Euler2D

end
