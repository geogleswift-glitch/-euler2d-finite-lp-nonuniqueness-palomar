module

public import RequestProject.Euler.CircularActualRotatingMaterialDynamics
public import RequestProject.Euler.CircularCoupledFiniteEulerUniformVectorCorrection
public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness

/-! The SAME original normalized Euler velocity equals its true material
self velocity plus actual residuals, with R=rho^10, A0=cA*(1+xi).
The resulting residual error is uniform in cutoff, layer and time. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

attribute [local irreducible] finiteBaseCurlL2 finiteBaseLp
  BoundedEulerParticleSystem.rotatingNormalizedVelocityAt
  BoundedEulerParticleSystem.rotatingNormalizedPlanarLabelSource
  BoundedEulerParticleSystem.rotatingNormalizedRelativeHomeomorph
  planarMaterialLabelVelocity kernelK complexPhysicalPlane

run_cmd do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "imports loaded"

theorem eventually_actualFinite_coupled_rotating_velocity_eq_material_add_residual
    {s cA b q T B : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance t : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ∀ θentry θtarget : ℝ, ∀ z : R2, ‖z‖ ≤ B →
      S.rotatingNormalizedVelocityAt (ampScale A₀ b k) (radScale R ρ k)
          (finiteAncestorAngularVelocity A₀ b k) t θtarget z =
        planarMaterialLabelVelocity kernelK
          (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k)
            (ampScale A₀ b k) (radScale R ρ k) θentry entrance)
          (S.rotatingNormalizedRelativeHomeomorph (radScale R ρ k) (radScale_pos hR hρ k).ne'
            entrance he t ht θentry θtarget) z +
        P.normalizedFiniteEulerResidual s A₀ b R ρ N k hkN S t θtarget z := by
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "field: body entered"
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨Cl, hCl, hlocalize⟩ := P.exists_uniform_actualFinite_boxed_label_eq_singlePlanar
  let dc := 4 * (Cs + Cl) * cA * T
  let dsupport := fun ξ : ℝ => B + 2 + dc * (1 + ξ)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hdRlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dc (B + 1 + dc) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hCoreLimit : Tendsto (fun ξ : ℝ => B * Real.exp (-ξ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul B
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "field: scale limits ready"
  filter_upwards [he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    he.eventually (eventually_lt_nhds (half_pos hb)),
    hdRlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hCoreLimit.eventually (eventually_lt_nhds cellA_pos), eventually_ge_atTop (0 : ℝ)]
    with ξ hhalf hρhalf hdρ hBρ hξ
  try dsimp only
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let d := B + 2 + 4 * (Cs + Cl) * A₀ * T
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρ1 : ρ ≤ 1 := hhalf.le.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hhalf.le
  have hρb : ρ < b := hρhalf.trans (half_lt_self hb)
  have hcatS : 0 ≤ Cs * A₀ * T := mul_nonneg (mul_nonneg hCs.le hA.le) hT
  have hcatL : 0 ≤ Cl * A₀ * T := mul_nonneg (mul_nonneg hCl.le hA.le) hT
  have hd : 0 < d := by dsimp only [d]; nlinarith only [hB, hcatS, hcatL]
  have hBd : B ≤ d := by dsimp only [d]; nlinarith only [hcatS, hcatL]
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dc, d, A₀]; ring
  rw [hdeq] at hdρ
  have hdρ1 : d * R < 1 := hdρ.trans (by norm_num : (1 / 16 : ℝ) < 1)
  have hden : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith only [hρhalf])
    linarith only [hh]
  have hdiv (C : ℝ) (hC : 0 ≤ C) : C * A₀ / (1 - ρ / b) ≤ 2 * C * A₀ := by
    calc
      _ ≤ C * A₀ / (1 / 2) := div_le_div_of_nonneg_left (mul_nonneg hC hA.le) (by norm_num) hden
      _ = _ := by ring
  have hDriftSξ : 5 / 4 + (Cs * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right (hdiv Cs hCs.le) hT
    dsimp only [d]
    nlinarith only [hh, hcatS, hcatL, hB]
  have hDriftLξ : 5 / 4 + (Cl * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right (hdiv Cl hCl.le) hT
    dsimp only [d]
    nlinarith only [hh, hcatS, hcatL, hB]
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "field: support budgets ready"
  intro N k hkN S harea entrance t he ht θentry θtarget z hz
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "field: actual support"
  have hsupp := hsupport (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
    (T := T) (H := T) (c := d) hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hT le_rfl
    hDriftSξ hdρ1 N S t ht
  have hlabel := hlocalize (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
    (T := T) (H := T) (c := d) hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hT le_rfl
    hDriftLξ hdρ1 N S t ht k
  have hquery : radScale R ρ k * ‖z‖ ≤ d * R := by
    have hrk : 0 ≤ radScale R ρ k := (radScale_pos hR hρ k).le
    have hrkmax : radScale R ρ k ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
    calc
      _ ≤ radScale R ρ k * d := mul_le_mul_of_nonneg_left (hz.trans hBd) hrk
      _ ≤ R * d := mul_le_mul_of_nonneg_right hrkmax hd.le
      _ = _ := mul_comm _ _
  have hcore (j : Fin k) : radScale R ρ k * ‖z‖ ≤ cellA * radScale R ρ j := by
    have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
    have hrk : 0 ≤ radScale R ρ k := (radScale_pos hR hρ k).le
    have hratio := radScale_ratio_eq_pow hR.ne' hρ.ne' j.isLt.le
    have hp : ρ ^ (k - (j : ℕ)) ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (show 1 ≤ k - (j : ℕ) by omega)
    have hrad : radScale R ρ k ≤ ρ * radScale R ρ j := (div_le_iff₀ hrj).mp (hratio.trans_le hp)
    have hsep := mul_le_mul_of_nonneg_right hBρ.le hrj.le
    calc
      _ ≤ radScale R ρ k * B := mul_le_mul_of_nonneg_left hz hrk
      _ ≤ (ρ * radScale R ρ j) * B := mul_le_mul_of_nonneg_right hrad hB
      _ ≤ _ := by nlinarith only [hsep]
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "field: final actual equation"
  exact P.actualFinite_rotating_velocity_eq_material_add_residual
    (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q) (T := T)
    (entrance := entrance) (t := t) (a := d * R) hs hA hb hR hRmax hρ hρ1 hq hqE
    N k hkN S he ht (harea entrance he).2 (harea t ht).1 hdρ.le hsupp hlabel θentry θtarget z hquery hcore

theorem eventually_actualFinite_coupled_normalizedEulerResidual_le
    {s cA b q T c C₀ K B ε : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      ∀ {δ : ℝ} (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s R ρ N
        (finiteAncestorPointwiseIndex hkN j) S t c δ),
      (∀ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) -
          (G j).reference (l, i)‖ ≤ radScale R ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ θ : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖P.normalizedFiniteEulerResidual s A₀ b R ρ N k hkN S t θ z‖ ≤ ε := by
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "residual: body entered"
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  have hancestor := P.eventually_normalizedFiniteAncestorResidual_le hb hb1 hc hC₀ hK hB hε3
  have hinner := P.eventually_normalizedFiniteInnerVelocity_le hb hε3
  have htorus := P.eventually_actualFinite_coupled_normalizedCorrectionLabelVelocity_le hs hcA hb hb1 hq hqE hT hB hε3
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [hancestor, hinner, htorus,
    he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop (0 : ℝ)]
    with ξ ha hi hcorr hhalf hξ
  try dsimp only at ha hi hcorr ⊢
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hρ1 : ρ ≤ 1 := hhalf.le.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hhalf.le
  intro N k hkN S hS t ht δ G hql θ z hz
  have ha' := ha (s := s) (A₀ := A₀) (R := R) hs hA hR hRmax N k hkN S t ht G hql θ z hz
  have hi' := hi (s := s) (A₀ := A₀) (R := R) hs hA hR hRmax N k S t θ z
  have hc' := hcorr N S hS t ht k θ z hz
  unfold normalizedFiniteEulerResidual
  calc
    _ ≤ ‖P.normalizedFiniteAncestorResidual s A₀ b R ρ N k hkN S t θ z‖ +
        ‖P.normalizedFiniteInnerVelocity s A₀ b R ρ N k S t θ z‖ +
        ‖S.normalizedCorrectionLabelVelocity (ampScale A₀ b k) (radScale R ρ k) t θ z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε := by linarith only [ha', hi', hc']

theorem eventually_actualFinite_coupled_rotating_material_velocity_error_le
    {s cA b q T c C₀ K B ε : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance t : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ∀ {δ : ℝ} (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s R ρ N
        (finiteAncestorPointwiseIndex hkN j) S t c δ),
      (∀ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) -
          (G j).reference (l, i)‖ ≤ radScale R ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ θentry θtarget : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖S.rotatingNormalizedVelocityAt (ampScale A₀ b k) (radScale R ρ k)
            (finiteAncestorAngularVelocity A₀ b k) t θtarget z -
          planarMaterialLabelVelocity kernelK
            (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k)
              (ampScale A₀ b k) (radScale R ρ k) θentry entrance)
            (S.rotatingNormalizedRelativeHomeomorph (radScale R ρ k) (radScale_pos hR hρ k).ne'
              entrance he t ht θentry θtarget) z‖ ≤ ε := by
  run_tac do IO.FS.writeFile "F:/internal-final_aristotle/verification/CoupledRotatingDynamics-phase.txt" "error: body entered"
  have hfield := P.eventually_actualFinite_coupled_rotating_velocity_eq_material_add_residual hs hcA hb hq hqE hT hB
  have herror := P.eventually_actualFinite_coupled_normalizedEulerResidual_le hs hcA hb hb1 hq hqE hT hc hC₀ hK hB hε
  filter_upwards [hfield, herror] with ξ hξ hεξ
  try dsimp only at hξ hεξ ⊢
  intro N k hkN S hS harea entrance t he ht δ G hql θentry θtarget z hz
  rw [hξ N k hkN S harea entrance t he ht θentry θtarget z hz, add_sub_cancel_left]
  exact hεξ N k hkN S hS t ht G hql θtarget z hz

end CircularMaterialTransferProfile
end Euler2D

end
