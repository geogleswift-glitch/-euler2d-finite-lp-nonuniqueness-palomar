module

public import RequestProject.Euler.CircularFiniteRealRadialFeedback
public import RequestProject.Euler.CircularFiniteOuterInteractionRow
public import RequestProject.Euler.RotatingNormalizedFiniteParticleTransport
public import RequestProject.Euler.Envelope

/-! A true outer label's residual velocity is controlled at every
interior particle point. This does not require a smooth contour for the
current label being observed. Only the actual ancestor geometry enters. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 5500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem norm_phaseFiniteContourPatchPerturbation_velocity_le_cubic
    {γ : ℝ≥0} {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (Z Z₀ : ι → ContourC1Space γ) (d β : ι → ℝ)
    {c q rl : ℝ} (hc : 0 < c) (hrl : 0 < rl) (hd : ∀ i, 0 < d i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (d i * rl))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ d i * rl / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ rl * q)
    (hcore : ∀ i, c ≤ 3 * d i / 4)
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z i) (θ + Real.pi / 2) = I * ContourC1Space.lift γ (Z i) θ)
    {x : ℂ} (hx : ‖x‖ ≤ c * rl / 2) :
    ‖velocityC (phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl)) x‖ ≤
      (32 / (15 * c ^ 4) * ∑ i, |g i| * d i) * q * ‖x‖ ^ 3 / rl ^ 2 := by
  have hi := integrable_phaseFiniteContourPatchPerturbation g Z Z₀ (fun i => d i * rl)
    (fun i => mul_pos (hd i) hrl) href β hsmall
  have hz : ∀ y : ℂ, ‖y‖ < c * rl →
      phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) y = 0 := by
    intro y hy
    exact phaseFiniteContourPatchPerturbation_zero_core_of_tube
      g Z Z₀ d β hc hrl hd href hsmall hq hcore hy
  have hm := integral_abs_phaseFiniteContourPatchPerturbation_le_scaled
    g Z Z₀ d β hc hrl hd href hsmall hq hcore
  have hp := outer_perturbation_field (mul_pos hc hrl) hi
    (phaseFiniteContourPatchPerturbation_fourfold g Z (fun i => d i * rl) hrot) hz hx
  refine hp.trans ((mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq ?_)
  field_simp [hc.ne', hrl.ne', Real.pi_ne_zero]
  <;> ring

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem norm_finiteOuterLabelComplexPerturbation_velocity_le_cubic
    {s A₀ b R ρ c δ ql : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1)) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N j S t c δ)
    (hql : ∀ i, ‖contourParameterShiftC1 (G.shifts (j, i)) (G.contours (j, i)) -
      G.reference (j, i)‖ ≤ radScale R ρ j * ql)
    (hc : 0 < c) {x : ℂ} (hx : ‖x‖ ≤ c * radScale R ρ j / 2) :
    ‖velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t) x‖ ≤
      (32 / (15 * c ^ 4) * circularRadialPerturbationWeight) * ampScale A₀ b j *
        ql * ‖x‖ ^ 3 / radScale R ρ j ^ 2 := by
  have he := P.finiteOuterLabelComplexPerturbation_eq_phaseContours (A₀ := A₀) (b := b)
    hs hR hRmax hρ hρ1 N j S G.contours t ht
    (G.initial_box j le_rfl) (G.current_box j le_rfl) (G.images j le_rfl)
  rw [he]
  have hh := norm_phaseFiniteContourPatchPerturbation_velocity_le_cubic
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i)) (fun i => G.contours (j, i))
    (fun i => G.reference (j, i)) circularContourRadii (fun i => G.shifts (j, i))
    hc (radScale_pos hR hρ j) (fun i => (circularContourRadii_bounds i).1)
    (G.reference_lift j le_rfl) (G.quarter_tube j le_rfl) hql G.core (G.fourfold j le_rfl) hx
  have hAj : 0 < ampScale A₀ b j := div_pos hA (pow_pos hb j)
  rw [finiteCircularInterfaceRadialWeight_eq, abs_of_pos hAj] at hh
  exact hh.trans_eq (by ring)

def normalizedFiniteOuterLabelVelocity (s A₀ b R ρ : ℝ) (N : ℕ) (j : Fin (N + 1)) (k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t θ : ℝ) (z : R2) : R2 :=
  planarRigidRotation (-θ)
    ((ampScale A₀ b k * radScale R ρ k)⁻¹ •
      complexPhysicalPlane (velocityC (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N j S t)
        (complexPhysicalPlane.symm (radScale R ρ k • planarRigidRotation θ z))))

theorem norm_normalizedFiniteOuterLabelVelocity_le
    {s A₀ b R ρ c δ ql : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1)) (k : ℕ) (hjk : (j : ℕ) ≤ k)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N j S t c δ)
    (hql : ∀ i, ‖contourParameterShiftC1 (G.shifts (j, i)) (G.contours (j, i)) -
      G.reference (j, i)‖ ≤ radScale R ρ j * ql)
    (hc : 0 < c) (θ : ℝ) (z : R2)
    (hx : radScale R ρ k * ‖z‖ ≤ c * radScale R ρ j / 2) :
    ‖P.normalizedFiniteOuterLabelVelocity s A₀ b R ρ N j k S t θ z‖ ≤
      (32 / (15 * c ^ 4) * circularRadialPerturbationWeight) *
        b ^ (k - (j : ℕ)) * ρ ^ (2 * (k - (j : ℕ))) * ql * ‖z‖ ^ 3 := by
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hAk : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hAr : 0 < ampScale A₀ b k * radScale R ρ k := mul_pos hAk hrk
  have hnorm : ‖complexPhysicalPlane.symm (radScale R ρ k • planarRigidRotation θ z)‖ =
      radScale R ρ k * ‖z‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hrk,
      LinearIsometryEquiv.norm_map]
  have hh := P.norm_finiteOuterLabelComplexPerturbation_velocity_le_cubic
    (x := complexPhysicalPlane.symm (radScale R ρ k • planarRigidRotation θ z))
    hs hA hb hR hRmax hρ hρ1 N j S t ht G hql hc
    (by simpa only [hnorm] using hx)
  rw [hnorm] at hh
  rw [normalizedFiniteOuterLabelVelocity, LinearIsometryEquiv.norm_map, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hAr, LinearIsometryEquiv.norm_map]
  refine (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hAr.le)).trans_eq ?_
  calc
    _ = (32 / (15 * c ^ 4) * circularRadialPerturbationWeight) *
        ((ampScale A₀ b j * (radScale R ρ k / radScale R ρ j) ^ 2) / ampScale A₀ b k) *
        ql * ‖z‖ ^ 3 := by
      field_simp [hAr.ne', hAk.ne', hrj.ne', hrk.ne']
      <;> ring
    _ = _ := by
      rw [outer_contour_current_clock_identity hA.ne' hb.ne' hR.ne' hρ.ne' hjk hjk]
      ring

def finiteAncestorPointwiseIndex {N k : ℕ} (hkN : k ≤ N) (j : Fin k) : Fin (N + 1) :=
  ⟨j, j.isLt.trans_le (Nat.le_succ_of_le hkN)⟩

def normalizedFiniteAncestorResidual (s A₀ b R ρ : ℝ) (N k : ℕ) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t θ : ℝ) (z : R2) : R2 :=
  ∑ j : Fin k, P.normalizedFiniteOuterLabelVelocity s A₀ b R ρ N
    (finiteAncestorPointwiseIndex hkN j) k S t θ z

theorem norm_normalizedFiniteAncestorResidual_le
    {s A₀ b R ρ c δ C₀ K : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hζ : C₀ * ρ ^ 8 < 1)
    (N k : ℕ) (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s R ρ N
      (finiteAncestorPointwiseIndex hkN j) S t c δ)
    (hql : ∀ (j : Fin k) i,
      let l := finiteAncestorPointwiseIndex hkN j
      ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) -
        (G j).reference (l, i)‖ ≤
          radScale R ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K))
    (hc : 0 < c) (θ : ℝ) (z : R2)
    (hsep : ∀ j : Fin k, radScale R ρ k * ‖z‖ ≤ c * radScale R ρ j / 2) :
    ‖P.normalizedFiniteAncestorResidual s A₀ b R ρ N k hkN S t θ z‖ ≤
      (32 / (15 * c ^ 4) * circularRadialPerturbationWeight) * b * K * ‖z‖ ^ 3 *
        ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8)) := by
  let ζ := C₀ * ρ ^ 8
  let C := 32 / (15 * c ^ 4) * circularRadialPerturbationWeight
  let A := C * b * K * ‖z‖ ^ 3
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hζ0 : 0 ≤ ζ := by dsimp only [ζ]; positivity
  have hAnonneg : 0 ≤ A := by dsimp only [A]; positivity
  have hpow (n : ℕ) : ρ ^ (2 * n) * (C₀ * ρ ^ 6) ^ n = ζ ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    dsimp only [ζ]
    ring
  have hterm (j : Fin k) :
      ‖P.normalizedFiniteOuterLabelVelocity s A₀ b R ρ N
        (finiteAncestorPointwiseIndex hkN j) k S t θ z‖ ≤ A * ζ ^ (k - (j : ℕ)) := by
    have hjk : (finiteAncestorPointwiseIndex hkN j : ℕ) ≤ k := j.isLt.le
    have hh := P.norm_normalizedFiniteOuterLabelVelocity_le hs hA hb hR hRmax hρ hρ1
      N (finiteAncestorPointwiseIndex hkN j) k hjk S t ht (G j) (hql j) hc θ z (hsep j)
    have hbpow : b ^ (k - (j : ℕ)) ≤ b := by
      simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - (j : ℕ) by omega)
    calc
      _ ≤ C * b ^ (k - (j : ℕ)) * ρ ^ (2 * (k - (j : ℕ))) *
          ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K) * ‖z‖ ^ 3 := hh
      _ = C * b ^ (k - (j : ℕ)) * ζ ^ (k - (j : ℕ)) * K * ‖z‖ ^ 3 := by
        calc
          _ = C * b ^ (k - (j : ℕ)) *
              (ρ ^ (2 * (k - (j : ℕ))) * (C₀ * ρ ^ 6) ^ (k - (j : ℕ))) * K * ‖z‖ ^ 3 := by ring
          _ = _ := by rw [hpow]
      _ ≤ C * b * ζ ^ (k - (j : ℕ)) * K * ‖z‖ ^ 3 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbpow hC)
            (pow_nonneg hζ0 _)) hK) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have hgeo := sum_pow_le_of_injOn (Finset.univ : Finset (Fin k))
    (fun j => k - (j : ℕ))
    (fun a _ b' _ hab => by
      have ha := a.isLt
      have hb' := b'.isLt
      change k - (a : ℕ) = k - (b' : ℕ) at hab
      exact Fin.ext (by omega))
    (fun j _ => by
      have hj := j.isLt
      change 1 ≤ k - (j : ℕ)
      omega) hζ0 hζ
  unfold normalizedFiniteAncestorResidual
  calc
    _ ≤ ∑ j : Fin k, ‖P.normalizedFiniteOuterLabelVelocity s A₀ b R ρ N
        (finiteAncestorPointwiseIndex hkN j) k S t θ z‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin k, A * ζ ^ (k - (j : ℕ)) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = A * ∑ j : Fin k, ζ ^ (k - (j : ℕ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (ζ / (1 - ζ)) := mul_le_mul_of_nonneg_left hgeo hAnonneg
    _ = _ := rfl

theorem eventually_normalizedFiniteAncestorResidual_le
    {b c C₀ K B ε : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hc : 0 < c)
    (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      ∀ {s A₀ R : ℝ}, s ≤ 0 → 0 < A₀ → 0 < R → R ≤ 1 / 2 →
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ {f : Lp ℝ 2 μT} {T : ℝ}
        (S : BoundedEulerParticleSystem f T) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      ∀ {δ : ℝ} (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s R ρ N
        (finiteAncestorPointwiseIndex hkN j) S t c δ),
      (∀ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) -
          (G j).reference (l, i)‖ ≤ radScale R ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ θ : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖P.normalizedFiniteAncestorResidual s A₀ b R ρ N k hkN S t θ z‖ ≤ ε := by
  let C := 32 / (15 * c ^ 4) * circularRadialPerturbationWeight
  let M := C * b * K * B ^ 3
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have he : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hzeta : Tendsto (fun ξ : ℝ => C₀ * Real.exp (-ξ) ^ 8) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (8 : ℕ) ≠ 0), mul_zero] using (he.pow 8).const_mul C₀
  have hden : Tendsto (fun ξ : ℝ => 1 - C₀ * Real.exp (-ξ) ^ 8) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hzeta
  have hlim : Tendsto (fun ξ : ℝ => M * ((C₀ * Real.exp (-ξ) ^ 8) /
      (1 - C₀ * Real.exp (-ξ) ^ 8))) atTop (𝓝 0) := by
    simpa only [Pi.div_def, zero_div, mul_zero] using
      (hzeta.div hden (by norm_num : (1 : ℝ) ≠ 0)).const_mul M
  have hlin : Tendsto (fun ξ : ℝ => 2 * B * Real.exp (-ξ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (2 * B)
  filter_upwards [he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hzeta.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hlin.eventually (eventually_lt_nhds hc), hlim.eventually (eventually_lt_nhds hε)]
    with ξ hρ1 hζ hsepSmall hsmall
  try dsimp only
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  intro s A₀ R hs hA hR hRmax N k hkN f T S t ht δ G hql θ z hz
  have hsep (j : Fin k) : radScale R ρ k * ‖z‖ ≤ c * radScale R ρ j / 2 := by
    have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
    have hrk : 0 < radScale R ρ k := radScale_pos hR hρ k
    have hratio := radScale_ratio_eq_pow hR.ne' hρ.ne' j.isLt.le
    have hp : ρ ^ (k - (j : ℕ)) ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1.le (show 1 ≤ k - (j : ℕ) by omega)
    have hrad : radScale R ρ k ≤ ρ * radScale R ρ j :=
      (div_le_iff₀ hrj).mp (hratio.trans_le hp)
    have hsepScaled := mul_le_mul_of_nonneg_right hsepSmall.le hrj.le
    calc
      _ ≤ radScale R ρ k * B := mul_le_mul_of_nonneg_left hz hrk.le
      _ ≤ (ρ * radScale R ρ j) * B := mul_le_mul_of_nonneg_right hrad hB
      _ ≤ _ := by nlinarith only [hsepScaled]
  have hh := P.norm_normalizedFiniteAncestorResidual_le hs hA hb hb1 hR hRmax hρ hρ1.le
    hC₀ hK hζ N k hkN S t ht G hql hc θ z hsep
  have hζnn : 0 ≤ (C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8) :=
    div_nonneg (mul_nonneg hC₀.le (pow_nonneg hρ.le 8)) (sub_nonneg.mpr hζ.le)
  refine hh.trans (le_trans ?_ hsmall.le)
  change C * b * K * ‖z‖ ^ 3 * ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8)) ≤
    M * ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hz 3) (by positivity : 0 ≤ C * b * K)) hζnn

end CircularMaterialTransferProfile
end Euler2D

end
