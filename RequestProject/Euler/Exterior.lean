module

public import Mathlib

/-!
# The exterior fourth-mode formula (Lemma `nt:lem:exterior`)

We identify `ℝ²` with `ℂ`. For a real vorticity `ω` the planar Biot–Savart velocity is
`u(z) = u₁ + i u₂ = ∫ ω(w) · i(z - w)/(2π|z - w|²) dw` (`velocityC`), i.e. `u = K * ω` with
`K(x) = Jx/(2π|x|²)` and `J` = multiplication by `i`. Its radial component at `z = r e^{iθ}` is
`u_r(r,θ) = Re(u(z) e^{-iθ})` (`radialVel`). Put `N_m = ∫ \bar z^m ω(z) dz` (`momentN`).

**Lemma (`nt:lem:exterior`).** If `ω` is integrable, vanishes outside `B̄_L`, has zero mass and
is fourfold symmetric (`ω(iz) = ω(z)`), then for every `r > L` the series
`Σ_{j≥1} (i/2π) N_{4j} r^{-4j-1} e^{4ijθ}` converges and
`u_r(r,θ) = Re(Σ_{j≥1} (i/2π) N_{4j} r^{-4j-1} e^{4ijθ})`.

In particular only the modes `e^{4ijθ}`, `j ≥ 1`, occur, and the fourth mode has amplitude
`i N₄/(2π r⁵)`.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate

namespace Euler2D

/-- The planar Biot–Savart velocity `u = u₁ + i u₂` of a real vorticity `ω`, in complex notation. -/
noncomputable def velocityC (ω : ℂ → ℝ) (z : ℂ) : ℂ :=
  ∫ w, (ω w : ℂ) * (I * (z - w) / (2 * Real.pi * ‖z - w‖ ^ 2))

/-- The radial velocity `u_r(r,θ) = Re(u(re^{iθ}) e^{-iθ})`. -/
noncomputable def radialVel (ω : ℂ → ℝ) (r θ : ℝ) : ℝ :=
  (velocityC ω (r * exp (θ * I)) * exp (-(θ * I))).re

/-- The complex moments `N_m = ∫ \bar z^m ω(z) dz`. -/
noncomputable def momentN (ω : ℂ → ℝ) (m : ℕ) : ℂ := ∫ w, (ω w : ℂ) * conj w ^ m

/-- The holomorphic moments `M_m = ∫ z^m ω(z) dz = conj N_m`. -/
noncomputable def momentM (ω : ℂ → ℝ) (m : ℕ) : ℂ := ∫ w, (ω w : ℂ) * w ^ m

lemma conj_momentM (ω : ℂ → ℝ) (m : ℕ) : conj (momentM ω m) = momentN ω m := by
  rw [momentM, momentN, ← integral_conj]
  congr 1; funext w
  simp [map_pow]

/-- Complex Biot–Savart law: `u₁ - i u₂ = -(i/2π) ∫ ω(w)/(z - w) dw`. -/
lemma conj_velocityC (ω : ℂ → ℝ) (z : ℂ) :
    conj (velocityC ω z) = -(I / (2 * Real.pi)) * ∫ w, (ω w : ℂ) * (z - w)⁻¹ := by
  rw [velocityC, ← integral_conj, ← integral_const_mul]
  congr 1; funext w
  rcases eq_or_ne z w with rfl | hzw
  · simp
  have ha : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hn : (‖z - w‖ : ℂ) ^ 2 = (z - w) * conj (z - w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : conj (z - w) ≠ 0 := (map_ne_zero _).mpr ha
  simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_pow, map_ofNat]
  rw [hn]
  field_simp

/-- Multipole expansion of `∫ ω(w)/(z - w)` outside the support. -/
lemma hasSum_cauchy_moments {ω : ℂ → ℝ} {L : ℝ} (hω : Integrable ω)
    (hsupp : ∀ w, L < ‖w‖ → ω w = 0) {z : ℂ} (hz : L < ‖z‖) :
    HasSum (fun m : ℕ => momentM ω m * (z ^ (m + 1))⁻¹) (∫ w, (ω w : ℂ) * (z - w)⁻¹) := by
  rcases lt_or_ge L 0 with hL | hL
  · have h0 : ∀ w, ω w = 0 := fun w => hsupp w (hL.trans_le (norm_nonneg w))
    simp [momentM, h0]
  have hzpos : 0 < ‖z‖ := hL.trans_lt hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  set F : ℕ → ℂ → ℂ := fun m w => (ω w : ℂ) * w ^ m * (z ^ (m + 1))⁻¹ with hF
  have hbound : ∀ m w, ‖F m w‖ ≤ ‖ω w‖ * (L ^ m / ‖z‖ ^ (m + 1)) := by
    intro m w
    by_cases hw : ω w = 0
    · simp [hF, hw]
    have hwL : ‖w‖ ≤ L := not_lt.mp fun h => hw (hsupp w h)
    simp only [hF, norm_mul, norm_inv, norm_pow, Complex.norm_real]
    rw [mul_assoc, div_eq_mul_inv]
    gcongr
  have hmeas : ∀ m, AEStronglyMeasurable (F m) volume := fun m =>
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hω.1).mul
      (continuous_pow m).aestronglyMeasurable).mul aestronglyMeasurable_const
  have hint : ∀ m, Integrable (F m) := fun m =>
    Integrable.mono' (hω.norm.mul_const _) (hmeas m) (Filter.Eventually.of_forall (hbound m))
  have hsum : Summable fun m => ∫ w, ‖F m w‖ := by
    have hq : L / ‖z‖ < 1 := (div_lt_one hzpos).mpr hz
    have hg : Summable fun m : ℕ => (∫ w, ‖ω w‖) * ‖z‖⁻¹ * (L / ‖z‖) ^ m :=
      (summable_geometric_of_lt_one (div_nonneg hL hzpos.le) hq).mul_left _
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun w => norm_nonneg _) (fun m => ?_) hg
    calc ∫ w, ‖F m w‖ ≤ ∫ w, ‖ω w‖ * (L ^ m / ‖z‖ ^ (m + 1)) :=
          integral_mono (hint m).norm (hω.norm.mul_const _) (hbound m)
      _ = (∫ w, ‖ω w‖) * ‖z‖⁻¹ * (L / ‖z‖) ^ m := by
          rw [integral_mul_const, div_pow, pow_succ]
          field_simp
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have hterm : ∀ m, ∫ w, F m w = momentM ω m * (z ^ (m + 1))⁻¹ := fun m => by
    simp only [hF, momentM]; rw [integral_mul_const]
  have hpt : ∀ w, ∑' m, F m w = (ω w : ℂ) * (z - w)⁻¹ := by
    intro w
    by_cases hw : ω w = 0
    · simp [hF, hw]
    have hwL : ‖w‖ ≤ L := not_lt.mp fun h => hw (hsupp w h)
    have hq : ‖w / z‖ < 1 := by
      rw [norm_div, div_lt_one hzpos]; exact hwL.trans_lt hz
    have hg := (hasSum_geometric_of_norm_lt_one hq).mul_right z⁻¹
    have hg' : HasSum (fun m => F m w) ((ω w : ℂ) * (z - w)⁻¹) := by
      convert hg.mul_left (ω w : ℂ) using 1
      · funext m; simp only [hF, div_pow, pow_succ]; field_simp
      · have hzw : z - w ≠ 0 := by
          intro h; rw [sub_eq_zero] at h; rw [h] at hz; linarith
        have h1 : (1 : ℂ) - w / z ≠ 0 := by
          rw [one_sub_div hz0]; exact div_ne_zero hzw hz0
        field_simp
    exact hg'.tsum_eq
  simp_rw [hterm, hpt] at key
  exact key

/-- Fourfold symmetry kills all moments `M_m` with `4 ∤ m`. -/
lemma momentM_eq_zero_of_not_dvd {ω : ℂ → ℝ} (hsym : ∀ w, ω (I * w) = ω w) {m : ℕ}
    (hm : ¬ 4 ∣ m) : momentM ω m = 0 := by
  have hI : ((Circle.exp (Real.pi / 2) : Circle) : ℂ) = I := by
    rw [Circle.coe_exp]; push_cast
    rw [show (Real.pi : ℂ) / 2 * I = (Real.pi / 2 : ℂ) * I by ring, Complex.exp_pi_div_two_mul_I]
  have hrot : ∀ f : ℂ → ℂ, ∫ w, f (I * w) = ∫ w, f w := by
    intro f
    have h := (rotation (Circle.exp (Real.pi / 2))).measurePreserving.integral_comp
      (rotation (Circle.exp (Real.pi / 2))).toHomeomorph.measurableEmbedding f
    simpa [rotation_apply, hI] using h
  have key : momentM ω m = I ^ m * momentM ω m := by
    conv_lhs => rw [momentM, ← hrot]
    rw [momentM, ← integral_const_mul]
    congr 1; funext w
    rw [hsym, mul_pow]; ring
  have hIm : I ^ m ≠ 1 := by
    rw [← Nat.mod_add_div m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]
    have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h0 : m % 4 ≠ 0 := fun h => hm (Nat.dvd_of_mod_eq_zero h)
    interval_cases (m % 4)
    · contradiction
    · simp [Complex.ext_iff]
    · simp [pow_two]; norm_num
    · simp [pow_three, Complex.ext_iff]
  have : (1 - I ^ m) * momentM ω m = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hIm
  · exact h

/-- **Lemma (`nt:lem:exterior`).** For an integrable, real, zero-mass, fourfold-symmetric
vorticity vanishing outside `B̄_L`, and `r > L`, the series
`Σ_{j≥1} (i/2π) N_{4j} r^{-4j-1} e^{4ijθ}` converges and its real part is the radial
velocity `u_r(r,θ)`. -/
theorem exterior_fourth_mode {ω : ℂ → ℝ} {L : ℝ} (hω : Integrable ω)
    (hsupp : ∀ w, L < ‖w‖ → ω w = 0) (hmass : ∫ w, ω w = 0) (hsym : ∀ w, ω (I * w) = ω w)
    {r : ℝ} (hr : L < r) (θ : ℝ) :
    Summable (fun j : ℕ => I / (2 * Real.pi) * momentN ω (4 * (j + 1)) *
        ((r : ℂ) ^ (4 * (j + 1) + 1))⁻¹ * exp ((4 * (j + 1) : ℕ) * θ * I)) ∧
      radialVel ω r θ = (∑' j : ℕ, I / (2 * Real.pi) * momentN ω (4 * (j + 1)) *
        ((r : ℂ) ^ (4 * (j + 1) + 1))⁻¹ * exp ((4 * (j + 1) : ℕ) * θ * I)).re := by
  set z : ℂ := (r : ℂ) * exp (θ * I) with hzdef
  have hzn : ‖z‖ = |r| := by
    rw [hzdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hz : L < ‖z‖ := hzn ▸ hr.trans_le (le_abs_self r)
  have h1 := hasSum_cauchy_moments hω hsupp hz
  have h2 := (h1.mul_left (-(I / (2 * Real.pi)))).mul_right (exp (θ * I))
  have h3 := Complex.hasSum_conj'.mpr h2
  set g : ℕ → ℂ := fun m => I / (2 * Real.pi) * momentN ω m * ((r : ℂ) ^ (m + 1))⁻¹ *
    exp ((m : ℂ) * θ * I) with hgdef
  have hconjexp : conj (exp (θ * I)) = exp (-(θ * I)) := by
    rw [← Complex.exp_conj]; congr 1; simp
  have hg : ∀ m, conj (-(I / (2 * Real.pi)) * (momentM ω m * (z ^ (m + 1))⁻¹) * exp (θ * I)) =
      g m := by
    intro m
    have hzc : conj z = (r : ℂ) * exp (-(θ * I)) := by
      rw [hzdef, map_mul, Complex.conj_ofReal, hconjexp]
    simp only [map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      map_inv₀, map_pow, hzc, conj_momentM, hconjexp, hgdef]
    rw [mul_pow, ← Complex.exp_nat_mul, mul_inv, ← Complex.exp_neg]
    have he : exp (-(((m + 1 : ℕ) : ℂ) * -(θ * I))) * exp (-(θ * I)) = exp ((m : ℂ) * θ * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc -(-I / (2 * Real.pi)) * (momentN ω m * (((r : ℂ) ^ (m + 1))⁻¹ *
          exp (-(((m + 1 : ℕ) : ℂ) * -(θ * I))))) * exp (-(θ * I))
        = I / (2 * Real.pi) * momentN ω m * ((r : ℂ) ^ (m + 1))⁻¹ *
          (exp (-(((m + 1 : ℕ) : ℂ) * -(θ * I))) * exp (-(θ * I))) := by ring
      _ = _ := by rw [he]
  have hT : conj (-(I / (2 * Real.pi)) * (∫ w, (ω w : ℂ) * (z - w)⁻¹) * exp (θ * I)) =
      velocityC ω z * exp (-(θ * I)) := by
    rw [← conj_velocityC, map_mul, Complex.conj_conj, hconjexp]
  simp_rw [hg, hT] at h3
  have hinj : Function.Injective (fun j : ℕ => 4 * (j + 1)) := fun a b h => by
    simp only at h; omega
  have hvan : ∀ m ∉ Set.range (fun j : ℕ => 4 * (j + 1)), g m = 0 := by
    intro m hm
    have hN : momentN ω m = 0 := by
      rw [← conj_momentM]
      by_cases h4 : 4 ∣ m
      · have hm0 : m = 0 := by
          by_contra hne
          obtain ⟨k, rfl⟩ := h4
          exact hm ⟨k - 1, by simp only; omega⟩
        subst hm0
        simp only [momentM, pow_zero, mul_one]
        rw [integral_complex_ofReal, hmass]; simp
      · rw [momentM_eq_zero_of_not_dvd hsym h4, map_zero]
    simp [hgdef, hN]
  have h4 := (hinj.hasSum_iff hvan).mpr h3
  have h5 : HasSum (fun j : ℕ => I / (2 * Real.pi) * momentN ω (4 * (j + 1)) *
      ((r : ℂ) ^ (4 * (j + 1) + 1))⁻¹ * exp ((4 * (j + 1) : ℕ) * θ * I))
      (velocityC ω z * exp (-(θ * I))) := h4
  exact ⟨h5.summable, by rw [h5.tsum_eq]; rfl⟩

end Euler2D

end
