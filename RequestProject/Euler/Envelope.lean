module

public import RequestProject.Euler.ScalarLemmas

/-!
# The weighted Gronwall estimate for the outer vortices (Theorem `ca:thm:envelope`)

Formalization of Theorem `ca:thm:envelope` of Section `part:ca`: for the weighted mild
system of Definition `ca:def:system` (diagonal propagators bounded by `M e^{σ a_j (t-s)}`,
`a_j = b^{k-j}`, interaction coefficients `B^±`, local terms `n_j`, forcing `f_j` and remaining
sources `r_j`), the weighted maximum `Z(t) = max_{j<k} h^{-(k-j)} ‖x_j(t)‖`, `h = C₀ρ⁶`, obeys

`Z(t) ≤ M e^{νt} Z(0) + (M C_int / C₀) ∫₀ᵗ e^{ν(t-s)} E(s) ds + M ∫₀ᵗ e^{ν(t-s)} 𝓡(s) ds`

with `ν = bσ + M C_int b (1/(C₀-1) + ζ_ρ/(1-ζ_ρ) + d_a + R⁸)` (`nuExp`), `ζ_ρ = C₀ρ⁸`.

We also prove the version of the scalar convolution inequality (`ca:lem:gronwall`) on a finite
interval `[0,T]`, which the proof uses.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Euler2D

/-! ### The scalar convolution inequality on a finite interval -/

/-- Lemma `ca:lem:gronwall` on `[0,T]`, for globally continuous data. -/
theorem scalar_convolution_gronwall_Icc {Z g : ℝ → ℝ} {T : ℝ} (hZ : Continuous Z)
    (hg : Continuous g) {A c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ t ∈ Icc 0 T, Z t ≤ A * exp (c * t) +
      ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Z t ≤ A * exp ((c + d) * t) + ∫ s in (0)..t, exp ((c + d) * (t - s)) * g s := by
  set z : ℝ → ℝ := fun s => exp (-c * s) * Z s
  set f : ℝ → ℝ := fun s => exp (-c * s) * g s
  have hz : Continuous z := by fun_prop
  have hf : Continuous f := by fun_prop
  set v : ℝ → ℝ := fun t => A + ∫ s in (0)..t, (d * z s + f s)
  have hzv : ∀ t ∈ Icc 0 T, z t ≤ v t := by
    intro t ht
    have h1 := h t ht
    have h2 : exp (-c * t) * (∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s)) =
        ∫ s in (0)..t, (d * z s + f s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [z, f]
      have : exp (-c * t) * exp (c * (t - s)) = exp (-c * s) := by
        rw [← exp_add]; ring_nf
      rw [← mul_assoc, this]; ring
    have h3 : exp (-c * t) * (A * exp (c * t)) = A := by
      rw [mul_left_comm, ← exp_add]; simp
    have hpos : 0 < exp (-c * t) := exp_pos _
    calc z t = exp (-c * t) * Z t := rfl
      _ ≤ exp (-c * t) * (A * exp (c * t) + ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = v t := by rw [mul_add, h3, h2]
  have hv : ∀ t, HasDerivAt v (d * z t + f t) t := fun t => by
    have := intervalIntegral.integral_hasDerivAt_right ((hz.const_smul d).add hf |>.intervalIntegrable 0 t)
      (((hz.const_smul d).add hf).stronglyMeasurableAtFilter _ _) ((hz.const_smul d).add hf).continuousAt
    simpa [v] using this.const_add A
  set W : ℝ → ℝ := fun t => exp (-d * t) * v t - ∫ s in (0)..t, exp (-d * s) * f s
  have hW : ∀ t, HasDerivAt W (exp (-d * t) * (d * z t + f t) + (-d * exp (-d * t)) * v t
      - exp (-d * t) * f t) t := fun t => by
    have he : HasDerivAt (fun t => exp (-d * t)) (-d * exp (-d * t)) t := by
      have := ((hasDerivAt_id t).const_mul (-d)).exp
      simpa [mul_comm] using this
    have hI := intervalIntegral.integral_hasDerivAt_right
      ((by fun_prop : Continuous fun s => exp (-d * s) * f s).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun s => exp (-d * s) * f s).stronglyMeasurableAtFilter _ _)
      (by fun_prop : Continuous fun s => exp (-d * s) * f s).continuousAt
    have := (he.mul (hv t)).sub hI
    convert this using 1; ring
  have hWanti : AntitoneOn W (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact (continuous_iff_continuousAt.2 fun t => (hW t).continuousAt).continuousOn
    · exact fun t _ => (hW t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hW t).deriv]
      have := hzv t (Ioo_subset_Icc_self ht)
      have hpos : 0 < exp (-d * t) := exp_pos _
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hd hpos.le)]
  have hW0 : W 0 = A := by simp [W, v]
  have hWt : W t ≤ A := hW0 ▸ hWanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  -- `v t ≤ A e^{dt} + ∫ e^{d(t-s)} f`
  have hvt : v t ≤ A * exp (d * t) + ∫ s in (0)..t, exp (d * (t - s)) * f s := by
    have e1 : (∫ s in (0)..t, exp (d * (t - s)) * f s) =
        exp (d * t) * ∫ s in (0)..t, exp (-d * s) * f s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [show d * (t - s) = d * t + -d * s by ring, exp_add]; ring
    have hWt' : exp (-d * t) * v t ≤ A + ∫ s in (0)..t, exp (-d * s) * f s := by
      simp only [W] at hWt; linarith
    have := mul_le_mul_of_nonneg_left hWt' (exp_pos (d * t)).le
    rw [← mul_assoc, ← exp_add, show d * t + -d * t = 0 by ring, exp_zero, one_mul] at this
    rw [e1]; linarith
  have hZt : Z t = exp (c * t) * z t := by
    simp only [z]; rw [← mul_assoc, ← exp_add]; simp
  have e2 : (∫ s in (0)..t, exp ((c + d) * (t - s)) * g s) =
      exp (c * t) * ∫ s in (0)..t, exp (d * (t - s)) * f s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [f]
    rw [show exp (c * t) * (exp (d * (t - s)) * (exp (-c * s) * g s)) =
      (exp (c * t) * exp (d * (t - s)) * exp (-c * s)) * g s by ring, ← exp_add, ← exp_add]
    ring_nf
  rw [hZt, e2, show (c + d) * t = c * t + d * t by ring, exp_add]
  have := mul_le_mul_of_nonneg_left ((hzv t ht).trans hvt) (exp_pos (c * t)).le
  linarith

/-- Lemma `ca:lem:gronwall` on `[0,T]`, for data continuous on `[0,T]`. -/
theorem scalar_convolution_gronwall_on {Z g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hZ : ContinuousOn Z (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T)) {A c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ t ∈ Icc 0 T, Z t ≤ A * exp (c * t) +
      ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Z t ≤ A * exp ((c + d) * t) + ∫ s in (0)..t, exp ((c + d) * (t - s)) * g s := by
  set Z' : ℝ → ℝ := IccExtend hT (fun s : Icc 0 T => Z s) with hZ'
  set g' : ℝ → ℝ := IccExtend hT (fun s : Icc 0 T => g s) with hg'
  have hZ'c : Continuous Z' := (ContinuousOn.restrict hZ).Icc_extend'
  have hg'c : Continuous g' := (ContinuousOn.restrict hg).Icc_extend'
  have eZ : ∀ s ∈ Icc 0 T, Z' s = Z s := fun s hs => by simp [hZ', IccExtend_of_mem _ _ hs]
  have eg : ∀ s ∈ Icc 0 T, g' s = g s := fun s hs => by simp [hg', IccExtend_of_mem _ _ hs]
  have hsub : ∀ t ∈ Icc 0 T, ∀ s ∈ uIcc 0 t, s ∈ Icc 0 T := fun t ht s hs => by
    rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1, hs.2.trans ht.2⟩
  have h' : ∀ t ∈ Icc 0 T, Z' t ≤ A * exp (c * t) +
      ∫ s in (0)..t, exp (c * (t - s)) * (d * Z' s + g' s) := by
    intro t ht
    rw [eZ t ht]
    convert h t ht using 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [eZ s (hsub t ht s hs), eg s (hsub t ht s hs)]
  have := scalar_convolution_gronwall_Icc hZ'c hg'c hd h' ht
  rw [eZ t ht] at this
  convert this using 2
  refine intervalIntegral.integral_congr fun s hs => ?_
  simp only [eg s (hsub t ht s hs)]

/-! ### The weighted system -/

/-- The weighted maximum `max_{j<k} h^{-(k-j)} v_j`. -/
noncomputable def weightedMax {k : ℕ} (hk : 0 < k) (h : ℝ) (v : Fin k → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun j : Fin k => (h ^ (k - (j : ℕ)))⁻¹ * v j)

lemma le_weightedMax {k : ℕ} (hk : 0 < k) (h : ℝ) (v : Fin k → ℝ) (j : Fin k) :
    (h ^ (k - (j : ℕ)))⁻¹ * v j ≤ weightedMax hk h v :=
  Finset.le_sup' (fun j : Fin k => (h ^ (k - (j : ℕ)))⁻¹ * v j) (Finset.mem_univ j)

lemma weightedMax_le {k : ℕ} (hk : 0 < k) (h : ℝ) (v : Fin k → ℝ) {c : ℝ}
    (hc : ∀ j : Fin k, (h ^ (k - (j : ℕ)))⁻¹ * v j ≤ c) : weightedMax hk h v ≤ c :=
  Finset.sup'_le _ _ fun j _ => hc j

/-- A sum of powers `q^{φ(i)}` over distinct exponents `φ(i) ≥ 1` is at most `q/(1-q)`. -/
lemma sum_pow_le_of_injOn {ι : Type*} (s : Finset ι) (φ : ι → ℕ) (hφ : Set.InjOn φ s)
    (hpos : ∀ i ∈ s, 1 ≤ φ i) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ i ∈ s, q ^ φ i ≤ q / (1 - q) := by
  classical
  set N : ℕ := (s.image φ).sup id + 1
  have hsub : s.image φ ⊆ Finset.Ico 1 N := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    refine Finset.mem_Ico.mpr ⟨hpos a ha, ?_⟩
    have : φ a ≤ (s.image φ).sup id := Finset.le_sup (f := id) hi
    omega
  calc ∑ i ∈ s, q ^ φ i = ∑ i ∈ s.image φ, q ^ i := (Finset.sum_image hφ).symm
    _ ≤ ∑ i ∈ Finset.Ico 1 N, q ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg hq0 i
    _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 hq1
    _ = q / (1 - q) := by rw [pow_one]

/-- Power bookkeeping for the upper interactions: `ρ^{6c} h^a = h^{a+c} C₀^{-c}`, `h = C₀ρ⁶`. -/
lemma rho_pow_up {C₀ ρ : ℝ} (hC₀ : C₀ ≠ 0) (a c : ℕ) :
    ρ ^ (6 * c) * (C₀ * ρ ^ 6) ^ a = (C₀ * ρ ^ 6) ^ (a + c) * (C₀⁻¹) ^ c := by
  rw [pow_add, mul_pow C₀ (ρ ^ 6) c, pow_mul, inv_pow]
  field_simp

/-- Power bookkeeping for the lower interactions: `ρ^{2c} h^{a+c} = h^a (C₀ρ⁸)^c`. -/
lemma rho_pow_down (C₀ ρ : ℝ) (a c : ℕ) :
    ρ ^ (2 * c) * (C₀ * ρ ^ 6) ^ (a + c) = (C₀ * ρ ^ 6) ^ a * (C₀ * ρ ^ 8) ^ c := by
  rw [pow_add, pow_mul, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  ring_nf

/-- **Theorem (`ca:thm:envelope`).** Uniformly in the current index `k` and the number of
ancestors, the weighted maximum `Z(t) = max_{j<k} h^{-(k-j)} ‖x_j(t)‖` (`h = C₀ρ⁶`) of a solution
of the weighted mild system satisfies
`Z(t) ≤ M e^{νt} Z(0) + (M C_int/C₀) ∫₀ᵗ e^{ν(t-s)} E(s) ds + M ∫₀ᵗ e^{ν(t-s)} 𝓡(s) ds`
on `[0,T]`, with `ν = nuExp b σ M C_int C₀ ζ_ρ d_a R` and `𝓡(s) = max_j h^{-(k-j)} ‖r_j(s)‖`. -/
theorem weighted_envelope {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {k : ℕ} (hk : 0 < k) {T b σ M Cint C₀ ρ da R : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hσ : 0 < σ) (hM : 0 ≤ M) (hC : 0 ≤ Cint) (hC₀ : 1 < C₀)
    (hρ : 0 < ρ) (hζ : C₀ * ρ ^ 8 < 1) (hda : 0 ≤ da)
    (U : Fin k → ℝ → ℝ → X →L[ℝ] X)
    (hU : ∀ j t s, 0 ≤ s → s ≤ t → t ≤ T → ‖U j t s‖ ≤ M * exp (σ * b ^ (k - (j : ℕ)) * (t - s)))
    (x n f r : Fin k → ℝ → X) (Bp Bm : Fin k → Fin k → ℝ → X →L[ℝ] X) (E : ℝ → ℝ)
    (hx : ∀ j, ContinuousOn (x j) (Icc 0 T)) (hr : ∀ j, ContinuousOn (r j) (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T)) (hE0 : ∀ s, 0 ≤ E s)
    (hBp : ∀ j l, j < l → ∀ s ∈ Icc 0 T,
      ‖Bp j l s‖ ≤ Cint * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j)))
    (hBm : ∀ j l, l < j → ∀ s ∈ Icc 0 T,
      ‖Bm j l s‖ ≤ Cint * b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l)))
    (hn : ∀ j, ∀ s ∈ Icc 0 T, ‖n j s‖ ≤ Cint * b ^ (k - (j : ℕ)) * (da + R ^ 8) * ‖x j s‖)
    (hf : ∀ j, ∀ s ∈ Icc 0 T, ‖f j s‖ ≤ Cint * ρ ^ (6 * (k - (j : ℕ))) * E s)
    (hmild : ∀ j, ∀ t ∈ Icc 0 T, x j t = U j t 0 (x j 0) + ∫ s in (0)..t, U j t s
      ((∑ l ∈ Finset.univ.filter (fun l => j < l), Bp j l s (x l s)) +
        (∑ l ∈ Finset.univ.filter (fun l => l < j), Bm j l s (x l s)) +
        n j s + f j s + r j s)) :
    ∀ t ∈ Icc 0 T,
      weightedMax hk (C₀ * ρ ^ 6) (fun j => ‖x j t‖) ≤
        M * exp (nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) da R * t) *
            weightedMax hk (C₀ * ρ ^ 6) (fun j => ‖x j 0‖) +
          M * Cint / C₀ * (∫ s in (0)..t,
            exp (nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) da R * (t - s)) * E s) +
          M * (∫ s in (0)..t, exp (nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) da R * (t - s)) *
            weightedMax hk (C₀ * ρ ^ 6) (fun j => ‖r j s‖)) := by
  classical
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have hC₀pos : 0 < C₀ := by linarith
  set h : ℝ := C₀ * ρ ^ 6 with hhdef
  set ζ : ℝ := C₀ * ρ ^ 8 with hζdef
  have hhpos : 0 < h := by positivity
  have hζ0 : 0 ≤ ζ := by positivity
  have hpow : ∀ m : ℕ, 0 < h ^ m := fun m => pow_pos hhpos m
  set Z : ℝ → ℝ := fun t => weightedMax hk h (fun j => ‖x j t‖) with hZdef
  set Rr : ℝ → ℝ := fun s => weightedMax hk h (fun j => ‖r j s‖) with hRdef
  set d' : ℝ := Cint * b * (1 / (C₀ - 1) + ζ / (1 - ζ) + da + R ^ 8) with hd'def
  set g0 : ℝ → ℝ := fun s => Cint / C₀ * E s + Rr s with hg0def
  have hxle : ∀ l t, ‖x l t‖ ≤ h ^ (k - (l : ℕ)) * Z t := fun l t =>
    (inv_mul_le_iff₀ (hpow _)).mp (le_weightedMax hk h (fun j => ‖x j t‖) l)
  have hrle : ∀ l s, ‖r l s‖ ≤ h ^ (k - (l : ℕ)) * Rr s := fun l s =>
    (inv_mul_le_iff₀ (hpow _)).mp (le_weightedMax hk h (fun j => ‖r j s‖) l)
  have hZnn : ∀ t, 0 ≤ Z t := fun t =>
    le_trans (by have := hpow (k - 0); positivity) (le_weightedMax hk h (fun j => ‖x j t‖) ⟨0, hk⟩)
  have hd'nn : 0 ≤ d' := by
    have : 0 < 1 - ζ := by linarith
    have : 0 < C₀ - 1 := by linarith
    positivity
  have hbpow : ∀ m : ℕ, 1 ≤ m → b ^ m ≤ b := fun m hm => by
    calc b ^ m ≤ b ^ 1 := pow_le_pow_of_le_one hb0.le hb1.le hm
      _ = b := pow_one b
  -- the source of the `j`-th mild equation
  set V : Fin k → ℝ → X := fun j s =>
    (∑ l ∈ Finset.univ.filter (fun l => j < l), Bp j l s (x l s)) +
      (∑ l ∈ Finset.univ.filter (fun l => l < j), Bm j l s (x l s)) + n j s + f j s + r j s
    with hVdef
  -- weighted bound on the source
  have hV : ∀ j, ∀ s ∈ Icc 0 T, ‖V j s‖ ≤ h ^ (k - (j : ℕ)) * (d' * Z s + g0 s) := by
    intro j s hs
    have hjk : (j : ℕ) < k := j.isLt
    have hZs := hZnn s
    -- upper interactions
    have hup : ‖∑ l ∈ Finset.univ.filter (fun l => j < l), Bp j l s (x l s)‖ ≤
        h ^ (k - (j : ℕ)) * (Cint * b * (1 / (C₀ - 1)) * Z s) := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ l ∈ Finset.univ.filter (fun l => j < l), ‖Bp j l s (x l s)‖ ≤
          h ^ (k - (j : ℕ)) * (Cint * b * Z s) * (C₀⁻¹) ^ ((l : ℕ) - j) := by
        intro l hl
        have hjl : j < l := (Finset.mem_filter.mp hl).2
        have hjl' : (j : ℕ) < l := hjl
        have hlk : (l : ℕ) < k := l.isLt
        have hid := rho_pow_up (ρ := ρ) hC₀pos.ne' (k - (l : ℕ)) ((l : ℕ) - j)
        rw [show k - (l : ℕ) + ((l : ℕ) - j) = k - (j : ℕ) by omega] at hid
        calc ‖Bp j l s (x l s)‖ ≤ ‖Bp j l s‖ * ‖x l s‖ := (Bp j l s).le_opNorm _
          _ ≤ (Cint * b ^ (k - (l : ℕ)) * ρ ^ (6 * ((l : ℕ) - j))) * (h ^ (k - (l : ℕ)) * Z s) :=
              mul_le_mul (hBp j l hjl s hs) (hxle l s) (norm_nonneg _) (by positivity)
          _ ≤ (Cint * b * ρ ^ (6 * ((l : ℕ) - j))) * (h ^ (k - (l : ℕ)) * Z s) := by
              gcongr; exact hbpow _ (by omega)
          _ = Cint * b * Z s * (ρ ^ (6 * ((l : ℕ) - j)) * h ^ (k - (l : ℕ))) := by ring
          _ = h ^ (k - (j : ℕ)) * (Cint * b * Z s) * (C₀⁻¹) ^ ((l : ℕ) - j) := by
              rw [hid]; ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      have hgeo := sum_pow_le_of_injOn (Finset.univ.filter (fun l : Fin k => j < l))
        (fun l => (l : ℕ) - j)
        (fun a ha b' hb' hab => by
          have := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          have := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
          simp only at hab; exact Fin.ext (by omega))
        (fun l hl => by have : j < l := (Finset.mem_filter.mp hl).2; omega)
        (inv_nonneg.mpr hC₀pos.le) (inv_lt_one_of_one_lt₀ hC₀)
      have heq : C₀⁻¹ / (1 - C₀⁻¹) = 1 / (C₀ - 1) := by
        field_simp
      rw [heq] at hgeo
      calc h ^ (k - (j : ℕ)) * (Cint * b * Z s) *
            ∑ l ∈ Finset.univ.filter (fun l => j < l), (C₀⁻¹) ^ ((l : ℕ) - j)
          ≤ h ^ (k - (j : ℕ)) * (Cint * b * Z s) * (1 / (C₀ - 1)) :=
            mul_le_mul_of_nonneg_left hgeo (by have := hpow (k - (j : ℕ)); positivity)
        _ = _ := by ring
    -- lower interactions
    have hdown : ‖∑ l ∈ Finset.univ.filter (fun l => l < j), Bm j l s (x l s)‖ ≤
        h ^ (k - (j : ℕ)) * (Cint * b * (ζ / (1 - ζ)) * Z s) := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ l ∈ Finset.univ.filter (fun l => l < j), ‖Bm j l s (x l s)‖ ≤
          h ^ (k - (j : ℕ)) * (Cint * b * Z s) * ζ ^ ((j : ℕ) - l) := by
        intro l hl
        have hlj : l < j := (Finset.mem_filter.mp hl).2
        have hlj' : (l : ℕ) < j := hlj
        have hid := rho_pow_down C₀ ρ (k - (j : ℕ)) ((j : ℕ) - l)
        rw [show k - (j : ℕ) + ((j : ℕ) - l) = k - (l : ℕ) by omega] at hid
        calc ‖Bm j l s (x l s)‖ ≤ ‖Bm j l s‖ * ‖x l s‖ := (Bm j l s).le_opNorm _
          _ ≤ (Cint * b ^ (k - (l : ℕ)) * ρ ^ (2 * ((j : ℕ) - l))) * (h ^ (k - (l : ℕ)) * Z s) :=
              mul_le_mul (hBm j l hlj s hs) (hxle l s) (norm_nonneg _) (by positivity)
          _ ≤ (Cint * b * ρ ^ (2 * ((j : ℕ) - l))) * (h ^ (k - (l : ℕ)) * Z s) := by
              gcongr; exact hbpow _ (by omega)
          _ = Cint * b * Z s * (ρ ^ (2 * ((j : ℕ) - l)) * h ^ (k - (l : ℕ))) := by ring
          _ = h ^ (k - (j : ℕ)) * (Cint * b * Z s) * ζ ^ ((j : ℕ) - l) := by
              rw [hid]; ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      have hgeo := sum_pow_le_of_injOn (Finset.univ.filter (fun l : Fin k => l < j))
        (fun l => (j : ℕ) - l)
        (fun a ha b' hb' hab => by
          have := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          have := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
          simp only at hab; exact Fin.ext (by omega))
        (fun l hl => by have : l < j := (Finset.mem_filter.mp hl).2; omega)
        hζ0 hζ
      calc h ^ (k - (j : ℕ)) * (Cint * b * Z s) *
            ∑ l ∈ Finset.univ.filter (fun l => l < j), ζ ^ ((j : ℕ) - l)
          ≤ h ^ (k - (j : ℕ)) * (Cint * b * Z s) * (ζ / (1 - ζ)) :=
            mul_le_mul_of_nonneg_left hgeo (by have := hpow (k - (j : ℕ)); positivity)
        _ = _ := by ring
    -- local term
    have hnb : ‖n j s‖ ≤ h ^ (k - (j : ℕ)) * (Cint * b * (da + R ^ 8) * Z s) := by
      calc ‖n j s‖ ≤ Cint * b ^ (k - (j : ℕ)) * (da + R ^ 8) * ‖x j s‖ := hn j s hs
        _ ≤ Cint * b * (da + R ^ 8) * (h ^ (k - (j : ℕ)) * Z s) := by
            gcongr
            · exact hbpow _ (by omega)
            · exact hxle j s
        _ = _ := by ring
    -- forcing
    have hfb : ‖f j s‖ ≤ h ^ (k - (j : ℕ)) * (Cint / C₀ * E s) := by
      have hid := rho_pow_up (ρ := ρ) hC₀pos.ne' 0 (k - (j : ℕ))
      rw [pow_zero, mul_one, zero_add] at hid
      have hc : (C₀⁻¹) ^ (k - (j : ℕ)) ≤ C₀⁻¹ := by
        calc (C₀⁻¹) ^ (k - (j : ℕ)) ≤ (C₀⁻¹) ^ 1 :=
              pow_le_pow_of_le_one (inv_nonneg.mpr hC₀pos.le) (inv_le_one_of_one_le₀ hC₀.le)
                (by omega)
          _ = C₀⁻¹ := pow_one _
      calc ‖f j s‖ ≤ Cint * ρ ^ (6 * (k - (j : ℕ))) * E s := hf j s hs
        _ = h ^ (k - (j : ℕ)) * (Cint * E s) * (C₀⁻¹) ^ (k - (j : ℕ)) := by rw [hid]; ring
        _ ≤ h ^ (k - (j : ℕ)) * (Cint * E s) * C₀⁻¹ :=
            mul_le_mul_of_nonneg_left hc (by have := hpow (k - (j : ℕ)); have := hE0 s; positivity)
        _ = _ := by ring
    have hrb := hrle j s
    calc ‖V j s‖ ≤ ‖∑ l ∈ Finset.univ.filter (fun l => j < l), Bp j l s (x l s)‖ +
          ‖∑ l ∈ Finset.univ.filter (fun l => l < j), Bm j l s (x l s)‖ + ‖n j s‖ + ‖f j s‖ +
          ‖r j s‖ := by
          simp only [hVdef]
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          exact norm_add_le _ _
      _ ≤ h ^ (k - (j : ℕ)) * (Cint * b * (1 / (C₀ - 1)) * Z s) +
          h ^ (k - (j : ℕ)) * (Cint * b * (ζ / (1 - ζ)) * Z s) +
          h ^ (k - (j : ℕ)) * (Cint * b * (da + R ^ 8) * Z s) +
          h ^ (k - (j : ℕ)) * (Cint / C₀ * E s) + h ^ (k - (j : ℕ)) * Rr s := by
          gcongr
      _ = h ^ (k - (j : ℕ)) * (d' * Z s + g0 s) := by
          simp only [hd'def, hg0def]; ring
  -- continuity of the weighted maxima
  have hZc : ContinuousOn Z (Icc 0 T) := by
    simp only [hZdef, weightedMax]
    exact ContinuousOn.finset_sup'_apply _ fun j _ => continuousOn_const.mul (hx j).norm
  have hRc : ContinuousOn Rr (Icc 0 T) := by
    simp only [hRdef, weightedMax]
    exact ContinuousOn.finset_sup'_apply _ fun j _ => continuousOn_const.mul (hr j).norm
  have hg0c : ContinuousOn g0 (Icc 0 T) := (continuousOn_const.mul hE).add hRc
  have hsub : ∀ t ∈ Icc 0 T, uIcc 0 t ⊆ Icc 0 T := fun t ht s hs => by
    rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1, hs.2.trans ht.2⟩
  -- the mild equation gives the convolution inequality for `Z`
  have hZineq : ∀ t ∈ Icc 0 T, Z t ≤ (M * Z 0) * exp (b * σ * t) +
      ∫ s in (0)..t, exp (b * σ * (t - s)) * ((M * d') * Z s + M * g0 s) := by
    intro t ht
    apply weightedMax_le
    intro j
    have hjk : (j : ℕ) < k := j.isLt
    have hexp : ∀ s, s ≤ t → exp (σ * b ^ (k - (j : ℕ)) * (t - s)) ≤ exp (b * σ * (t - s)) :=
      fun s hst => exp_le_exp.mpr (by
        have h1 := hbpow (k - (j : ℕ)) (by omega)
        have h2 : 0 ≤ t - s := by linarith
        have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hσ.le) h2
        linarith)
    have hI : ‖∫ s in (0)..t, U j t s (V j s)‖ ≤
        ∫ s in (0)..t, M * exp (b * σ * (t - s)) * (h ^ (k - (j : ℕ)) * (d' * Z s + g0 s)) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.1 (Eventually.of_forall ?_) ?_
      · intro s hs
        have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
        calc ‖U j t s (V j s)‖ ≤ ‖U j t s‖ * ‖V j s‖ := (U j t s).le_opNorm _
          _ ≤ (M * exp (b * σ * (t - s))) * (h ^ (k - (j : ℕ)) * (d' * Z s + g0 s)) := by
            refine mul_le_mul ((hU j t s hs.1.le hs.2 ht.2).trans ?_) (hV j s hs')
              (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left (hexp s hs.2) hM
      · apply ContinuousOn.intervalIntegrable
        refine ContinuousOn.mul (by fun_prop) (continuousOn_const.mul ?_)
        exact ((continuousOn_const.mul hZc).add hg0c).mono (hsub t ht)
    have hx0 : ‖x j 0‖ ≤ h ^ (k - (j : ℕ)) * Z 0 := hxle j 0
    have hU0 : ‖U j t 0‖ ≤ M * exp (b * σ * t) := by
      have := hU j t 0 le_rfl ht.1 ht.2
      rw [sub_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hM)
      simpa using hexp 0 ht.1
    have hxt : ‖x j t‖ ≤ M * exp (b * σ * t) * (h ^ (k - (j : ℕ)) * Z 0) +
        ∫ s in (0)..t, M * exp (b * σ * (t - s)) * (h ^ (k - (j : ℕ)) * (d' * Z s + g0 s)) := by
      rw [hmild j t ht]
      refine (norm_add_le _ _).trans (add_le_add ?_ hI)
      calc ‖U j t 0 (x j 0)‖ ≤ ‖U j t 0‖ * ‖x j 0‖ := (U j t 0).le_opNorm _
        _ ≤ _ := mul_le_mul hU0 hx0 (norm_nonneg _) (by positivity)
    have hint : ∫ s in (0)..t, M * exp (b * σ * (t - s)) * (h ^ (k - (j : ℕ)) * (d' * Z s + g0 s)) =
        h ^ (k - (j : ℕ)) * ∫ s in (0)..t, exp (b * σ * (t - s)) * ((M * d') * Z s + M * g0 s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [hint] at hxt
    rw [inv_mul_le_iff₀ (hpow _)]
    calc ‖x j t‖ ≤ _ := hxt
      _ = h ^ (k - (j : ℕ)) * ((M * Z 0) * exp (b * σ * t) +
          ∫ s in (0)..t, exp (b * σ * (t - s)) * ((M * d') * Z s + M * g0 s)) := by ring
  -- scalar Gronwall
  have hG := scalar_convolution_gronwall_on hT hZc (continuousOn_const.mul hg0c)
    (mul_nonneg hM hd'nn) hZineq ht₀
  have hν : nuExp b σ M Cint C₀ (C₀ * ρ ^ 8) da R = b * σ + M * d' := by
    simp only [nuExp, hd'def, hζdef]; ring
  rw [hν]
  have hiE : IntervalIntegrable (fun s => exp ((b * σ + M * d') * (t₀ - s)) * E s) volume 0 t₀ :=
    (ContinuousOn.mul (by fun_prop) (hE.mono (hsub t₀ ht₀))).intervalIntegrable
  have hiR : IntervalIntegrable (fun s => exp ((b * σ + M * d') * (t₀ - s)) * Rr s) volume 0 t₀ :=
    (ContinuousOn.mul (by fun_prop) (hRc.mono (hsub t₀ ht₀))).intervalIntegrable
  have hsplit : ∫ s in (0)..t₀, exp ((b * σ + M * d') * (t₀ - s)) * (M * g0 s) =
      M * Cint / C₀ * (∫ s in (0)..t₀, exp ((b * σ + M * d') * (t₀ - s)) * E s) +
        M * (∫ s in (0)..t₀, exp ((b * σ + M * d') * (t₀ - s)) * Rr s) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hiE.const_mul _) (hiR.const_mul _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hg0def]; ring
  calc Z t₀ ≤ M * Z 0 * exp ((b * σ + M * d') * t₀) +
        ∫ s in (0)..t₀, exp ((b * σ + M * d') * (t₀ - s)) * (M * g0 s) := hG
    _ = _ := by rw [hsplit]; ring

end Euler2D

end
