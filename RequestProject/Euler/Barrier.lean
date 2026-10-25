module

public import RequestProject.Euler.ScalarLemmas

/-!
# First-contact barrier arguments

The support estimates of the paper (Lemma `cs:supportlemma` and Lemma `ca:lem:polymoment`)
reduce, after the geometric estimates on the velocity, to a scalar first-contact argument for an
upper Dini derivative inequality `D⁺y ≤ f(y)`, valid as long as `y` stays below a barrier.
This file proves that scalar argument in general (`dini_barrier`) and the two instances used in
the paper:

* `support_bootstrap` (Lemma `cs:supportlemma`, scalar part): if `D⁺y ≤ c_b ρ + c δ y³` while
  `y ≤ B`, `y(0) ≤ C_w ρ`, `B = 2(C_w + c_b)(1 + L)ρ` and `c δ B² L ≤ 1/4`, then `y ≤ 3B/4` on
  `[0, L]`;
* `polymoment_radius_barrier` (Lemma `ca:lem:polymoment`, scalar part): if
  `D⁺𝓡 ≤ C₁ + K 𝓡³` while `𝓡 ≤ 2(2 + C₁ s)`, `𝓡(0) ≤ 2` and `8K(2 + C₁L)³ < C₁`, then
  `𝓡(s) ≤ 2(2 + C₁ s)` on `[0, L]`.

Upper Dini derivatives are expressed as in `dini_comparison`: `D⁺y(t) ≤ g` means that for every
`r > g`, eventually for small `h > 0`, `(y(t+h) - y(t))/h < r`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Real

namespace Euler2D

/-- **First-contact barrier lemma.** Let `y, B` be continuous on `[0,T]` and `f` continuous and
monotone. Suppose `D⁺y(t) ≤ f(y(t))` whenever `y(t) ≤ B(t)`, `y(0) < B(0)`, and
`y(0) + ∫₀ᵗ f(B) < B(t)` for every `t ∈ [0,T]`. Then `y < B` on `[0,T]`. -/
theorem dini_barrier {y B f : ℝ → ℝ} {T : ℝ} (hy : ContinuousOn y (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T)) (hf : Continuous f) (hfm : Monotone f)
    (hD : ∀ t ∈ Ico 0 T, y t ≤ B t → ∀ r > f (y t),
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (y (t + h) - y t) / h < r)
    (h0 : y 0 < B 0) (hbar : ∀ t ∈ Icc 0 T, y 0 + ∫ s in (0)..t, f (B s) < B t) :
    ∀ t ∈ Icc 0 T, y t < B t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t₀, ht₀, hyt₀⟩ := hcon
  set S : Set ℝ := Icc 0 T ∩ (fun t => y t - B t) ⁻¹' Ici 0 with hS
  have hSc : IsClosed S := (hy.sub hB).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨t₀, ht₀, by simp; linarith⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set s := sInf S with hsdef
  have hsS : s ∈ S := hSc.csInf_mem hSne hSbdd
  have hsI : s ∈ Icc 0 T := hsS.1
  have hBys : B s ≤ y s := by have := hsS.2; simp at this; linarith
  have hlt : ∀ t ∈ Ico 0 s, y t < B t := by
    intro t ht
    by_contra h
    push_neg at h
    have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hsI.2⟩, by simp; linarith⟩
    have := csInf_le hSbdd htS
    linarith [ht.2]
  have hs0 : 0 < s := by
    rcases hsI.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hBys; linarith
  have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hsI.2
  have hle : ∀ t ∈ Icc 0 s, y t ≤ B t := by
    have hcl : IsClosed (Icc 0 s ∩ (fun t => y t - B t) ⁻¹' Iic 0) :=
      ((hy.sub hB).mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub2 : Ico 0 s ⊆ Icc 0 s ∩ (fun t => y t - B t) ⁻¹' Iic 0 := fun t ht =>
      ⟨Ico_subset_Icc_self ht, by simp; linarith [hlt t ht]⟩
    have := closure_minimal hsub2 hcl
    rw [closure_Ico hs0.ne] at this
    intro t ht
    have := (this ht).2
    simp at this; linarith
  have hfy : ContinuousOn (fun t => f (y t)) (Icc 0 s) := hf.comp_continuousOn (hy.mono hsub)
  have hfB : ContinuousOn (fun t => f (B t)) (Icc 0 s) := hf.comp_continuousOn (hB.mono hsub)
  have hcmp := dini_comparison (hy.mono hsub) hfy
    (fun t ht r hr => hD t ⟨ht.1, ht.2.trans_le hsI.2⟩ (hlt t ht).le r hr) s ⟨hs0.le, le_rfl⟩
  have hint : ∫ u in (0)..s, f (y u) ≤ ∫ u in (0)..s, f (B u) := by
    apply intervalIntegral.integral_mono_on hs0.le
    · exact hfy.intervalIntegrable_of_Icc hs0.le
    · exact hfB.intervalIntegrable_of_Icc hs0.le
    · intro u hu; exact hfm (hle u hu)
  have := hbar s hsI
  linarith

/-- **Scalar part of the support bootstrap (Lemma `cs:supportlemma`).** Suppose `y` is continuous
on `[0,L]`, and as long as `y ≤ B` its upper Dini derivative satisfies
`D⁺y ≤ c_b ρ + c δ y³`. If `y(0) ≤ C_w ρ`, `B = 2(C_w + c_b)(1 + L)ρ` and `c δ B² L ≤ 1/4`, then
`y < 3B/4` on `[0,L]` (in particular the a priori assumption `y ≤ B` is never saturated). -/
theorem support_bootstrap {y : ℝ → ℝ} {L ρ Cw cb c δ B : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hCw : 0 < Cw) (hcb : 0 ≤ cb) (hcδ : 0 ≤ c * δ) (hy : ContinuousOn y (Icc 0 L))
    (hD : ∀ t ∈ Ico 0 L, y t ≤ B → ∀ r > cb * ρ + c * δ * y t ^ 3,
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (y (t + h) - y t) / h < r)
    (h0 : y 0 ≤ Cw * ρ) (hB : B = 2 * (Cw + cb) * (1 + L) * ρ) (hsmall : c * δ * B ^ 2 * L ≤ 1 / 4) :
    ∀ t ∈ Icc 0 L, y t < 3 * B / 4 := by
  have hBpos : 0 < B := by rw [hB]; positivity
  have hmono : Monotone fun u : ℝ => cb * ρ + c * δ * u ^ 3 := by
    intro a b hab
    have : a ^ 3 ≤ b ^ 3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone hab
    have := mul_le_mul_of_nonneg_left this hcδ
    simpa using add_le_add_left this (cb * ρ)
  have h1 : Cw * ρ + L * (cb * ρ) ≤ B / 2 := by
    rw [hB]; nlinarith [mul_nonneg hcb hρ.le, mul_nonneg hL (mul_nonneg hcb hρ.le),
      mul_nonneg hCw.le hρ.le, mul_nonneg hL (mul_nonneg hCw.le hρ.le)]
  have hLc : 0 ≤ L * (cb * ρ) := by positivity
  have hCρ : 0 < Cw * ρ := by positivity
  refine dini_barrier hy continuousOn_const (by fun_prop) hmono
    (fun t ht hyt r hr => hD t ht (hyt.trans (by linarith)) r hr) (by linarith) ?_
  intro t ht
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have h2 : t * (cb * ρ) ≤ L * (cb * ρ) :=
    mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hcb hρ.le)
  have h3 : t * (c * δ * (3 * B / 4) ^ 3) ≤ 27 / 256 * B := by
    have e : t * (c * δ * (3 * B / 4) ^ 3) = 27 / 64 * B * (c * δ * B ^ 2 * t) := by ring
    have : c * δ * B ^ 2 * t ≤ c * δ * B ^ 2 * L :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    rw [e]; nlinarith
  nlinarith

/-- **Scalar part of the polynomial-moment radius estimate (Lemma `ca:lem:polymoment`).** Suppose
`𝓡` is continuous on `[0,L]`, and as long as `𝓡(s) ≤ 2(2 + C₁ s)` its upper Dini derivative
satisfies `D⁺𝓡 ≤ C₁ + K 𝓡³`. If `𝓡(0) ≤ 2`, `K ≥ 0`, `C₁ ≥ 0` and `8K(2 + C₁L)³ < C₁`, then
`𝓡(s) < 2(2 + C₁ s)` on `[0,L]`. -/
theorem polymoment_radius_barrier {R : ℝ → ℝ} {L C₁ K : ℝ} (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K)
    (hR : ContinuousOn R (Icc 0 L))
    (hD : ∀ s ∈ Ico 0 L, R s ≤ 2 * (2 + C₁ * s) → ∀ r > C₁ + K * R s ^ 3,
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (R (s + h) - R s) / h < r)
    (h0 : R 0 ≤ 2) (hsmall : 8 * K * (2 + C₁ * L) ^ 3 < C₁) :
    ∀ s ∈ Icc 0 L, R s < 2 * (2 + C₁ * s) := by
  have hmono : Monotone fun u : ℝ => C₁ + K * u ^ 3 := by
    intro a b hab
    have : a ^ 3 ≤ b ^ 3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone hab
    have := mul_le_mul_of_nonneg_left this hK
    simpa using add_le_add_left this C₁
  refine dini_barrier hR (by fun_prop) (by fun_prop) hmono hD (by simp; linarith) ?_
  intro t ht
  have hbound : ∀ u ∈ Icc 0 t, C₁ + K * (2 * (2 + C₁ * u)) ^ 3 ≤ C₁ + 8 * K * (2 + C₁ * L) ^ 3 := by
    intro u hu
    have hb0 : 0 ≤ 2 + C₁ * u := by nlinarith [hu.1]
    have hb1 : 2 + C₁ * u ≤ 2 + C₁ * L := by nlinarith [hu.2, ht.2]
    have : (2 + C₁ * u) ^ 3 ≤ (2 + C₁ * L) ^ 3 := pow_le_pow_left₀ hb0 hb1 3
    have := mul_le_mul_of_nonneg_left this hK
    nlinarith
  have hint : ∫ u in (0)..t, (C₁ + K * (2 * (2 + C₁ * u)) ^ 3) ≤
      ∫ u in (0)..t, (C₁ + 8 * K * (2 + C₁ * L) ^ 3) := by
    apply intervalIntegral.integral_mono_on ht.1
    · exact (by fun_prop : Continuous fun u : ℝ => C₁ + K * (2 * (2 + C₁ * u)) ^ 3)
        |>.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · exact hbound
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  have : t * (C₁ + 8 * K * (2 + C₁ * L) ^ 3) ≤ t * (2 * C₁) :=
    mul_le_mul_of_nonneg_left (by linarith) ht.1
  nlinarith

end Euler2D

end
