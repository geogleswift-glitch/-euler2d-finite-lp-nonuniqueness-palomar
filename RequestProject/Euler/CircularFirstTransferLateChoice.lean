module

public import RequestProject.Euler.CircularActualFirstNonzeroTransfer

/-! Fix the real past lookback before the later observation time.
The original nonzero bilateral transform gives an exponentially growing
seed at every sufficiently late observation, with the same past budgets. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_firstTransfer_uniform_late_response_and_lookback
    {b sCanon Chistory ηctrl : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hbilateral : bilateral P.moment ((b : ℂ) * (sigma + 5 / 4 * I)) ≠ 0)
    (hsCanon : sCanon < 0) (hChistory : 0 ≤ Chistory) (hηctrl : 0 ≤ ηctrl) :
    ∃ c > 0, ∃ Lback > 0, ∃ tmin ≥ 0, ∀ tstar ≥ tmin,
      let κ := ‖retardedSol ((b : ℂ) * lamStar)
        ((b : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖
      let d := tstar - sCanon
      0 < d ∧ c * Real.exp (b * sigma * tstar) ≤ κ ∧
      ((‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma) * Real.exp (b * sigma * d)) *
        Real.exp (-(sigma - b * sigma) * Lback) ≤ κ / 8 ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
          ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
            Real.exp (b * sigma * (Lback + d)) ≤ (κ / 8) * ρ ^ 6 := by
  let a : ℂ := (b : ℂ) * lamStar
  let z : ℂ := (b : ℂ) * (sigma + 5 / 4 * I)
  let R := retardedSol a z Kstar P.moment
  let kInf := ‖Kstar * bilateral P.moment z‖
  have hkInf : 0 < kInf := norm_pos_iff.mpr (mul_ne_zero Kstar_ne_zero hbilateral)
  have hz0 : 0 < z.re := by dsimp only [z]; simpa using mul_pos hb.1 sigma_pos
  have hb1 : b < 1 := hb.2.trans (by norm_num)
  have hz1 : z.re < sigma := by
    dsimp only [z]
    simpa using mul_lt_of_lt_one_left sigma_pos hb1
  obtain ⟨_, _, hlim⟩ := retardedSol_spec P.laplace.expWindow hz0 hz1 a Kstar
  have hnorm : ∀ᶠ t : ℝ in atTop, kInf / 2 < ‖Complex.exp (-a * t) * R t‖ :=
    hlim.norm.eventually (lt_mem_nhds (half_lt_self hkInf))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hnorm
  let c := kInf / 2
  have hc : 0 < c := half_pos hkInf
  have ha : a.re = b * sigma := by simp [a, lamStar]
  have hresponse (t : ℝ) (ht : t₀ ≤ t) : c * Real.exp (b * sigma * t) ≤ ‖R t‖ := by
    have hn := (ht₀ t ht).le
    rw [norm_mul, norm_cexp_neg_mul, ha] at hn
    have hh := mul_le_mul_of_nonneg_right hn (Real.exp_pos (b * sigma * t)).le
    have he : Real.exp (-(b * sigma) * t) * Real.exp (b * sigma * t) = 1 := by
      rw [← Real.exp_add, show -(b * sigma) * t + b * sigma * t = 0 by ring, Real.exp_zero]
    calc
      _ ≤ (Real.exp (-(b * sigma) * t) * ‖R t‖) * Real.exp (b * sigma * t) := hh
      _ = (Real.exp (-(b * sigma) * t) * Real.exp (b * sigma * t)) * ‖R t‖ := by ring
      _ = _ := by rw [he, one_mul]
  let ζ := c * Real.exp (b * sigma * sCanon) / 8
  have hζ : 0 < ζ := div_pos (mul_pos hc (Real.exp_pos _)) (by norm_num)
  have hgap : 0 < sigma - b * sigma := by
    rw [show sigma - b * sigma = sigma * (1 - b) by ring]
    exact mul_pos sigma_pos (sub_pos.mpr hb1)
  let Atail := (‖Kstar‖ * Chistory * ηctrl) / (sigma - b * sigma)
  have harg : Tendsto (fun L : ℝ => (sigma - b * sigma) * L) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hgap).2 tendsto_id
  have hlimL : Tendsto (fun L : ℝ => Atail * Real.exp (-(sigma - b * sigma) * L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg).const_mul Atail
  have hsmall : ∀ᶠ L : ℝ in atTop, Atail * Real.exp (-(sigma - b * sigma) * L) ≤ ζ :=
    (hlimL.eventually (gt_mem_nhds hζ)).mono (fun _ h => h.le)
  have htail := P.eventually_retarded_lookback_tail_uniform_rho hb hζ sCanon 0
  obtain ⟨Lback, hLback, hlead, htailL⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hsmall.and htail)).exists
  refine ⟨c, hc, Lback, hLback, max t₀ 0, le_max_right _ _, ?_⟩
  intro tstar htstar
  dsimp only
  let κ := ‖R tstar‖
  let d := tstar - sCanon
  have ht : t₀ ≤ tstar := (le_max_left _ _).trans htstar
  have ht0 : 0 ≤ tstar := (le_max_right _ _).trans htstar
  have hd : 0 < d := by dsimp only [d]; linarith only [ht0, hsCanon]
  have hresp := hresponse tstar ht
  have hscale : ζ * Real.exp (b * sigma * d) = (c * Real.exp (b * sigma * tstar)) / 8 := by
    have he : Real.exp (b * sigma * sCanon) * Real.exp (b * sigma * d) =
        Real.exp (b * sigma * tstar) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring
    calc
      _ = (c / 8) * (Real.exp (b * sigma * sCanon) * Real.exp (b * sigma * d)) := by
        dsimp only [ζ]
        ring
      _ = _ := by rw [he]; ring
  have hscaleLe : ζ * Real.exp (b * sigma * d) ≤ κ / 8 := by
    rw [hscale]
    exact div_le_div_of_nonneg_right hresp (by norm_num)
  refine ⟨hd, hresp, ?_, ?_⟩
  · calc
      _ = (Atail * Real.exp (-(sigma - b * sigma) * Lback)) * Real.exp (b * sigma * d) := by
        dsimp only [Atail]
        ring
      _ ≤ ζ * Real.exp (b * sigma * d) :=
        mul_le_mul_of_nonneg_right hlead (Real.exp_pos _).le
      _ ≤ _ := hscaleLe
  · intro ρ hρ
    have hexp : Real.exp (b * sigma * (Lback + d)) =
        Real.exp (b * sigma * Lback) * Real.exp (b * sigma * d) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (‖retardedSol a z ((ρ : ℂ) ^ 6 * Kstar) P.moment (sCanon - Lback)‖ *
          Real.exp (b * sigma * Lback)) * Real.exp (b * sigma * d) := by rw [hexp]; ring
      _ ≤ (ζ * ρ ^ 6) * Real.exp (b * sigma * d) :=
        mul_le_mul_of_nonneg_right (by simpa only [add_zero] using htailL ρ hρ) (Real.exp_pos _).le
      _ = (ζ * Real.exp (b * sigma * d)) * ρ ^ 6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscaleLe (pow_nonneg hρ 6)

theorem exists_actual_late_firstTransfer_nonzero_family {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Y)
    (hd : ContDiffAt ℝ 2 (fun W => Y W period) (littleCircularReference hγ hγ1))
    (hfix : Y (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Y W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Y W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq)
    (hsamples : ∃ N : ℕ, ∀ n ≥ N, ∃ α : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧ ‖α‖ ≤ r₀ / 2 ∧
      P.ancient (-(n : ℝ) * (period + period)) = circularConstrainedChart hγ hγ1 (gseq α 0))
    {q T : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 < T)
    (ηctrl Kextra : ℝ) (hηctrl : 0 < ηctrl) (hKextra : 0 ≤ Kextra)
    (hηa : ηctrl ≤ cellA / 16) (hηgap : ηctrl ≤ (1 - cellA) / 16) :
    ∃ b : ℝ≥0, 0 < b ∧ b < 1 / 4 ∧
      bilateral P.moment (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) ≠ 0 ∧
      (b : ℝ) * Kextra + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 ∧
      ∃ δ > 0, ∃ sCanon < 0, ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
      ∃ Henv > 0, ∃ Chistory > 0, ∃ c > 0, ∃ Lback > 0, ∃ tmin ≥ 0,
      ∀ tstar ≥ tmin,
        let κ := ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
          (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖ / 2
        let d := tstar - sCanon
        0 < κ ∧ c * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ ∧
        ∀ seedMax > 0, ∀ nMin : ℕ, ∃ n ≥ nMin,
          let s := -(n : ℝ) * (period + period)
          ∃ hs : s ≤ 0, ∃ A₀ > 0, ∃ D > 0, ∃ Cmatch > 0, ∃ Cback > 0,
          ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ < seedMax ∧
            Henv * ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (P.ancient s - littleCircularReference hγ hγ1))‖ * Real.exp (sigma * D) ≤ ηctrl ∧
            D / A₀ < T ∧ Lback + d < D ∧
            ∀ᶠ ξ : ℝ in atTop,
              P.HasActualFirstNonzeroTransferFamilyAt (T := T) hq hqE
                b s hs A₀ D δ sCanon ηctrl Lback (Lback + d) Henv Chistory Cmatch Cback Cb Ccur Cobs κ ξ := by
  obtain ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, hfamilies⟩ :=
    P.exists_actual_firstTransfer_input_family hRflow hr₀ hY hd hfix harea hg hsamples
      hq hqE hT ηctrl Kextra hηctrl hKextra hηa hηgap
  have hbI : (b : ℝ) ∈ Ioo (0 : ℝ) (1 / 4) := ⟨hb, hbquarter⟩
  obtain ⟨c₀, hc₀, Lback, hLback, tmin, htmin, hlate⟩ :=
    P.exists_firstTransfer_uniform_late_response_and_lookback hbI hnonzero hsCanon hChistory.le hηctrl.le
  refine ⟨b, hb, hbquarter, hnonzero, hslow, δ, hδ, sCanon, hsCanon, hcanonδ,
    Henv, hHenv, Chistory, hChistory, c₀ / 2, half_pos hc₀,
    Lback, hLback, tmin, htmin, ?_⟩
  intro tstar htstar
  obtain ⟨hdpos, hresponseLower, hlead, htail⟩ := hlate tstar htstar
  let κ₀ := ‖retardedSol (((b : ℝ) : ℂ) * lamStar)
    (((b : ℝ) : ℂ) * (sigma + 5 / 4 * I)) Kstar P.moment tstar‖
  let d := tstar - sCanon
  have hκ₀ : 0 < κ₀ :=
    (mul_pos hc₀ (Real.exp_pos _)).trans_le hresponseLower
  have hhalf : (c₀ / 2) * Real.exp ((b : ℝ) * sigma * tstar) ≤ κ₀ / 2 := by
    convert div_le_div_of_nonneg_right hresponseLower (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  refine ⟨half_pos hκ₀, hhalf, ?_⟩
  intro seedMax hseedMax nMin
  obtain ⟨n, hn, hdata⟩ := hfamilies Lback hLback d hdpos seedMax hseedMax nMin
  dsimp only at hdata
  obtain ⟨hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobs, hfamily⟩ := hdata
  let s := -(n : ℝ) * (period + period)
  have hstrengthen := P.eventually_actual_firstTransfer_nonzero_of_input
    (b := b) (s := s) (A₀ := A₀) (D := D) (δ := δ) (sCanon := sCanon) (ηctrl := ηctrl)
    (Lback := Lback) (d := d) (Henv := Henv) (Chistory := Chistory) (Cmatch := Cmatch)
    (Cback := Cback) (Cb := Cb) (Ccur := Ccur) (Cobs := Cobs) (κ := κ₀) (tstar := tstar)
    hq hqE hb hbquarter hs hA hT.le hD.le hsCanon hLback hdpos hκ₀ hChistory.le hηctrl.le
    hCb.le hCcur.le hCobs.le rfl (by dsimp only [d]; ring) hlead htail
  refine ⟨n, hn, hs, A₀, hA, D, hD, Cmatch, hCmatch, Cback, hCback, Cb, hCb, Ccur, hCcur,
    Cobs, hCobs, hseed, hterminal, htime, hDobs, ?_⟩
  filter_upwards [hfamily, hstrengthen] with ξ hfamilyξ hstrengthenξ
  exact hstrengthenξ hfamilyξ

end CircularMaterialTransferProfile
end Euler2D

end
