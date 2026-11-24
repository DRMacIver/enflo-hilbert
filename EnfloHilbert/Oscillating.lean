import EnfloHilbert.Rigidity

/-!
# Oscillating states cannot be continued

Let `W` be an isometry of `H` and `v = ½ (x + W x)`.  In the model operator,
`W = exp (i N T)` is multiplication by `e^{iNλ}` and `v` is the oscillating state `v_N` of the
notes (with `A = ∅`).  This file proves, with no spectral theory:

* `oscillating_lower_bound` : for every `u`,
  `‖u - v‖² ≥ ¼ (‖x‖² - ‖½ (W x + W* x)‖²) + ½ Re⟨(W - W*) u, x - u⟩`;
* `norm_inner_hasSum_pow_le` : if `W = ∑ c_k T^k` with `∑ ‖c_k‖ < ∞` and all `|⟨T^k u, r⟩| ≤ Δ`,
  then `|⟨W u, r⟩| ≤ (∑ ‖c_k‖) Δ`;
* `oscillating_ball_bound` : combining the two, the defect of `u` is bounded below in terms of
  `‖u - v‖`;
* `oscillating_defect` : if `W` is unitary and commutes with `T`, then
  `⟨T^j v, x - v⟩ = ¼ ⟨T^j (W - W*) x, x⟩`.

(tex: Theorem `thm:abstract-nogo`.)
-/

open scoped InnerProductSpace
open ContinuousLinearMap RCLike

namespace EnfloHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Rigidity inequality for a skew-adjoint `B`. -/
theorem rigidity_skewAdjoint {B : H →L[ℂ] H} (hB : adjoint B = -B) (u v x : H) :
    ‖v‖ ^ 2 - ‖v + B x‖ ^ 2 ≤ ‖u - v‖ ^ 2 + 2 * re ⟪x - u, B u⟫_ℂ := by
  have hd : ∀ a : H, defectForm B a = a := by
    intro a
    unfold defectForm
    rw [hB]
    simp
  have hz : v - (adjoint B) x = v + B x := by
    rw [hB]
    simp
  have key := rigidity_inequality B
    (fun a => by
      rw [hd]
      exact inner_self_nonneg (𝕜 := ℂ))
    u v x (v + B x) (by rw [hd, hz])
  rw [hz] at key
  have hn : re ⟪v + B x, v + B x⟫_ℂ = ‖v + B x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  linarith

/-- **Lower bound near an oscillating state.** -/
theorem oscillating_lower_bound (W : H →L[ℂ] H) (hW : ∀ a : H, ‖W a‖ = ‖a‖) (x u : H) :
    (1 / 4 : ℝ) * (‖x‖ ^ 2 - ‖(1 / 2 : ℂ) • (W x + (adjoint W) x)‖ ^ 2)
      ≤ ‖u - (1 / 2 : ℂ) • (x + W x)‖ ^ 2
        - (1 / 2 : ℝ) * re ⟪x - u, (W - adjoint W) u⟫_ℂ := by
  set B : H →L[ℂ] H := (-(1 / 4 : ℂ)) • (W - adjoint W) with hBdef
  have hB : adjoint B = -B := by
    have h1 : adjoint B = star B := rfl
    rw [h1, hBdef, star_smul, star_sub]
    have h2 : star (adjoint W) = W := by
      change adjoint (adjoint W) = W
      exact adjoint_adjoint W
    have h3 : star W = adjoint W := rfl
    rw [h2, h3]
    have h4 : star (-(1 / 4 : ℂ)) = -(1 / 4 : ℂ) := by
      simp
    rw [h4]
    ext a
    simp
    module
  have key := rigidity_skewAdjoint hB u ((1 / 2 : ℂ) • (x + W x)) x
  -- identify the two vectors
  have hv : (1 / 2 : ℂ) • (x + W x) + B x
      = (1 / 2 : ℂ) • x + (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (W x + (adjoint W) x)) := by
    simp only [hBdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
    module
  rw [hv] at key
  set c : H := (1 / 2 : ℂ) • (W x + (adjoint W) x) with hc
  -- norms
  have n1 : ‖(1 / 2 : ℂ) • (x + W x)‖ ^ 2
      = (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * re ⟪x, W x⟫_ℂ := by
    rw [norm_smul, mul_pow, @norm_add_sq ℂ, hW x]
    norm_num
    ring
  have hxc : re ⟪x, c⟫_ℂ = re ⟪x, W x⟫_ℂ := by
    rw [hc, inner_smul_right, inner_add_right, adjoint_inner_right]
    have hs : re ⟪W x, x⟫_ℂ = re ⟪x, W x⟫_ℂ := inner_re_symm (𝕜 := ℂ) _ _
    have : ((1 / 2 : ℂ) * (⟪x, W x⟫_ℂ + ⟪W x, x⟫_ℂ)).re
        = (1 / 2 : ℝ) * (re ⟪x, W x⟫_ℂ + re ⟪W x, x⟫_ℂ) := by
      simp [Complex.mul_re]
    change ((1 / 2 : ℂ) * (⟪x, W x⟫_ℂ + ⟪W x, x⟫_ℂ)).re = _
    rw [this, hs]
    ring
  have n2 : ‖(1 / 2 : ℂ) • x + (1 / 2 : ℂ) • c‖ ^ 2
      = (1 / 4 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * re ⟪x, c⟫_ℂ + (1 / 4 : ℝ) * ‖c‖ ^ 2 := by
    rw [← smul_add, norm_smul, mul_pow, @norm_add_sq ℂ]
    norm_num
    ring
  -- the inner product term
  have hin : re ⟪x - u, B u⟫_ℂ = -(1 / 4 : ℝ) * re ⟪x - u, (W - adjoint W) u⟫_ℂ := by
    rw [hBdef, ContinuousLinearMap.smul_apply, inner_smul_right]
    change ((-(1 / 4 : ℂ)) * ⟪x - u, (W - adjoint W) u⟫_ℂ).re = _
    simp [Complex.mul_re]
  rw [n1, n2, hxc, hin] at key
  linarith

omit [CompleteSpace H] in
/-- If `W = ∑ c_k T^k` with summable coefficient norms and every `|⟨T^k u, r⟩| ≤ Δ`, then
`|⟨W u, r⟩| ≤ (∑ ‖c_k‖) Δ`. -/
theorem norm_inner_hasSum_pow_le (T W : H →L[ℂ] H) (c : ℕ → ℂ)
    (hsum : HasSum (fun k => c k • T ^ k) W) (hc : Summable fun k => ‖c k‖)
    (u r : H) (Δ : ℝ) (h : ∀ j, ‖⟪r, (T ^ j) u⟫_ℂ‖ ≤ Δ) :
    ‖⟪r, W u⟫_ℂ‖ ≤ (∑' k, ‖c k‖) * Δ := by
  -- the continuous linear functional `A ↦ ⟪r, A u⟫`
  let φ : (H →L[ℂ] H) →L[ℂ] ℂ := (innerSL ℂ r).comp (ContinuousLinearMap.apply ℂ H u)
  have hφ : ∀ A : H →L[ℂ] H, φ A = ⟪r, A u⟫_ℂ := fun A => rfl
  have hs : HasSum (fun k => φ (c k • T ^ k)) (φ W) := hsum.mapL φ
  have hterm : ∀ k, ‖φ (c k • T ^ k)‖ ≤ ‖c k‖ * Δ := by
    intro k
    rw [hφ, ContinuousLinearMap.smul_apply, inner_smul_right, norm_mul]
    exact mul_le_mul_of_nonneg_left (h k) (norm_nonneg _)
  have hsumm : Summable fun k => ‖c k‖ * Δ := hc.mul_right Δ
  rw [← hφ, ← hs.tsum_eq]
  calc ‖∑' k, φ (c k • T ^ k)‖ ≤ ∑' k, ‖c k‖ * Δ :=
        tsum_of_norm_bounded hsumm.hasSum hterm
    _ = (∑' k, ‖c k‖) * Δ := tsum_mul_right

/-- **No continuation from an oscillating state.** Let `W` be an isometry such that both `W`
and `W*` are `ℓ¹` power series in `T` with coefficient sums at most `K`.  If all orbit pairings
`|⟨T^j u, x - u⟩|` are at most `Δ`, then
`‖u - v‖² ≥ ¼ (‖x‖² - ‖½ (W x + W* x)‖²) - K Δ` for `v = ½ (x + W x)`. -/
theorem oscillating_ball_bound (T W : H →L[ℂ] H) (hW : ∀ a : H, ‖W a‖ = ‖a‖)
    (c c' : ℕ → ℂ) (hsum : HasSum (fun k => c k • T ^ k) W)
    (hsum' : HasSum (fun k => c' k • T ^ k) (adjoint W))
    (hc : Summable fun k => ‖c k‖) (hc' : Summable fun k => ‖c' k‖)
    (K : ℝ) (hK : ∑' k, ‖c k‖ ≤ K) (hK' : ∑' k, ‖c' k‖ ≤ K)
    (x u : H) (Δ : ℝ) (h : ∀ j, ‖⟪x - u, (T ^ j) u⟫_ℂ‖ ≤ Δ) :
    (1 / 4 : ℝ) * (‖x‖ ^ 2 - ‖(1 / 2 : ℂ) • (W x + (adjoint W) x)‖ ^ 2) - K * Δ
      ≤ ‖u - (1 / 2 : ℂ) • (x + W x)‖ ^ 2 := by
  have hΔ : 0 ≤ Δ := (norm_nonneg _).trans (h 0)
  have b1 := norm_inner_hasSum_pow_le T W c hsum hc u (x - u) Δ h
  have b2 := norm_inner_hasSum_pow_le T (adjoint W) c' hsum' hc' u (x - u) Δ h
  have b1' : ‖⟪x - u, W u⟫_ℂ‖ ≤ K * Δ := b1.trans (mul_le_mul_of_nonneg_right hK hΔ)
  have b2' : ‖⟪x - u, (adjoint W) u⟫_ℂ‖ ≤ K * Δ := b2.trans (mul_le_mul_of_nonneg_right hK' hΔ)
  have hre : |re ⟪x - u, (W - adjoint W) u⟫_ℂ| ≤ 2 * (K * Δ) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
    have r1 : |re ⟪x - u, W u⟫_ℂ| ≤ K * Δ := (abs_re_le_norm _).trans b1'
    have r2 : |re ⟪x - u, (adjoint W) u⟫_ℂ| ≤ K * Δ := (abs_re_le_norm _).trans b2'
    have := (abs_sub (re ⟪x - u, W u⟫_ℂ) (re ⟪x - u, (adjoint W) u⟫_ℂ)).trans
      (add_le_add r1 r2)
    linarith
  have key := oscillating_lower_bound W hW x u
  have := abs_le.1 hre
  linarith [this.1, this.2]

/-- The defect pairings of the oscillating state: if `W` is unitary and commutes with `T`, then
`⟨T^j v, x - v⟩ = ¼ ⟨T^j (W - W*) x, x⟩` for `v = ½ (x + W x)`. -/
theorem oscillating_defect (T W : H →L[ℂ] H) (hW : adjoint W * W = 1)
    (hcomm : Commute W T) (hcomm' : Commute (adjoint W) T) (x : H) (j : ℕ) :
    ⟪x - (1 / 2 : ℂ) • (x + W x), (T ^ j) ((1 / 2 : ℂ) • (x + W x))⟫_ℂ
      = (1 / 4 : ℂ) * ⟪x, (T ^ j) ((W - adjoint W) x)⟫_ℂ := by
  have e1 : x - (1 / 2 : ℂ) • (x + W x) = (1 / 2 : ℂ) • (x - W x) := by module
  have hWW : ∀ a b : H, ⟪W a, W b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro a b
    rw [← adjoint_inner_right, ← ContinuousLinearMap.mul_apply, hW,
      ContinuousLinearMap.one_apply]
  have c1 : (T ^ j) (W x) = W ((T ^ j) x) := by
    have := (hcomm.pow_right j).eq
    rw [← ContinuousLinearMap.mul_apply, ← this, ContinuousLinearMap.mul_apply]
  have c2 : (T ^ j) ((adjoint W) x) = (adjoint W) ((T ^ j) x) := by
    have := (hcomm'.pow_right j).eq
    rw [← ContinuousLinearMap.mul_apply, ← this, ContinuousLinearMap.mul_apply]
  rw [e1, map_smul, inner_smul_left, inner_smul_right, map_add, inner_sub_left,
    inner_add_right, inner_add_right, ContinuousLinearMap.sub_apply, map_sub, inner_sub_right,
    c1, c2, hWW, adjoint_inner_right]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_eq_iff_real.2 ⟨2, by norm_num⟩
  simp only [one_div, map_inv₀, coe_pow']
  rw [h2]
  ring

end EnfloHilbert
