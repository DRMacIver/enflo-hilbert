import Mathlib

/-!
# The abstract rigidity inequality

For an arbitrary bounded operator `B` on a complex Hilbert space (in the application
`B = φ(T)` for a polynomial `φ`), and arbitrary vectors `u, v, x`:

  `‖u - v‖² + 2 Re⟨B u, x - u⟩ = ‖v‖² + Re⟨P u, u⟩ - 2 Re⟨u, v - B* x⟩`,  `P = I - B - B*`.

If `P ≥ 0` and `v - B* x = P z`, completing the square gives the lower bound
`‖u - v‖² + 2 Re⟨B u, x - u⟩ ≥ ‖v‖² - Re⟨v - B* x, z⟩`
(tex: Theorem `thm:abstract-rigidity`).  When the defect of `u` is small the term
`Re⟨B u, x - u⟩` is small, so `u` cannot be close to `v` unless the right side is small.

Convention: Mathlib's `⟪a, b⟫_ℂ` is conjugate-linear in `a`; the tex notes use `⟨b, a⟩`.
-/

open scoped InnerProductSpace
open ContinuousLinearMap RCLike

namespace EnfloHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `P = I - B - B*` applied to a vector. -/
noncomputable def defectForm (B : H →L[ℂ] H) (a : H) : H := a - B a - (adjoint B) a

theorem re_inner_defectForm_symm (B : H →L[ℂ] H) (a b : H) :
    re ⟪a, defectForm B b⟫_ℂ = re ⟪b, defectForm B a⟫_ℂ := by
  unfold defectForm
  simp only [inner_sub_right, map_sub, adjoint_inner_right]
  have h1 : re ⟪a, b⟫_ℂ = re ⟪b, a⟫_ℂ := inner_re_symm (𝕜 := ℂ) a b
  have h2 : re ⟪B a, b⟫_ℂ = re ⟪b, B a⟫_ℂ := inner_re_symm (𝕜 := ℂ) _ _
  have h3 : re ⟪B b, a⟫_ℂ = re ⟪a, B b⟫_ℂ := inner_re_symm (𝕜 := ℂ) _ _
  linarith

theorem defectForm_sub (B : H →L[ℂ] H) (a b : H) :
    defectForm B (a - b) = defectForm B a - defectForm B b := by
  unfold defectForm
  simp only [map_sub]
  abel

/-- The basic expansion. -/
theorem rigidity_expansion (B : H →L[ℂ] H) (u v x : H) :
    ‖u - v‖ ^ 2 + 2 * re ⟪x - u, B u⟫_ℂ
      = ‖v‖ ^ 2 + re ⟪u, defectForm B u⟫_ℂ - 2 * re ⟪u, v - (adjoint B) x⟫_ℂ := by
  unfold defectForm
  rw [@norm_sub_sq ℂ]
  simp only [inner_sub_left, inner_sub_right, map_sub, adjoint_inner_right]
  have h0 : re ⟪u, u⟫_ℂ = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have h1 : re ⟪B u, u⟫_ℂ = re ⟪u, B u⟫_ℂ := inner_re_symm (𝕜 := ℂ) _ _
  have h2 : re ⟪B u, x⟫_ℂ = re ⟪x, B u⟫_ℂ := inner_re_symm (𝕜 := ℂ) _ _
  linarith

/-- **Abstract rigidity inequality.** If `P = I - B - B*` is non-negative and
`v - B* x = P z`, then `‖u - v‖² + 2 Re⟨B u, x - u⟩ ≥ ‖v‖² - Re⟨v - B* x, z⟩` for every `u`. -/
theorem rigidity_inequality (B : H →L[ℂ] H)
    (hP : ∀ a : H, 0 ≤ re ⟪a, defectForm B a⟫_ℂ) (u v x z : H)
    (hz : defectForm B z = v - (adjoint B) x) :
    ‖v‖ ^ 2 - re ⟪z, v - (adjoint B) x⟫_ℂ ≤ ‖u - v‖ ^ 2 + 2 * re ⟪x - u, B u⟫_ℂ := by
  rw [rigidity_expansion, ← hz]
  have hsq := hP (u - z)
  rw [defectForm_sub, inner_sub_left, inner_sub_right, inner_sub_right] at hsq
  simp only [map_sub] at hsq
  have hs := re_inner_defectForm_symm B z u
  linarith

/-- If all the orbit pairings `⟨T^j u, r⟩` are bounded by `Δ`, then the pairing with a
polynomial in `T` is bounded by the `ℓ¹` norm of the coefficients times `Δ`. -/
theorem norm_inner_sum_pow_le (T : H →L[ℂ] H) (c : ℕ → ℂ) (n : ℕ) (u r : H) (Δ : ℝ)
    (h : ∀ j, ‖⟪r, (T ^ j) u⟫_ℂ‖ ≤ Δ) :
    ‖⟪r, (∑ j ∈ Finset.range n, c j • T ^ j) u⟫_ℂ‖ ≤ (∑ j ∈ Finset.range n, ‖c j‖) * Δ := by
  rw [ContinuousLinearMap.sum_apply, inner_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, norm_mul]
  exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)

/-- For self-adjoint `A`, the operator `B = i A` has `I - B - B* = I`. -/
theorem defectForm_I_smul {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (a : H) :
    defectForm (Complex.I • A) a = a := by
  have hadj : adjoint (Complex.I • A) = -(Complex.I • A) := by
    have h1 : adjoint (Complex.I • A) = star (Complex.I • A) := rfl
    rw [h1, star_smul, hA.star_eq]
    simp
  unfold defectForm
  rw [hadj]
  simp

/-- **Rigidity for self-adjoint operators.** If `A` is self-adjoint (in the application
`A = ψ(T)` with `T` self-adjoint and `ψ` a real polynomial), then for all `u, v, x`:
`‖u - v‖² + 2 Re⟨i A u, x - u⟩ ≥ ‖v‖² - ‖v + i A x‖²`
(tex: Remark `rem:DT`(b)). -/
theorem rigidity_selfAdjoint {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (u v x : H) :
    ‖v‖ ^ 2 - ‖v + Complex.I • A x‖ ^ 2
      ≤ ‖u - v‖ ^ 2 + 2 * re ⟪x - u, (Complex.I • A) u⟫_ℂ := by
  have hadj : adjoint (Complex.I • A) = -(Complex.I • A) := by
    have h1 : adjoint (Complex.I • A) = star (Complex.I • A) := rfl
    rw [h1, star_smul, hA.star_eq]
    simp
  have hz : v - (adjoint (Complex.I • A)) x = v + Complex.I • A x := by
    rw [hadj]
    simp
  have key := rigidity_inequality (Complex.I • A)
    (fun a => by
      rw [defectForm_I_smul hA]
      exact inner_self_nonneg (𝕜 := ℂ))
    u v x (v + Complex.I • A x)
    (by rw [defectForm_I_smul hA, hz])
  rw [hz] at key
  have hn : re ⟪v + Complex.I • A x, v + Complex.I • A x⟫_ℂ = ‖v + Complex.I • A x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  linarith

end EnfloHilbert
