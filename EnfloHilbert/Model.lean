import Mathlib

/-!
# Pointwise identities behind the rigidity theorem in the model operator

In the model `T = multiplication by λ on L²[0, κ]` (tex: Section "Rigidity in the model"), write
`v = x₀ g` and `u = x₀ h`.  Then `u · conj (x₀ - u) = |x₀|² (h - |h|²)`, and the theorem that
sequences with defect tending to `0` cannot stay closer to `v` than the true solutions rests on
the two pointwise identities below (tex: Lemma `lem:pointwise`).
-/

open Complex ComplexConjugate

namespace EnfloHilbert

/-- Expansion around the solution value `0`; the term `(1 - 2 g.re) * normSq h` is
non-negative when `g.re ≤ 1/2`. -/
theorem normSq_sub_eq_left (g h : ℂ) :
    normSq (h - g) = normSq g + (1 - 2 * g.re) * normSq h
      - 2 * (conj g * (h - (normSq h : ℂ))).re := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, conj_re, conj_im, ofReal_re,
    ofReal_im]
  ring

/-- Expansion around the solution value `1`; the term `(2 g.re - 1) * normSq (1 - h)` is
non-negative when `g.re ≥ 1/2`. -/
theorem normSq_sub_eq_right (g h : ℂ) :
    normSq (h - g) = normSq (1 - g) + (2 * g.re - 1) * normSq (1 - h)
      - 2 * ((1 - g) * (h - (normSq h : ℂ))).re := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, one_re, one_im, ofReal_re,
    ofReal_im]
  ring

/-- Lower bound used when `g.re ≤ 1/2`. -/
theorem normSq_sub_ge_left {g : ℂ} (hg : g.re ≤ 1 / 2) (h : ℂ) :
    normSq g - 2 * (conj g * (h - (normSq h : ℂ))).re ≤ normSq (h - g) := by
  rw [normSq_sub_eq_left g h]
  have : 0 ≤ (1 - 2 * g.re) * normSq h := mul_nonneg (by linarith) (normSq_nonneg h)
  linarith

/-- Lower bound used when `g.re ≥ 1/2`. -/
theorem normSq_sub_ge_right {g : ℂ} (hg : 1 / 2 ≤ g.re) (h : ℂ) :
    normSq (1 - g) - 2 * ((1 - g) * (h - (normSq h : ℂ))).re ≤ normSq (h - g) := by
  rw [normSq_sub_eq_right g h]
  have : 0 ≤ (2 * g.re - 1) * normSq (1 - h) := mul_nonneg (by linarith) (normSq_nonneg _)
  linarith

end EnfloHilbert
