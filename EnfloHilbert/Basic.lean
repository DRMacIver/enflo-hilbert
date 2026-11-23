import Mathlib

/-!
# Basic objects for the Enflo-style approach to the invariant subspace problem

This file formalises the parts of `tex/main.tex`, Section "Extremal series and the defect",
that do not depend on the extremal construction itself:

* `HasNontrivialInvariantSubspace T` : the conclusion we are after;
* `orbitAnnihilator T r` : the closed invariant subspace `{x | ∀ j, T^j x ⟂ r}`;
* `hasNontrivialInvariantSubspace_of_orbit_orthogonal` : the non-cyclicity criterion
  (tex: Lemma `lem:criterion`);
* `norm_sub_sq_eq_confinement` : the confinement identity (tex: Lemma `lem:confinement`).

Convention: Mathlib's inner product `⟪x, y⟫_ℂ` is conjugate-linear in `x`, while the paper and
the tex notes use `⟨a, b⟩` linear in `a`.  So the paper's `⟨a, b⟩` is `⟪b, a⟫_ℂ` here.
-/

open scoped InnerProductSpace

namespace EnfloHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T` has a closed invariant subspace other than `0` and `H`. -/
def HasNontrivialInvariantSubspace (T : H →L[ℂ] H) : Prop :=
  ∃ M : Submodule ℂ H, IsClosed (M : Set H) ∧ M ≠ ⊥ ∧ M ≠ ⊤ ∧ ∀ x ∈ M, T x ∈ M

/-- The set of vectors whose whole `T`-orbit is orthogonal to `r`. -/
def orbitAnnihilator (T : H →L[ℂ] H) (r : H) : Submodule ℂ H where
  carrier := {x | ∀ j : ℕ, ⟪r, (T ^ j) x⟫_ℂ = 0}
  add_mem' := by
    intro a b ha hb j
    rw [map_add, inner_add_right, ha j, hb j, add_zero]
  zero_mem' := by
    intro j
    simp
  smul_mem' := by
    intro c x hx j
    rw [map_smul, inner_smul_right, hx j, mul_zero]

theorem mem_orbitAnnihilator {T : H →L[ℂ] H} {r x : H} :
    x ∈ orbitAnnihilator T r ↔ ∀ j : ℕ, ⟪r, (T ^ j) x⟫_ℂ = 0 :=
  Iff.rfl

theorem isClosed_orbitAnnihilator (T : H →L[ℂ] H) (r : H) :
    IsClosed (orbitAnnihilator T r : Set H) := by
  have h : (orbitAnnihilator T r : Set H) = ⋂ j : ℕ, {x | ⟪r, (T ^ j) x⟫_ℂ = 0} := by
    ext x
    simp [mem_orbitAnnihilator]
  rw [h]
  exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const

theorem map_mem_orbitAnnihilator {T : H →L[ℂ] H} {r x : H}
    (hx : x ∈ orbitAnnihilator T r) : T x ∈ orbitAnnihilator T r := by
  intro j
  have := hx (j + 1)
  rwa [pow_succ, ContinuousLinearMap.mul_apply] at this

/-- **Non-cyclicity criterion.** If `v ≠ 0`, `r ≠ 0` and the whole orbit of `v` is orthogonal
to `r`, then `T` has a nontrivial closed invariant subspace.  In the application
`r = x₀ - v`. -/
theorem hasNontrivialInvariantSubspace_of_orbit_orthogonal (T : H →L[ℂ] H) {v r : H}
    (hv : v ≠ 0) (hr : r ≠ 0) (h : ∀ j : ℕ, ⟪r, (T ^ j) v⟫_ℂ = 0) :
    HasNontrivialInvariantSubspace T := by
  refine ⟨orbitAnnihilator T r, isClosed_orbitAnnihilator T r, ?_, ?_,
    fun x hx => map_mem_orbitAnnihilator hx⟩
  · intro hbot
    have hmem : v ∈ orbitAnnihilator T r := h
    rw [hbot] at hmem
    exact hv ((Submodule.mem_bot ℂ).1 hmem)
  · intro htop
    have hmem : r ∈ orbitAnnihilator T r := by
      rw [htop]
      exact Submodule.mem_top
    have h0 := hmem 0
    simp only [pow_zero, ContinuousLinearMap.one_apply] at h0
    exact hr (inner_self_eq_zero.1 h0)

/-- **Confinement identity.** For arbitrary `x₀, v, v'`,
`‖v - v'‖² = 2 Re⟨v, x₀ - v'⟩ - 2 Re⟨v', x₀ - v'⟩ + ‖x₀ - v‖² - ‖x₀ - v'‖²`.
When `v, v'` are extremal images, `Re⟨v', x₀ - v'⟩` is the defect of `v'`, so holding
`Re⟨v, x₀ - v'⟩` fixed confines `v` to a small ball around `v'`. -/
theorem norm_sub_sq_eq_confinement (x₀ v v' : H) :
    ‖v - v'‖ ^ 2 = 2 * RCLike.re ⟪x₀ - v', v⟫_ℂ - 2 * RCLike.re ⟪x₀ - v', v'⟫_ℂ
      + ‖x₀ - v‖ ^ 2 - ‖x₀ - v'‖ ^ 2 := by
  have h1 : v - v' = (x₀ - v') - (x₀ - v) := by abel
  have h2 : RCLike.re ⟪x₀ - v', v⟫_ℂ - RCLike.re ⟪x₀ - v', v'⟫_ℂ
      = ‖x₀ - v'‖ ^ 2 - RCLike.re ⟪x₀ - v', x₀ - v⟫_ℂ := by
    have hn := inner_self_eq_norm_sq (𝕜 := ℂ) (x₀ - v')
    have e : RCLike.re ⟪x₀ - v', v⟫_ℂ - RCLike.re ⟪x₀ - v', v'⟫_ℂ
        = RCLike.re ⟪x₀ - v', x₀ - v'⟫_ℂ - RCLike.re ⟪x₀ - v', x₀ - v⟫_ℂ := by
      simp only [inner_sub_right, map_sub]
      ring
    rw [e, hn]
  rw [h1, @norm_sub_sq ℂ]
  linarith

end EnfloHilbert
