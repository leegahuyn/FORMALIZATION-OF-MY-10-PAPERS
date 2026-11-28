import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Dimension.Constructions
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsRayleigh
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsFiniteSpectrum

/-! Exact variational counting below an energy threshold for the actual form. -/

namespace ManuscriptAudit.Paper10FriedrichsCounting

open Paper10FriedrichsResolvent Paper10FriedrichsDomainSpectrum Paper10FriedrichsRayleigh

noncomputable section

variable {D H I : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (J : D →L[ℝ] H) (hJ : DenseRange J) (hInj : Function.Injective J)
variable (b : HilbertBasis I ℝ H) (e : I → ℝ)
variable (he : ∀ i, (b i, e i • b i) ∈ (realization J).graph)

/-- The form-domain subspace supported on the eigenvalues strictly below the cutoff. -/
def below (R : ℝ) : Submodule ℝ D where
  carrier := {u | ∀ i, R ≤ e i → b.repr (J u) i = 0}
  zero_mem' := by
    intro i hi
    simp
  add_mem' := by
    intro x y hx hy i hi
    simp only [Set.mem_setOf_eq] at hx hy
    rw [map_add, map_add]
    change b.repr (J x) i + b.repr (J y) i = 0
    rw [hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro c x hx i hi
    simp only [Set.mem_setOf_eq] at hx
    rw [map_smul, map_smul]
    change c * b.repr (J x) i = 0
    rw [hx i hi, mul_zero]

include hJ hInj he in
/-- The actual low-energy coordinate map has the full function space on the low
indices as target, and the form energy there is strictly below the cutoff. -/
theorem below_equiv (R : ℝ) [Finite {i // e i < R}] :
    (∀ u : below J b e R, u ≠ 0 → ‖(u : D)‖^2 < R * ‖J u‖^2) ∧
    Nonempty (below J b e R ≃ₗ[ℝ] ({i // e i < R} → ℝ)) := by
  classical
  let W := below J b e R
  have hW (u : W) (hu : u ≠ 0) : ‖(u : D)‖^2 < R * ‖J u‖^2 := by
    apply rayleigh_lt_of_high_coordinates_zero J hJ hInj b e he R (u : D)
    · intro h
      exact hu (Subtype.ext h)
    · exact u.property
  obtain ⟨P, hP, hp⟩ := exists_injective_low_coordinates J hJ hInj b e he R W hW
  refine ⟨hW, ⟨LinearEquiv.ofBijective P ⟨hP, ?_⟩⟩⟩
  intro a
  let f (i : I) : ℝ := if hi : e i < R then a ⟨i, hi⟩ else 0
  let g (i : I) : ℝ := Real.sqrt (e i) * f i
  have hFinite : ({i : I | g i ≠ 0} : Set I).Finite := by
    apply (Set.finite_range (Subtype.val : {i // e i < R} → I)).subset
    intro i hi
    by_cases h : e i < R
    · exact ⟨⟨i, h⟩, rfl⟩
    · exact (hi (by simp [g, f, h])).elim
  have hg₀ : Memℓp g 0 := memℓp_zero_iff.mpr hFinite
  let G : lp (fun _ : I => ℝ) 2 := ⟨g, hg₀.of_exponent_ge (by norm_num)⟩
  obtain ⟨d, hd⟩ := exists_form_basis J hJ hInj b e he
  let u := d.repr.symm G
  have hU (i : I) : b.repr (J u) i = f i := by
    have hi := hd u i
    rw [show d.repr u = G from d.repr.apply_symm_apply G] at hi
    change Real.sqrt (e i) * f i = Real.sqrt (e i) * b.repr (J u) i at hi
    exact mul_left_cancel₀ (Real.sqrt_pos.mpr (positive_label J hJ b e he i)).ne' hi.symm
  have hu : u ∈ W := by
    intro i hi
    rw [hU, show f i = 0 from dif_neg (not_lt_of_ge hi)]
  refine ⟨⟨u, hu⟩, ?_⟩
  funext i
  rw [hp, hU]
  exact dif_pos i.property

include hJ hInj in
/-- For a compact form inclusion, the spectral count below a real energy is exactly
the largest dimension on which every nonzero vector has Rayleigh energy below it. -/
theorem variational_count (hK : IsCompactOperator J)
    (b₀ : HilbertBasis (Paper10FriedrichsEigenbasis.EigenIndex J) ℝ H)
    (hb₀ : ∀ i, (b₀ i, i.1 • b₀ i) ∈ (realization J).graph) (R : ℝ) :
    let Low := {i : Paper10FriedrichsEigenbasis.EigenIndex J // i.1 < R}
    (∃ W : Submodule ℝ D, Module.finrank ℝ W = Nat.card Low ∧
      ∀ u : W, u ≠ 0 → ‖(u : D)‖^2 < R * ‖J u‖^2) ∧
    (∀ W : Submodule ℝ D,
      (∀ u : W, u ≠ 0 → ‖(u : D)‖^2 < R * ‖J u‖^2) →
      Module.finrank ℝ W ≤ Nat.card Low) := by
  classical
  let Low := {i : Paper10FriedrichsEigenbasis.EigenIndex J // i.1 < R}
  let E₀ (i : Paper10FriedrichsEigenbasis.EigenIndex J) : ℝ := i.1
  let M := max 1 R
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  letI := Paper10FriedrichsFiniteSpectrum.finite_bounded_basis_indices J hJ hK b₀ hb₀ M hM
  let j : Low → {i : Paper10FriedrichsEigenbasis.EigenIndex J // ‖i.1‖ ≤ M} :=
    fun i => ⟨i.val, by
      have h := positive_label J hJ b₀ E₀ hb₀ i.val
      change 0 < i.val.1 at h
      rw [Real.norm_eq_abs, abs_of_pos h]
      exact i.property.le.trans (le_max_right _ _)⟩
  letI : Finite Low := Finite.of_injective j
    (fun i k h => Subtype.ext (congrArg (fun v : {i : Paper10FriedrichsEigenbasis.EigenIndex J // ‖i.1‖ ≤ M} => v.val) h))
  letI : Fintype Low := Fintype.ofFinite Low
  have hCard : Module.finrank ℝ (Low → ℝ) = Nat.card Low := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨hLow, ⟨equiv⟩⟩ := below_equiv J hJ hInj b₀ E₀ hb₀ R
  refine ⟨⟨below J b₀ E₀ R, equiv.finrank_eq.trans hCard, hLow⟩, ?_⟩
  intro W hW
  obtain ⟨π, hπ, _⟩ := exists_injective_low_coordinates J hJ hInj b₀ E₀ hb₀ R W hW
  exact (LinearMap.finrank_le_finrank_of_injective hπ).trans hCard.le


end
end ManuscriptAudit.Paper10FriedrichsCounting

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsCounting.below_equiv,
      ``ManuscriptAudit.Paper10FriedrichsCounting.variational_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
