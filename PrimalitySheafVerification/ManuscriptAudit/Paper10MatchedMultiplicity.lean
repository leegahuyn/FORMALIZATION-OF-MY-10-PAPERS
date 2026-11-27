import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Spectrum
import PrimalitySheafVerification.ManuscriptAudit.RSMassGap

/-! The matched null space may contain a repeated ground level even with exact ground normalization. -/

namespace ManuscriptAudit.Paper10MatchedMultiplicity

open Module.End
open scoped InnerProductSpace

noncomputable section

abbrev E := EuclideanSpace ℝ (Fin 3)

def coefficient (i : Fin 3) : ℝ := if i = 2 then 3 else 2

def hamiltonian : Module.End ℝ E where
  toFun x := WithLp.toLp 2 (fun i => coefficient i * x i)
  map_add' x y := by
    apply PiLp.ext
    intro i
    exact mul_add _ _ _
  map_smul' r x := by
    apply PiLp.ext
    intro i
    exact mul_left_comm _ _ _

@[simp] theorem hamiltonian_apply (x : E) (i : Fin 3) :
    hamiltonian x i = coefficient i * x i := rfl

private theorem inner_coordinates (x y : E) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp [add_assoc] <;> ring

private theorem norm_sq_coordinates (x : E) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp [add_assoc]

theorem hamiltonian_symmetric : hamiltonian.IsSymmetric := by
  intro x y
  simp only [inner_coordinates, hamiltonian_apply]
  ring

def boundedHamiltonian : E →L[ℝ] E := LinearMap.toContinuousLinearMap hamiltonian

theorem bounded_hamiltonian_selfAdjoint : IsSelfAdjoint boundedHamiltonian := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  simpa only [boundedHamiltonian, LinearMap.coe_toContinuousLinearMap] using hamiltonian_symmetric

def axis (i : Fin 3) : E := EuclideanSpace.single i 1

def matched : Submodule ℝ E := LinearMap.ker (EuclideanSpace.projₗ 2)

@[simp] theorem mem_matched (x : E) : x ∈ matched ↔ x 2 = 0 := Iff.rfl

theorem matched_is_ground_eigenspace : matched = eigenspace hamiltonian 2 := by
  ext x
  rw [mem_matched, mem_eigenspace_iff]
  constructor
  · intro hx
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hamiltonian_apply, coefficient, hx]
  · intro hx
    have h := congrArg (fun y : E => y 2) hx
    norm_num [hamiltonian_apply, coefficient, PiLp.smul_apply, smul_eq_mul] at h
    linarith

private theorem ambient_finrank : Module.finrank ℝ E = 3 := by
  simp [E]

theorem matched_finrank : Module.finrank ℝ matched = 2 := by
  let projection : E →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 2
  have hs : Function.Surjective projection := by
    intro r
    refine ⟨EuclideanSpace.single (2 : Fin 3) r, ?_⟩
    change (EuclideanSpace.single (2 : Fin 3) r) 2 = r
    simp
  have hd := LinearMap.finrank_range_add_finrank_ker projection
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    ambient_finrank] at hd
  change 1 + Module.finrank ℝ matched = 3 at hd
  omega

@[simp] theorem mem_matched_orthogonal (x : E) :
    x ∈ matchedᗮ ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    have h₀ : axis 0 ∈ matched := by simp [axis]
    have h₁ : axis 1 ∈ matched := by simp [axis]
    constructor
    · simpa [axis, inner_coordinates] using h (axis 0) h₀
    · simpa [axis, inner_coordinates] using h (axis 1) h₁
  · rintro ⟨h₀, h₁⟩ y hy
    simp [inner_coordinates, h₀, h₁, (mem_matched y).mp hy]

def mass (x : E) : ℝ := (x 2)^2

theorem exact_ground_normalized_hypotheses :
    matched = eigenspace hamiltonian 2 ∧
      (∀ x, 0 ≤ mass x) ∧
      (∀ x ∈ matchedᗮ, ‖x‖^2 ≤ mass x) ∧
      (∀ x, mass x + 2*‖x‖^2 = inner ℝ x (hamiltonian x)) ∧
      (∃ x ∈ matchedᗮ, x ≠ 0) := by
  refine ⟨matched_is_ground_eigenspace, fun x => sq_nonneg _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h₀, h₁⟩ := (mem_matched_orthogonal x).mp hx
    rw [norm_sq_coordinates, h₀, h₁]
    simp [mass]
  · intro x
    rw [norm_sq_coordinates]
    simp only [mass, inner_coordinates, hamiltonian_apply]
    have h₀ : (0 : Fin 3) ≠ 2 := by decide
    have h₁ : (1 : Fin 3) ≠ 2 := by decide
    simp [coefficient, h₀, h₁] <;> ring
  · exact ⟨axis 2, by simp [axis], by simp [axis, PiLp.single_eq_zero_iff]⟩

/-- The real eigenvalues in decreasing order, including multiplicities. -/
def levels : Fin 3 → ℝ := hamiltonian_symmetric.eigenvalues ambient_finrank

private theorem level_values (i : Fin 3) : levels i = 2 ∨ levels i = 3 := by
  obtain ⟨x, hx⟩ := (hamiltonian_symmetric.hasEigenvalue_eigenvalues ambient_finrank i).exists_hasEigenvector
  have hcoord : ∃ j : Fin 3, x j ≠ 0 := by
    by_contra! h
    apply hx.2
    apply PiLp.ext
    intro j
    simpa using h j
  obtain ⟨j, hj⟩ := hcoord
  have he : coefficient j * x j = levels i * x j := by
    simpa only [levels, hamiltonian_apply, PiLp.smul_apply, smul_eq_mul,
      RCLike.ofReal_real_eq_id, id_eq] using
      congrArg (fun y : E => y j) hx.apply_eq_smul
  have hm : (coefficient j - levels i) * x j = 0 := by rw [sub_mul, he, sub_self]
  have hv : coefficient j = levels i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hj)
  rw [← hv]
  by_cases h : j = 2 <;> simp [coefficient, h]

theorem lowest_two_levels_equal : levels 2 = 2 ∧ levels 1 = 2 ∧ levels 0 = 3 := by
  classical
  have he : Module.finrank ℝ (eigenspace hamiltonian 2) = 2 := by
    rw [← matched_is_ground_eigenspace]
    exact matched_finrank
  have hcard : Finset.card {i : Fin 3 | levels i = 2} = 2 := by
    have h := hamiltonian_symmetric.card_filter_eigenvalues_eq ambient_finrank (2 : ℝ)
    rw [he] at h
    refine Eq.trans ?_ h
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, levels,
      RCLike.ofReal_real_eq_id, id_eq]
  have hmono : Antitone levels := hamiltonian_symmetric.eigenvalues_antitone ambient_finrank
  have h₀ : levels 0 = 3 := by
    rcases level_values 0 with he | he
    · have hall (i : Fin 3) : levels i = 2 := by
        have hle := hmono (show (0 : Fin 3) ≤ i from bot_le)
        rw [he] at hle
        rcases level_values i with hi | hi
        · exact hi
        · linarith
      simp [hall] at hcard
    · exact he
  have hnot₀ : levels 0 ≠ 2 := by rw [h₀]; norm_num
  have h₁ : levels 1 = 2 := by
    by_contra h
    have hsub : Finset.univ.filter (fun i : Fin 3 => levels i = 2) ⊆ ({2} : Finset (Fin 3)) := by
      intro i hi
      fin_cases i <;> simp_all
    have hh := Finset.card_le_card hsub
    rw [hcard] at hh
    simp at hh
  have h₂ : levels 2 = 2 := by
    have hh := hmono (show (1 : Fin 3) ≤ 2 by decide)
    rw [h₁] at hh
    rcases level_values 2 with he | he
    · exact he
    · linarith
  exact ⟨h₂, h₁, h₀⟩

theorem multiplicity_gap_is_zero : levels 1 - levels 2 = 0 := by
  rw [lowest_two_levels_equal.1, lowest_two_levels_equal.2.1, sub_self]

end
end ManuscriptAudit.Paper10MatchedMultiplicity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10MatchedMultiplicity.bounded_hamiltonian_selfAdjoint,
      ``ManuscriptAudit.Paper10MatchedMultiplicity.matched_finrank,
      ``ManuscriptAudit.Paper10MatchedMultiplicity.exact_ground_normalized_hypotheses,
      ``ManuscriptAudit.Paper10MatchedMultiplicity.lowest_two_levels_equal,
      ``ManuscriptAudit.Paper10MatchedMultiplicity.multiplicity_gap_is_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
