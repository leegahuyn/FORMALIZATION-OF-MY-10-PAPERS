import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The mass-form gap inference and its truncation limit

Paper 10, physical PDF pp. 498–499, Proposition 4.23 and Corollary 4.25.
These examples concern the logical consequences of the quadratic-form and
exhaustion assumptions. They use a real Euclidean Hilbert space.
-/

namespace ManuscriptAudit.RSMassGap

open Module.End
open scoped InnerProductSpace

noncomputable section

abbrev E := EuclideanSpace ℝ (Fin 2)

def diagonal (a b : ℝ) : Module.End ℝ E where
  toFun x := WithLp.toLp 2 (fun i => (if i = 0 then a else b) * x i)
  map_add' x y := by
    apply PiLp.ext
    intro i
    change (if i = 0 then a else b) * (x i + y i) =
      (if i = 0 then a else b) * x i + (if i = 0 then a else b) * y i
    rw [mul_add]
  map_smul' r x := by
    apply PiLp.ext
    intro i
    change (if i = 0 then a else b) * (r * x i) = r * ((if i = 0 then a else b) * x i)
    rw [mul_left_comm]

private theorem diagonal_apply (a b : ℝ) (x : E) (i : Fin 2) :
    diagonal a b x i = (if i = 0 then a else b) * x i := rfl

@[simp] theorem diagonal_zero (a b : ℝ) (x : E) :
    diagonal a b x 0 = a * x 0 := by simp [diagonal_apply]

@[simp] theorem diagonal_one (a b : ℝ) (x : E) :
    diagonal a b x 1 = b * x 1 := by simp [diagonal_apply]

private theorem inner_coordinates (x y : E) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]

private theorem norm_sq_coordinates (x : E) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem diagonal_symmetric (a b : ℝ) : (diagonal a b).IsSymmetric := by
  intro x y
  simp only [inner_coordinates, diagonal_zero, diagonal_one]
  ring

def boundedDiagonal (a b : ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (diagonal a b)

theorem boundedDiagonal_selfAdjoint (a b : ℝ) : IsSelfAdjoint (boundedDiagonal a b) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  simpa only [boundedDiagonal, LinearMap.coe_toContinuousLinearMap] using diagonal_symmetric a b

def axis (i : Fin 2) : E := EuclideanSpace.single i 1

theorem axis_ne_zero (i : Fin 2) : axis i ≠ 0 := by
  simp [axis, PiLp.single_eq_zero_iff]

theorem diagonal_axis_eigenvector (a b : ℝ) (i : Fin 2) :
    HasEigenvector (diagonal a b) (if i = 0 then a else b) (axis i) := by
  refine ⟨mem_eigenspace_iff.mpr ?_, axis_ne_zero i⟩
  apply PiLp.ext
  intro j
  change diagonal a b (axis i) j = (if i = 0 then a else b) * axis i j
  by_cases h : j = i
  · subst j
    rw [diagonal_apply]
  · simp [diagonal_apply, axis, h]

theorem diagonal_spectrum_iff (a b μ : ℝ) :
    μ ∈ spectrum ℝ (diagonal a b) ↔ μ = a ∨ μ = b := by
  rw [← hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    by_cases hzero : x 0 = 0
    · right
      have hone : x 1 ≠ 0 := by
        intro he
        apply hx.2
        apply PiLp.ext
        intro i
        fin_cases i
        · exact hzero
        · exact he
      have he : b * x 1 = μ * x 1 := by
        have h' := congrArg (fun y : E => y 1) hx.apply_eq_smul
        simpa only [diagonal_one, PiLp.smul_apply, smul_eq_mul] using h'
      have hm : (b - μ) * x 1 = 0 := by rw [sub_mul, he, sub_self]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hone)).symm
    · left
      have he : a * x 0 = μ * x 0 := by
        have h' := congrArg (fun y : E => y 0) hx.apply_eq_smul
        simpa only [diagonal_zero, PiLp.smul_apply, smul_eq_mul] using h'
      have hm : (a - μ) * x 0 = 0 := by rw [sub_mul, he, sub_self]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hzero)).symm
  · intro h
    rcases h with h | h
    · rw [h]
      simpa using hasEigenvalue_of_hasEigenvector (diagonal_axis_eigenvector a b 0)
    · rw [h]
      simpa using hasEigenvalue_of_hasEigenvector (diagonal_axis_eigenvector a b 1)

def matched : Submodule ℝ E := LinearMap.ker (EuclideanSpace.projₗ 1)

@[simp] theorem mem_matched (x : E) : x ∈ matched ↔ x 1 = 0 := Iff.rfl

theorem matched_ne_bot : matched ≠ ⊥ := by
  intro h
  have hx : axis 0 ∈ matched := by simp [axis]
  have hbot : axis 0 ∈ (⊥ : Submodule ℝ E) := h ▸ hx
  exact axis_ne_zero 0 (by simpa using hbot)

theorem matched_ne_top : matched ≠ ⊤ := by
  intro h
  have hx : axis 1 ∈ matched := h.symm ▸ Submodule.mem_top
  simpa [axis] using hx

@[simp] theorem mem_matched_orthogonal (x : E) :
    x ∈ matchedᗮ ↔ x 0 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    have haxis : axis 0 ∈ matched := by simp [axis]
    simpa [axis, inner_coordinates] using h (axis 0) haxis
  · intro h y hy
    simp [inner_coordinates, h, (mem_matched y).mp hy]

theorem matched_eq_ground_eigenspace {b : ℝ} (hb : 2 < b) :
    matched = eigenspace (diagonal 2 b) 2 := by
  ext x
  rw [mem_matched, mem_eigenspace_iff]
  constructor
  · intro hx
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [diagonal_apply, hx]
  · intro hx
    have h : b * x 1 = 2 * x 1 := by
      have h' := congrArg (fun y : E => y 1) hx
      simpa only [diagonal_one, PiLp.smul_apply, smul_eq_mul] using h'
    have hm : (b - 2) * x 1 = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (ne_of_gt hb))

def mass (x : E) : ℝ := inner ℝ x (diagonal 0 1 x)

def hamiltonianForm (b : ℝ) (x : E) : ℝ := inner ℝ x (diagonal 2 b x)

private theorem mass_apply (x : E) : mass x = x 1 ^ 2 := by
  simp [mass, inner_coordinates, pow_two]

private theorem hamiltonianForm_apply (b : ℝ) (x : E) :
    hamiltonianForm b x = 2 * x 0 ^ 2 + b * x 1 ^ 2 := by
  simp only [hamiltonianForm, inner_coordinates, diagonal_zero, diagonal_one]
  ring

theorem mass_nonnegative (x : E) : 0 ≤ mass x := by
  rw [mass_apply]
  exact sq_nonneg _

theorem mass_on_matched_orthogonal {x : E} (hx : x ∈ matchedᗮ) :
    ‖x‖ ^ 2 = mass x := by
  simp [norm_sq_coordinates, mass_apply, (mem_matched_orthogonal x).mp hx]

theorem mass_le_hamiltonianForm {b : ℝ} (hb : 1 ≤ b) (x : E) :
    mass x ≤ hamiltonianForm b x := by
  rw [mass_apply, hamiltonianForm_apply]
  nlinarith only [sq_nonneg (x 0), mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (x 1))]

/-- Proposition 4.23's proposed gap estimate fails with `α = cRS = 1` and `β = 0`
even when the matched space is the full ground eigenspace. -/
theorem prop4_23_gap_bound_refuted :
    matched = eigenspace (diagonal 2 (5 / 2)) 2 ∧
    (∀ μ : ℝ, μ ∈ spectrum ℝ (diagonal 2 (5 / 2)) ↔ μ = 2 ∨ μ = 5 / 2) ∧
    (∀ x : E, 0 ≤ mass x ∧ mass x ≤ hamiltonianForm (5 / 2) x) ∧
    (∀ x ∈ matchedᗮ, ‖x‖ ^ 2 = mass x) ∧
    (0 : ℝ) ≤ 2 ∧ (5 / 2 : ℝ) - 2 < 1 :=
  ⟨matched_eq_ground_eigenspace (by norm_num), diagonal_spectrum_iff _ _,
    fun x => ⟨mass_nonnegative x, mass_le_hamiltonianForm (by norm_num) x⟩,
    fun _ hx => mass_on_matched_orthogonal hx, by norm_num, by norm_num⟩

/-- Dividing the complement form estimate by the positive squared norm retains
the term `β - lambda0` after shifting the Rayleigh quotient by the ground level. -/
theorem shifted_rayleigh_lower_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {T : F →ₗ[ℝ] F} {N : Submodule ℝ F} {M : F → ℝ}
    {alpha beta c lambda0 : ℝ}
    (ha : 0 ≤ alpha)
    (hdom : ∀ x, alpha * M x + beta * ‖x‖ ^ 2 ≤ inner ℝ x (T x))
    (hcoercive : ∀ x ∈ Nᗮ, c * ‖x‖ ^ 2 ≤ M x)
    {x : F} (hx : x ∈ Nᗮ) (hn : x ≠ 0) :
    alpha * c + beta - lambda0 ≤ inner ℝ x (T x) / ‖x‖ ^ 2 - lambda0 := by
  apply sub_le_sub_right
  rw [le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hn))]
  nlinarith only [hdom x, mul_le_mul_of_nonneg_left (hcoercive x hx) ha]

def upperLevel (Y : ℝ) : ℝ := 2 + Real.exp (-Y)

def gap (Y : ℝ) : ℝ := upperLevel Y - 2

def admissible (_Y : ℝ) : Submodule ℝ E := ⊤

theorem admissible_exhaustion :
    Monotone admissible ∧ (⨆ Y : ℝ, admissible Y) = ⊤ :=
  ⟨fun _ _ _ => le_rfl, top_unique (le_iSup admissible (0 : ℝ))⟩

theorem gap_eq_exp (Y : ℝ) : gap Y = Real.exp (-Y) := by
  simp [gap, upperLevel]

theorem gap_liminf_zero : Filter.liminf gap Filter.atTop = 0 := by
  rw [show gap = fun Y => Real.exp (-Y) from funext gap_eq_exp]
  exact Real.tendsto_exp_neg_atTop_nhds_zero.liminf_eq

/-- A constant admissible exhaustion has uniform mass coercivity and domination.
The exact off-ground gap is positive at every truncation and tends to zero. -/
theorem cor4_25_uniformly_coercive_gap_limit_counterexample :
    Monotone admissible ∧ (⨆ Y : ℝ, admissible Y) = ⊤ ∧
    (∀ Y : ℝ, matched = eigenspace (diagonal 2 (upperLevel Y)) 2 ∧
      (∀ μ : ℝ, μ ∈ spectrum ℝ (diagonal 2 (upperLevel Y)) ↔ μ = 2 ∨ μ = upperLevel Y) ∧
      (∀ x : E, 0 ≤ mass x ∧ mass x ≤ hamiltonianForm (upperLevel Y) x) ∧
      (∀ x ∈ matchedᗮ, ‖x‖ ^ 2 = mass x) ∧
      0 < gap Y) ∧
    Filter.liminf gap Filter.atTop = 0 := by
  refine ⟨admissible_exhaustion.1, admissible_exhaustion.2, ?_, gap_liminf_zero⟩
  intro Y
  have hb : 2 < upperLevel Y := by
    simpa [upperLevel] using Real.exp_pos (-Y)
  refine ⟨matched_eq_ground_eigenspace hb, diagonal_spectrum_iff _ _,
    fun x => ⟨mass_nonnegative x, mass_le_hamiltonianForm (by linarith) x⟩,
    fun _ hx => mass_on_matched_orthogonal hx, ?_⟩
  rw [gap_eq_exp]
  exact Real.exp_pos _

end

end ManuscriptAudit.RSMassGap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RSMassGap.boundedDiagonal_selfAdjoint,
      ``ManuscriptAudit.RSMassGap.matched_ne_bot,
      ``ManuscriptAudit.RSMassGap.matched_ne_top,
      ``ManuscriptAudit.RSMassGap.prop4_23_gap_bound_refuted,
      ``ManuscriptAudit.RSMassGap.shifted_rayleigh_lower_bound,
      ``ManuscriptAudit.RSMassGap.cor4_25_uniformly_coercive_gap_limit_counterexample] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
