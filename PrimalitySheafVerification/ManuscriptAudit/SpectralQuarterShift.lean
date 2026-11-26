import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# The quarter threshold under a constant potential shift

Paper 10, physical PDF p. 494 equation (4.42) and p. 500 before
Definition 4.6. A real constant times the identity is a bounded,
self-adjoint multiplication operator. Adding it translates eigenvalues
without altering eigenvectors or the domain of a partial Hamiltonian.
These results concern the bounded self-adjoint multiplier hypothesis.
-/

namespace ManuscriptAudit.SpectralQuarterShift

open Module.End
open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]

section Multipliers

variable [NormedSpace 𝕜 H]

def constantMultiplier (c : ℝ) : H →L[𝕜] H :=
  (c : 𝕜) • ContinuousLinearMap.id 𝕜 H

@[simp] theorem constantMultiplier_apply (c : ℝ) (x : H) :
    constantMultiplier (𝕜 := 𝕜) c x = (c : 𝕜) • x := by
  simp [constantMultiplier]

theorem constantMultiplier_norm (c : ℝ) (x : H) :
    ‖constantMultiplier (𝕜 := 𝕜) c x‖ = |c| * ‖x‖ := by
  rw [constantMultiplier_apply, norm_smul, RCLike.norm_ofReal]

def addConstantPotential (V : H →L[𝕜] H) (c : ℝ) : H →L[𝕜] H :=
  V + constantMultiplier c

@[simp] theorem addConstantPotential_apply (V : H →L[𝕜] H) (c : ℝ) (x : H) :
    addConstantPotential V c x = V x + (c : 𝕜) • x := by
  simp [addConstantPotential]

theorem addConstantPotential_norm_le (V : H →L[𝕜] H) {B : ℝ}
    (hB : ∀ x, ‖V x‖ ≤ B * ‖x‖) (c : ℝ) (x : H) :
    ‖addConstantPotential V c x‖ ≤ (B + |c|) * ‖x‖ := by
  calc
    ‖addConstantPotential V c x‖ ≤ ‖V x‖ + ‖constantMultiplier (𝕜 := 𝕜) c x‖ :=
      norm_add_le _ _
    _ = ‖V x‖ + |c| * ‖x‖ := by rw [constantMultiplier_norm]
    _ ≤ (B + |c|) * ‖x‖ := by
      rw [add_mul]
      exact add_le_add (hB x) le_rfl

theorem eigenvector_add_constant {T : H →L[𝕜] H} {lambda : ℝ} {x : H}
    (hx : HasEigenvector (T : Module.End 𝕜 H) (lambda : 𝕜) x) (c : ℝ) :
    HasEigenvector (addConstantPotential T c : Module.End 𝕜 H) ((lambda + c : ℝ) : 𝕜) x := by
  refine ⟨mem_eigenspace_iff.mpr ?_, hx.2⟩
  change addConstantPotential T c x = ((lambda + c : ℝ) : 𝕜) • x
  have h : T x = (lambda : 𝕜) • x := hx.apply_eq_smul
  rw [addConstantPotential_apply, h, RCLike.ofReal_add, add_smul]

end Multipliers

section Hilbert

variable [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem constantMultiplier_selfAdjoint (c : ℝ) :
    IsSelfAdjoint (constantMultiplier (𝕜 := 𝕜) (H := H) c) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change inner 𝕜 (constantMultiplier (𝕜 := 𝕜) c u) v =
    inner 𝕜 u (constantMultiplier (𝕜 := 𝕜) c v)
  simp only [constantMultiplier_apply, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]

theorem addConstantPotential_selfAdjoint {V : H →L[𝕜] H}
    (hV : IsSelfAdjoint V) (c : ℝ) : IsSelfAdjoint (addConstantPotential V c) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (hV.isSymmetric.add (constantMultiplier_selfAdjoint (𝕜 := 𝕜) (H := H) c).isSymmetric)

theorem zero_has_no_real_parameter :
    ¬ ∃ t : ℝ, 0 ≤ t ∧ (0 : ℝ) = 1 / 4 + t ^ 2 := by
  rintro ⟨t, _, ht⟩
  nlinarith only [ht, sq_nonneg t]

/-- One can preserve the bounded self-adjoint class while making an existing
eigenvalue zero. This is a perturbation theorem for an arbitrary fixed base. -/
theorem bounded_hamiltonian_constant_shift_refutes_real_parameter
    {K V : H →L[𝕜] H} (hK : IsSelfAdjoint K) (hV : IsSelfAdjoint V)
    {lambda : ℝ} {x : H}
    (hx : HasEigenvector ((K + V : H →L[𝕜] H) : Module.End 𝕜 H) (lambda : 𝕜) x) :
    ∃ W : H →L[𝕜] H, IsSelfAdjoint W ∧ IsSelfAdjoint (K + W) ∧
      HasEigenvector ((K + W : H →L[𝕜] H) : Module.End 𝕜 H) 0 x ∧
      ¬ ∃ t : ℝ, 0 ≤ t ∧ (0 : ℝ) = 1 / 4 + t ^ 2 := by
  let W := addConstantPotential V (-lambda)
  have hW : IsSelfAdjoint W := addConstantPotential_selfAdjoint hV _
  have hKW : IsSelfAdjoint (K + W) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (hK.isSymmetric.add hW.isSymmetric)
  refine ⟨W, hW, hKW, ?_, zero_has_no_real_parameter⟩
  have he := eigenvector_add_constant (T := K + V) hx (-lambda)
  change HasEigenvector ((K + W : H →L[𝕜] H) : Module.End 𝕜 H) 0 x
  simpa only [W, addConstantPotential, add_assoc, add_neg_cancel, RCLike.ofReal_zero] using he

/-- A bounded potential acts on the unchanged domain of a partial Hamiltonian. -/
def withPotential (K : H →ₗ.[𝕜] H) (V : H →L[𝕜] H) : H →ₗ.[𝕜] H :=
  V.toLinearMap +ᵥ K

@[simp] theorem withPotential_domain (K : H →ₗ.[𝕜] H) (V : H →L[𝕜] H) :
    (withPotential K V).domain = K.domain := rfl

theorem partial_eigenvector_add_constant
    {K : H →ₗ.[𝕜] H} {V : H →L[𝕜] H} {lambda : ℝ} {x : K.domain}
    (hx : withPotential K V x = (lambda : 𝕜) • (x : H)) (c : ℝ) :
    withPotential K (addConstantPotential V c) x = ((lambda + c : ℝ) : 𝕜) • (x : H) := by
  change V (x : H) + K x = (lambda : 𝕜) • (x : H) at hx
  change addConstantPotential V c (x : H) + K x = ((lambda + c : ℝ) : 𝕜) • (x : H)
  rw [addConstantPotential_apply, add_right_comm, hx, RCLike.ofReal_add, add_smul]

/-- On an unbounded operator domain the same nonzero vector is an exact
zero-eigenvector after shifting the bounded multiplication potential. -/
theorem partial_hamiltonian_constant_shift_refutes_real_parameter
    {K : H →ₗ.[𝕜] H} {V : H →L[𝕜] H} (hV : IsSelfAdjoint V)
    {lambda : ℝ} {x : K.domain} (hne : (x : H) ≠ 0)
    (hx : withPotential K V x = (lambda : 𝕜) • (x : H)) :
    ∃ W : H →L[𝕜] H, IsSelfAdjoint W ∧ (withPotential K W).domain = K.domain ∧
      (x : H) ≠ 0 ∧ withPotential K W x = 0 ∧
      ¬ ∃ t : ℝ, 0 ≤ t ∧ (0 : ℝ) = 1 / 4 + t ^ 2 := by
  refine ⟨addConstantPotential V (-lambda), addConstantPotential_selfAdjoint hV _,
    rfl, hne, ?_, zero_has_no_real_parameter⟩
  simpa only [add_neg_cancel, RCLike.ofReal_zero, zero_smul] using
    partial_eigenvector_add_constant hx (-lambda)

end Hilbert

section Lp

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {p : ℝ≥0∞} {μ : Measure X} [Fact (1 ≤ p)]

theorem constantMultiplier_ae (c : ℝ) (u : Lp F p μ) :
    ((constantMultiplier (𝕜 := 𝕜) c u : Lp F p μ) : X → F) =ᵐ[μ]
      fun y => (c : 𝕜) • u y := by
  filter_upwards [Lp.coeFn_smul (c : 𝕜) u] with y hy
  simpa only [constantMultiplier_apply, Pi.smul_apply] using hy

/-- On `Lp`, the shifted potential adds the same real scalar to the
pointwise multiplier at almost every point. -/
theorem addConstantPotential_represents
    (V : Lp F p μ →L[𝕜] Lp F p μ) (B : X → (F →L[𝕜] F))
    (c : ℝ) (u : Lp F p μ)
    (hV : ((V u : Lp F p μ) : X → F) =ᵐ[μ] fun y => B y (u y)) :
    ((addConstantPotential V c u : Lp F p μ) : X → F) =ᵐ[μ]
      fun y => addConstantPotential (B y) c (u y) := by
  have hadd :
      ((addConstantPotential V c u : Lp F p μ) : X → F) =ᵐ[μ]
        fun y => V u y + constantMultiplier (𝕜 := 𝕜) c u y := by
    filter_upwards [Lp.coeFn_add (V u) (constantMultiplier (𝕜 := 𝕜) c u)] with y hy
    simpa only [addConstantPotential_apply, constantMultiplier_apply, Pi.add_apply] using hy
  filter_upwards [hadd, hV, constantMultiplier_ae (𝕜 := 𝕜) c u] with y ha hb hc
  rw [ha, hb, hc, addConstantPotential_apply]

end Lp

end

end ManuscriptAudit.SpectralQuarterShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpectralQuarterShift.bounded_hamiltonian_constant_shift_refutes_real_parameter,
      ``ManuscriptAudit.SpectralQuarterShift.partial_hamiltonian_constant_shift_refutes_real_parameter,
      ``ManuscriptAudit.SpectralQuarterShift.addConstantPotential_represents] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
