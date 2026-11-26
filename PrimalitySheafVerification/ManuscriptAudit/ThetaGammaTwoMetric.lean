import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import PrimalitySheafVerification.ManuscriptAudit.ThetaProfileGenerators

/-! The actual weighted Jacobi theta density descends to the level-two quotient. -/

namespace ManuscriptAudit.ThetaGammaTwoMetric

open CompactModularCore LiteralCuspTruncation ThetaProfileGenerators Paper9ThetaCuspPhases
open Matrix ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

abbrev Direction := Fin 2 → ZMod 2

def direction (g : SL(2, ℤ)) (v : Direction) : Direction :=
  ((reduceTwo g : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec v

theorem direction_one (v : Direction) : direction 1 v = v := by
  simp [direction]

theorem direction_mul (g h : SL(2, ℤ)) (v : Direction) :
    direction (g * h) v = direction g (direction h v) := by
  simp [direction, Matrix.mulVec_mulVec]

/-- The three nonzero labels encode the standard, alternating and half-shifted theta functions. -/
def profile (v : Direction) : ℂ → ℂ :=
  if v = ![1, 1] then jacobiTheta
  else if v = ![0, 1] then thetaAlternating
  else if v = ![1, 0] then thetaHalfShift
  else 0

def profileDensity (v : Direction) (z : ℍ) : ℝ := thetaDensity (profile v) z

theorem direction_cases (v : Direction) :
    v = ![0, 0] ∨ v = ![1, 1] ∨ v = ![0, 1] ∨ v = ![1, 0] := by
  let h := ThreeCuspNeighborhoods.zmod_two_cases
  rcases h (v 0) with h0 | h0 <;> rcases h (v 1) with h1 | h1
  · exact Or.inl (funext fun i => by fin_cases i <;> simpa [h0, h1])
  · exact Or.inr (Or.inr (Or.inl (funext fun i => by fin_cases i <;> simpa [h0, h1])))
  · exact Or.inr (Or.inr (Or.inr (funext fun i => by fin_cases i <;> simpa [h0, h1])))
  · exact Or.inr (Or.inl (funext fun i => by fin_cases i <;> simpa [h0, h1]))

theorem profile_00 : profile (![0, 0] : Direction) = 0 := by
  have h11 : (![0, 0] : Direction) ≠ ![1, 1] := by decide
  have h01 : (![0, 0] : Direction) ≠ ![0, 1] := by decide
  have h10 : (![0, 0] : Direction) ≠ ![1, 0] := by decide
  simp only [profile, h11, h01, h10, if_false, if_true]

theorem profile_11 : profile (![1, 1] : Direction) = jacobiTheta := by
  rw [profile, if_pos rfl]

theorem profile_01 : profile (![0, 1] : Direction) = thetaAlternating := by
  have h11 : (![0, 1] : Direction) ≠ ![1, 1] := by decide
  rw [profile, if_neg h11, if_pos rfl]

theorem profile_10 : profile (![1, 0] : Direction) = thetaHalfShift := by
  have h11 : (![1, 0] : Direction) ≠ ![1, 1] := by decide
  have h01 : (![1, 0] : Direction) ≠ ![0, 1] := by decide
  rw [profile, if_neg h11, if_neg h01, if_pos rfl]

private theorem density_S (v : Direction) (z : ℍ) :
    profileDensity v (S • z) = profileDensity (direction S⁻¹ v) z := by
  rcases direction_cases v with rfl | rfl | rfl | rfl
  · have h : direction S⁻¹ (![0, 0] : Direction) = ![0, 0] := by decide
    rw [h]
    simp [profileDensity, profile_00, thetaDensity]
  · have h : direction S⁻¹ (![1, 1] : Direction) = ![1, 1] := by decide
    rw [h]
    simpa only [profileDensity, profile_11, profile_11] using thetaDensity_S_standard z
  · have h : direction S⁻¹ (![0, 1] : Direction) = ![1, 0] := by decide
    rw [h]
    simpa only [profileDensity, profile_01, profile_10] using thetaDensity_S_alternating z
  · have h : direction S⁻¹ (![1, 0] : Direction) = ![0, 1] := by decide
    rw [h]
    simpa only [profileDensity, profile_10, profile_01] using thetaDensity_S_half z

private theorem density_T (v : Direction) (z : ℍ) :
    profileDensity v (T • z) = profileDensity (direction T⁻¹ v) z := by
  rcases direction_cases v with rfl | rfl | rfl | rfl
  · have h : direction T⁻¹ (![0, 0] : Direction) = ![0, 0] := by decide
    rw [h]
    simp [profileDensity, profile_00, thetaDensity]
  · have h : direction T⁻¹ (![1, 1] : Direction) = ![0, 1] := by decide
    rw [h]
    simpa only [profileDensity, profile_11, profile_01] using thetaDensity_T_standard z
  · have h : direction T⁻¹ (![0, 1] : Direction) = ![1, 1] := by decide
    rw [h]
    simpa only [profileDensity, profile_01, profile_11] using thetaDensity_T_alternating z
  · have h : direction T⁻¹ (![1, 0] : Direction) = ![1, 0] := by decide
    rw [h]
    simpa only [profileDensity, profile_10, profile_10] using thetaDensity_T_half z

theorem full_modular_density_covariance (g : SL(2, ℤ)) :
    ∀ (v : Direction) (z : ℍ), profileDensity v (g • z) = profileDensity (direction g⁻¹ v) z := by
  have hg : g ∈ Subgroup.closure {S, T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hg using Subgroup.closure_induction with
  | mem γ hγ =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl
    · exact density_S
    · exact density_T
  | one => intro v z; simp [direction_one]
  | mul g h _ _ ig ih =>
    intro v z
    rw [mul_smul, ig, ih, _root_.mul_inv_rev g h, direction_mul]
  | inv g _ ig =>
    intro v z
    have he := ig (direction g v) (g⁻¹ • z)
    rw [smul_inv_smul, ← direction_mul, inv_mul_cancel, direction_one] at he
    simpa only [inv_inv] using he.symm

theorem thetaDensity_invariant (g : SL(2, ℤ)) (hg : g ∈ GammaTwo) (z : ℍ) :
    thetaDensity jacobiTheta (g • z) = thetaDensity jacobiTheta z := by
  have hΓ := (mem_gamma_iff_reduced_one g).mp hg
  have hd : direction g⁻¹ (![1, 1] : Direction) = ![1, 1] := by
    rw [direction, map_inv, hΓ, inv_one]
    simp
  have he := full_modular_density_covariance g (![1, 1] : Direction) z
  rw [hd] at he
  simpa only [profileDensity, profile_11] using he

/-- The actual nonnegative squared norm density on the level-two orbit quotient. -/
def quotientThetaDensity : OrbitQuotient → ℝ :=
  Quotient.lift (thetaDensity jacobiTheta) (by
    rintro z w ⟨g, rfl⟩
    exact thetaDensity_invariant g.val g.property w)

theorem quotientThetaDensity_apply (z : ℍ) :
    quotientThetaDensity (orbitPoint z) = thetaDensity jacobiTheta z := rfl

end
end ManuscriptAudit.ThetaGammaTwoMetric

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaGammaTwoMetric.full_modular_density_covariance,
      ``ManuscriptAudit.ThetaGammaTwoMetric.thetaDensity_invariant,
      ``ManuscriptAudit.ThetaGammaTwoMetric.quotientThetaDensity_apply] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
