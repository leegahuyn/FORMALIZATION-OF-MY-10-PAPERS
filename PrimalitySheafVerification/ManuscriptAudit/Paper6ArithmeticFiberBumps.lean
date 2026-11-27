import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCuspSmoothLocus
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticCuspBinary
import PrimalitySheafVerification.ManuscriptAudit.NodalArithmeticBump

/-! Exact ordinary arithmetic binary bumps for the actual smooth opens of the two curves. -/

namespace ManuscriptAudit.Paper6ArithmeticFiberBumps

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNodeToBase)
open NodalArithmeticProjectiveHOne (properHOne)

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [Finite K]

private abbrev R := ZMod 2
private abbrev C := AddCommGrpCat.of R
private abbrev X := AffineCuspSmoothLocus.cusp K
private abbrev V := (AffineCuspSmoothLocus.cuspToBase K).smoothLocus.toScheme
private abbrev J (S : Scheme.{0}) := S.smallEtaleTopology
private abbrev cuspHOne := Sheaf.H (BinaryConstantCohomology.constantBinary (J (X K))) 1
private abbrev cuspSmoothHOne := Sheaf.H (BinaryConstantCohomology.constantBinary (J (V K))) 1

def cuspModule : Module R (cuspHOne K) :=
  BinaryConstantCohomology.coefficientModule (J (X K)) 1

def cuspSmoothModule : Module R (cuspSmoothHOne K) :=
  BinaryConstantCohomology.coefficientModule (J (V K)) 1

def cuspSmoothHOneEquiv (h₂ : (2 : K) ≠ 0) :
    (R × R) ≃+ cuspSmoothHOne K :=
  (ArithmeticCuspBinary.punctureHOneEquiv K h₂).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (AffineCuspSmoothLocus.smoothLocusIso K).symm C 1)

theorem cusp_finranks (p : ℕ) [Fact p.Prime] [CharP K p] (h₂ : (2 : K) ≠ 0) :
    letI := cuspModule K
    letI := cuspSmoothModule K
    Module.finrank R (cuspHOne K) = 1 ∧ Module.finrank R (cuspSmoothHOne K) = 2 := by
  letI := cuspModule K
  letI := cuspSmoothModule K
  let e := ArithmeticCuspBinary.cuspHOneEquiv K p h₂
  let g := cuspSmoothHOneEquiv K h₂
  let eLinear : R ≃ₗ[R] cuspHOne K := { e with map_smul' := ZMod.map_smul e }
  let gLinear : (R × R) ≃ₗ[R] cuspSmoothHOne K := { g with map_smul' := ZMod.map_smul g }
  refine ⟨eLinear.finrank_eq.symm.trans (CommSemiring.finrank_self _), ?_⟩
  rw [← gLinear.finrank_eq, Module.finrank_prod, CommSemiring.finrank_self] <;> norm_num

theorem cusp_signed_bump (p : ℕ) [Fact p.Prime] [CharP K p] (h₂ : (2 : K) ≠ 0) :
    letI := cuspModule K
    letI := cuspSmoothModule K
    (Module.finrank R (cuspHOne K) : ℤ) - Module.finrank R (cuspSmoothHOne K) = -1 := by
  letI := cuspModule K
  letI := cuspSmoothModule K
  obtain ⟨hC, hV⟩ := cusp_finranks K p h₂
  rw [hC, hV] <;> norm_num

def nodeSmoothHOneEquiv (h₂ : (2 : K) ≠ 0) :
    (R × R) ≃+ NodalArithmeticBump.smoothHOne K :=
  (ArithmeticLaurentBinary.laurentBinaryHOneEquiv K h₂).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (NodalSmoothLocusGm.smoothLocusIsoGm K h₂).symm C 1)

theorem node_finranks (h₂ : (2 : K) ≠ 0) :
    letI := NodalArithmeticBump.properModule K
    letI := NodalArithmeticBump.smoothModule K
    Module.finrank R (properHOne K) = 2 ∧
      Module.finrank R (NodalArithmeticBump.smoothHOne K) = 2 := by
  obtain ⟨u, hu⟩ := FiniteFieldSquareClasses.exists_nonsquare_unit K h₂
  exact NodalArithmeticBump.finranks_eq_two K h₂
    (ArithmeticKummerSquareClasses.affineLineBinaryHOneEquiv K h₂) (nodeSmoothHOneEquiv K h₂) u hu

theorem node_zero_bump_and_nonsmooth (h₂ : (2 : K) ≠ 0) :
    letI := NodalArithmeticBump.properModule K
    letI := NodalArithmeticBump.smoothModule K
    ((Module.finrank R (properHOne K) : ℤ) -
      Module.finrank R (NodalArithmeticBump.smoothHOne K) = 0) ∧
      ¬ AlgebraicGeometry.Smooth (projectiveNodeToBase K) := by
  letI := NodalArithmeticBump.properModule K
  letI := NodalArithmeticBump.smoothModule K
  obtain ⟨hp, hs⟩ := node_finranks K h₂
  exact ⟨by rw [hp, hs, sub_self], NodalSmoothCharts.projectiveNode_not_smooth K⟩

end
end ManuscriptAudit.Paper6ArithmeticFiberBumps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper6ArithmeticFiberBumps.cuspSmoothHOneEquiv,
      ``ManuscriptAudit.Paper6ArithmeticFiberBumps.cusp_finranks,
      ``ManuscriptAudit.Paper6ArithmeticFiberBumps.cusp_signed_bump,
      ``ManuscriptAudit.Paper6ArithmeticFiberBumps.nodeSmoothHOneEquiv,
      ``ManuscriptAudit.Paper6ArithmeticFiberBumps.node_finranks,
      ``ManuscriptAudit.Paper6ArithmeticFiberBumps.node_zero_bump_and_nonsmooth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
