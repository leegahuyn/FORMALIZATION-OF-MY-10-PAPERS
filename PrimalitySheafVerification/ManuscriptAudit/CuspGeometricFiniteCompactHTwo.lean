import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Finite
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeFiniteCompactHTwo

/-! Compactly supported degree-two finite cohomology of the cusp and its
puncture over the geometric residue field of any prime different from the
coefficient prime. Both actual native groups have dimension one. -/

namespace ManuscriptAudit.CuspGeometricFiniteCompactHTwo

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (affineCusp affineOpen)
open CuspNativeCompactSmoothHOne (smoothOpen)
open SmallEtaleGeometricBaseChange (cuspPuncturedOpen)
open OpenProetaleExtension (extensionByZero)
open ProetaleConstantRestriction (constant)

noncomputable section

variable (p l : ℕ) [Fact p.Prime] [Fact l.Prime]

private abbrev K := AlgebraicClosure (ZMod p)
private abbrev A := AddCommGrpCat.{1}

private theorem residue_nonzero (h : l ≠ p) : NeZero (l : K p) :=
  ⟨fun hz ↦ h ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : l.Prime)).mp
    ((CharP.cast_eq_zero_iff (K p) p l).mp hz)).symm⟩

abbrev affineGroup := Sheaf.H ((extensionByZero (affineOpen (K p)) A).obj
  (constant (affineCusp (K p)) (ZMod l))) 2

abbrev smoothGroup := Sheaf.H ((extensionByZero (smoothOpen (K p)) A).obj
  (constant (cuspPuncturedOpen (K p)).toScheme (ZMod l))) 2

/-- Finite geometric compact cohomology of the actual affine cusp. -/
def affineEquiv (h : l ≠ p) : ZMod l ≃+ affineGroup p l := by
  letI := residue_nonzero p l h
  exact CuspNativeFiniteCompactHTwo.affinePrimeCompactEquiv (K p) p l

/-- Finite geometric compact cohomology of the actual punctured cusp. -/
def smoothEquiv (h : l ≠ p) : ZMod l ≃+ smoothGroup p l := by
  letI := residue_nonzero p l h
  exact CuspNativeFiniteCompactHTwo.smoothPrimeCompactEquiv (K p) p l

private def coefficientModule {M : Type 1} [AddCommGroup M] (e : ZMod l ≃+ M) :
    Module (ZMod l) M :=
  AddCommGroup.zmodModule fun x ↦ by
    obtain ⟨a, rfl⟩ := e.surjective x
    have ha : l • a = 0 := by simp [nsmul_eq_mul]
    rw [← map_nsmul, ha, map_zero]

private theorem finrank_eq_one {M : Type 1} [AddCommGroup M] (e : ZMod l ≃+ M) :
    letI := coefficientModule l e
    Module.finrank (ZMod l) M = 1 := by
  letI := coefficientModule l e
  let e' : ZMod l ≃ₗ[ZMod l] M := { e with map_smul' := ZMod.map_smul e }
  exact e'.finrank_eq.symm.trans (CommSemiring.finrank_self _)

/-- Both compact-support groups have dimension one at prime coefficients. -/
theorem finranks (h : l ≠ p) :
    letI := coefficientModule l (affineEquiv p l h)
    letI := coefficientModule l (smoothEquiv p l h)
    Module.finrank (ZMod l) (affineGroup p l) = 1 ∧
      Module.finrank (ZMod l) (smoothGroup p l) = 1 :=
  ⟨finrank_eq_one l (affineEquiv p l h), finrank_eq_one l (smoothEquiv p l h)⟩

end
end ManuscriptAudit.CuspGeometricFiniteCompactHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspGeometricFiniteCompactHTwo.affineEquiv,
      ``ManuscriptAudit.CuspGeometricFiniteCompactHTwo.smoothEquiv,
      ``ManuscriptAudit.CuspGeometricFiniteCompactHTwo.finranks] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
