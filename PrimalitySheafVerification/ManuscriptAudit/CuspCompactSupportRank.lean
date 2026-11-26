import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportEuler
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportExcess
import PrimalitySheafVerification.ManuscriptAudit.FiniteKernelRank

/-!
# Degree-one compact-support rank for the punctured cusp

The native map onto the compactly supported group of the affine cusp
has one cyclic coefficient group as its kernel. Finite dimensionality
on the affine cusp alone therefore gives the rank of the puncture.
-/

namespace ManuscriptAudit.CuspCompactSupportRank

open CategoryTheory
open CuspCompactSupportSequence CuspCompactSupportLowDegrees CuspCompactSupportExcess

universe u

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] CuspCompactSupportEuler.cuspModule CuspCompactSupportEuler.punctureModule

variable (K : Type u) [Field K] [IsSepClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev coeff : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} (ZMod ℓ))

private abbrev firstMap : punctureHc K (coeff ℓ) 1 →+ cuspHc K (coeff ℓ) 1 :=
  Sheaf.H.map (compactSupportSequence K (coeff ℓ)).f 1

private def firstLinearMap :
    punctureHc K (coeff ℓ) 1 →ₗ[ZMod ℓ] cuspHc K (coeff ℓ) 1 :=
  (firstMap K ℓ).toZModLinearMap ℓ

private def firstLinearKernelEquiv :
    (firstLinearMap K ℓ).ker ≃ₗ[ZMod ℓ] ZMod ℓ := by
  let r : (firstLinearMap K ℓ).ker ≃+ (firstMap K ℓ).ker :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := by intros; rfl }
  let ul : ULift.{u} (ZMod ℓ) ≃+ ZMod ℓ :=
    { toFun := ULift.down, invFun := ULift.up, left_inv := by intro x; rfl,
      right_inv := by intro x; rfl, map_add' := by intros; rfl }
  let e := r.trans ((firstKernelEquivOrigin K (coeff ℓ)).trans ul)
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective

/-- A single finite-dimensionality hypothesis suffices for the actual
degree-one compact-support rank difference of one. -/
theorem firstRankOfFiniteCusp [FiniteDimensional (ZMod ℓ) (cuspHc K (coeff ℓ) 1)] :
    FiniteDimensional (ZMod ℓ) (punctureHc K (coeff ℓ) 1) ∧
      Module.finrank (ZMod ℓ) (punctureHc K (coeff ℓ) 1) =
        Module.finrank (ZMod ℓ) (cuspHc K (coeff ℓ) 1) + 1 := by
  let f := firstLinearMap K ℓ
  let e := firstLinearKernelEquiv K ℓ
  letI : FiniteDimensional (ZMod ℓ) f.ker := e.symm.finiteDimensional
  have hs : Function.Surjective f := (compactSupportFiveTerm K (coeff ℓ)).2.2.2.2
  have h := FiniteKernelRank.finiteDimensional_and_finrank f hs
  have hr : Module.finrank (ZMod ℓ) f.ker = 1 := e.finrank_eq.trans (Module.finrank_self _)
  exact ⟨h.1, by rw [h.2, hr, Nat.add_comm]⟩

end

end ManuscriptAudit.CuspCompactSupportRank

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspCompactSupportRank.firstRankOfFiniteCusp
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
