import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspLaurentNativePowerKummer
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSchemeConstant
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeConstantNaturality

/-! The actual power pullback on Laurent H¹ has the required scalar action
on the constant cyclic coefficient group. -/

namespace ManuscriptAudit.CuspLaurentNativeConstantPower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspRelativePowerMap (overlapMap)
open CuspRelativePowerCoordinates (laurentPower)
open CuspLaurentNativePowerKummer (kernelCyclicEquiv kernelMap_scalar)
open ProetaleSchemeCohomologyPullback (constant)
open ProetaleSchemeConstantNaturality (constant_natural)
open ProetaleKummerSchemeConstant (constant_cohomology)
open ProetaleKummerPower (J G power)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev R := LaurentPolynomial K
private abbrev W := Spec (CommRingCat.of (R K))
private abbrev k : W K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (R K)))

/-- The actual Laurent power is a morphism over the algebraically closed coefficient field. -/
theorem overlap_overField (m : ℕ) : overlapMap K m ≫ k K = k K := by
  unfold overlapMap
  change Spec.map (CommRingCat.ofHom (laurentPower K m).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (R K))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (laurentPower K m).commutes a

variable (d : ℕ) [NeZero (d : K)]

local instance residueOrder : NeZero d := NeZero.of_neZero_natCast K

private abbrev C := constantSheaf (J (W K)) G
private abbrev M := coefficientGroup K d
private abbrev N := AddCommGrpCat.of (ULift.{1} (ZMod d))

set_option maxHeartbeats 6200000 in
/-- Pullback is multiplication by m on the actual constant roots group. -/
theorem roots_scalar (m : ℕ) (a : Sheaf.H ((C K).obj (M K d)) 1) :
    constant (overlapMap K m) (M K d) 1 a = m • a := by
  let f := overlapMap K m
  let e := cohomologyIso (constantKernelIso (k K) d) 1
  apply e.injective
  have h := constant_cohomology d f (k K) (k K) (overlap_overField K m) 1 a
  change ProetaleKummerSchemePullback.kernelMap f d 1 (e a) = e (constant f (M K d) 1 a) at h
  obtain ⟨z, hz⟩ := (kernelCyclicEquiv K d).surjective (e a)
  have hScalar : ProetaleKummerSchemePullback.kernelMap f d 1 (e a) = m • e a := by
    rw [← hz]
    exact kernelMap_scalar K d m z
  exact h.symm.trans (hScalar.trans (map_nsmul e a m).symm)

set_option maxHeartbeats 6200000 in
/-- Pullback is multiplication by m on the actual Laurent H¹ with ZMod d coefficients. -/
theorem cyclic_scalar (m : ℕ) (a : Sheaf.H ((C K).obj (N d)) 1) :
    constant (overlapMap K m) (N d) 1 a = m • a := by
  let root := (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let i : M K d ≅ N d := (AddEquiv.ulift.trans (root.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  let e := cohomologyIso ((C K).mapIso i) 1
  obtain ⟨b, rfl⟩ := e.surjective a
  have h := constant_natural (overlapMap K m) i.hom 1 b
  change constant (overlapMap K m) (N d) 1 (e b) =
    e (constant (overlapMap K m) (M K d) 1 b) at h
  exact h.trans ((congrArg e (roots_scalar K d m b)).trans (map_nsmul e b m))

end
end ManuscriptAudit.CuspLaurentNativeConstantPower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspLaurentNativeConstantPower.overlap_overField,
      ``ManuscriptAudit.CuspLaurentNativeConstantPower.roots_scalar,
      ``ManuscriptAudit.CuspLaurentNativeConstantPower.cyclic_scalar] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
