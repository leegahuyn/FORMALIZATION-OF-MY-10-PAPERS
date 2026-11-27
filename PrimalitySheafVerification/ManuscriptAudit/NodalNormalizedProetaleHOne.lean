import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedProetalePic
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerTorsionFree

/-! Native cyclic and integral adic H¹ vanish on the actual normalization
of the proper split nodal curve in the invertible coefficient regime. -/

namespace ManuscriptAudit.NodalNormalizedProetaleHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalProjectiveClosure (projectiveNodeToBase)
open NodalNormalizedProetalePic
open ProetaleOpenLocalLifts (identityObject)
open ProetaleKummerTorsionFree (roots_HOne_subsingleton)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleAdicHOneDetection (finiteCoefficient reductionMap_injective)
open ProetaleDiscreteConstant (nativeResidueIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)

private abbrev X := normalizedNode K
private abbrev J := Scheme.ProEt.topology (X K)
private abbrev G := AddCommGrpCat.{1}

/-- The actual normalized proper model has vanishing degree-one native
cohomology for every positive cyclic order invertible in the field. -/
theorem cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (J K) G).obj
      (AddCommGrpCat.of (ULift.{1} (ZMod d)))) 1) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let hT : IsTerminal (identityObject (X K)) :=
    MorphismProperty.Over.mkIdTerminal @WeaklyEtale (X K)
  let e := Sheaf.H.equiv₀ (NodalNormalizedUnitOrder.F K) hT
  have hp : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h₀ : Function.Surjective (fun a : Sheaf.H (NodalNormalizedUnitOrder.F K) 0 ↦ d • a) := by
    intro a
    obtain ⟨b, hb⟩ := globalUnits_nsmul_surjective K h2 d hp (e a)
    refine ⟨e.symm b, e.injective ?_⟩
    rw [map_nsmul, AddEquiv.apply_symm_apply]
    exact hb
  let k := normalizationMap K ≫ projectiveNodeToBase K
  have h := roots_HOne_subsingleton (X K) k d h₀
    (units_HOne_eq_zero_of_nsmul_eq_zero K h2 d hp)
  let t : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let s : ULift.{1} (Additive (rootsOfUnity d K)) ≃+ ULift.{1} (ZMod d) :=
    AddEquiv.ulift.trans (t.trans AddEquiv.ulift.symm)
  let i := ((Sheaf.functorH (J K) 1).mapIso
    ((constantSheaf (J K) G).mapIso s.toAddCommGrpIso)).addCommGroupIsoToAddEquiv
  exact ⟨fun a b ↦ i.symm.injective (h.elim _ _)⟩

variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

theorem residue_HOne_subsingleton (n : ℕ) : Subsingleton (Sheaf.H (finiteCoefficient (X K) ℓ n) 1) := by
  letI : NeZero ((ℓ ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩
  let e := ((Sheaf.functorH (J K) 1).mapIso
    (nativeResidueIso (X K) ℓ n)).addCommGroupIsoToAddEquiv
  have h := cyclic_HOne_subsingleton K h2 (ℓ ^ n)
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

/-- Actual native integral adic H¹ vanishes on the normalized proper model. -/
theorem adic_HOne_subsingleton : Subsingleton ((X K).EllAdicCohomology ℓ 1) := by
  constructor
  intro a b
  apply reductionMap_injective (X K) ℓ
  apply Subtype.ext
  funext n
  exact (residue_HOne_subsingleton K h2 ℓ n).elim _ _

end
end ManuscriptAudit.NodalNormalizedProetaleHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedProetaleHOne.cyclic_HOne_subsingleton,
      ``ManuscriptAudit.NodalNormalizedProetaleHOne.residue_HOne_subsingleton,
      ``ManuscriptAudit.NodalNormalizedProetaleHOne.adic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
