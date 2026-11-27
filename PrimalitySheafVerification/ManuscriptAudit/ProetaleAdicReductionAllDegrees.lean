import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant
import PrimalitySheafVerification.ManuscriptAudit.CompatibleTowerCongruence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction

/-! Actual integral native pro-étale classes have coherent finite reductions
in every degree. The finite constants and actual residue sheaves agree as towers. -/

namespace ManuscriptAudit.ProetaleAdicReductionAllDegrees

open AlgebraicGeometry CategoryTheory
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueReduction residueTransition residueReduction_comp)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleDiscreteConstant (nativeResidueIso nativeResidueIso_naturality)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)
open CyclicPowerInverseLimit (compatibleTuples)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

abbrev nativeStep (d n : ℕ) :=
  Sheaf.H.map ((lift X).map (residueTransition X ℓ n)) d

abbrev nativeCompatible (d : ℕ) :=
  compatibleTuples (fun n ↦ Sheaf.H (finiteCoefficient X ℓ n) d) (nativeStep X ℓ d)

/-- The actual native integral-to-residue comparison in each cohomological degree. -/
def reductionMap (d : ℕ) : X.EllAdicCohomology ℓ d →+ nativeCompatible X ℓ d where
  toFun x := ⟨fun n ↦ Sheaf.H.map ((lift X).map (residueReduction X ℓ n)) d x, fun n ↦ by
    change Sheaf.H.map ((lift X).map (residueTransition X ℓ n)) d
      (Sheaf.H.map ((lift X).map (residueReduction X ℓ (n + 1))) d x) =
        Sheaf.H.map ((lift X).map (residueReduction X ℓ n)) d x
    rw [← Sheaf.H.map_comp_apply, ← (lift X).map_comp, residueReduction_comp]⟩
  map_zero' := Subtype.ext (funext fun n ↦ map_zero (Sheaf.H.map ((lift X).map (residueReduction X ℓ n)) d))
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (Sheaf.H.map ((lift X).map (residueReduction X ℓ n)) d) x y)

private abbrev q (n : ℕ) :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).map
    (AddCommGrpCat.uliftFunctor.{1}.map
      (AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom))

private abbrev z (n : ℕ) := constant X (ZMod (ℓ ^ n))

abbrev constantStep (d n : ℕ) := Sheaf.H.map (q X ℓ n) d

abbrev constantCompatible (d : ℕ) :=
  compatibleTuples (fun n ↦ Sheaf.H (z X ℓ n) d) (constantStep X ℓ d)

private abbrev e (d n : ℕ) := cohomologyIso (X := X) (nativeResidueIso X ℓ n) d

set_option maxHeartbeats 1400000 in
theorem level_naturality (d n : ℕ) (x : Sheaf.H (z X ℓ (n + 1)) d) :
    e X ℓ d n (constantStep X ℓ d n x) = nativeStep X ℓ d n (e X ℓ d (n + 1) x) := by
  let a := (nativeResidueIso X ℓ n).hom
  let b := (nativeResidueIso X ℓ (n + 1)).hom
  let f := q X ℓ n
  let g := (lift X).map (residueTransition X ℓ n)
  calc
    _ = Sheaf.H.map (f ≫ a) d x := (Sheaf.H.map_comp_apply f a x).symm
    _ = Sheaf.H.map (b ≫ g) d x := congrArg (fun t ↦ Sheaf.H.map t d x)
      (nativeResidueIso_naturality X ℓ n)
    _ = _ := Sheaf.H.map_comp_apply b g x

set_option maxHeartbeats 1400000 in
/-- Constants and the actual native residue sheaves give the same ordinary limit. -/
def compatibleEquiv (d : ℕ) : constantCompatible X ℓ d ≃+ nativeCompatible X ℓ d :=
  CompatibleTowerCongruence.compatibleEquiv (fun n ↦ Sheaf.H (z X ℓ n) d)
    (fun n ↦ Sheaf.H (finiteCoefficient X ℓ n) d)
    (constantStep X ℓ d) (nativeStep X ℓ d) (e X ℓ d) (level_naturality X ℓ d)

end
end ManuscriptAudit.ProetaleAdicReductionAllDegrees

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicReductionAllDegrees.reductionMap,
      ``ManuscriptAudit.ProetaleAdicReductionAllDegrees.level_naturality,
      ``ManuscriptAudit.ProetaleAdicReductionAllDegrees.compatibleEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
