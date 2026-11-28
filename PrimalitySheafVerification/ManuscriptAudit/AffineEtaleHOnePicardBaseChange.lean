import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDerivedRestriction
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOneToPicard
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleBaseChangePicard

/-! The actual Picard map sends each degree-one affine étale unit class
to the scalar extension of the descended line after restriction. -/

namespace ManuscriptAudit.AffineEtaleHOnePicardBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TensorProduct
open KummerUnitsSheaf SheafH1Descent FlatTwistedBaseChangeLine
open AffineEtaleOpenRestriction AffineEtaleRestrictedResolution
open AffineEtaleFaithfullyFlatRepresentatives AffineEtaleHOneToPicard AffineEtalePicardClass
open AffineEtaleRestrictRepresentative AffineEtaleDerivedRestriction
open FaithfullyFlatCocycleBaseChangePicard FaithfullyFlatCocyclePicard

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S] [Module.Flat A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev J (R : Type) [CommRing R] := Scheme.AffineEtale.topology (X R)
private abbrev C (R : Type) [CommRing R] := Sheaf (J R) AddCommGrpCat.{0}
private abbrev G (R : Type) [CommRing R] := coordinateUnitSheaf (X R)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (j A S)]

variable {I : C A} (i : G A ⟶ I) [Mono i] [Injective I]

local instance : Injective ((affineRestriction (j A S)).obj I) :=
  restrictedTarget_injective (j A S)

private abbrev rI := restrictedInjection (j A S) i

/-- Native affine H¹ restriction agrees literally with `Pic.mapAlgebra` on
the invertible modules constructed from the original and restricted injective embeddings. -/
theorem toPicard_restrict (h : Sheaf.H (G A) 1) :
    toPicard S (rI A S i) (restrictHOne A S h) =
      CommRing.Pic.mapAlgebra A S (toPicard A i h) := by
  obtain ⟨x, hx, ⟨c⟩⟩ := exists_faithfullyFlatAffineRepresentative A i h
  let B := c.coverRing
  letI : CommRing B := c.commRing
  letI : Algebra A B := c.algebra
  letI : Algebra.Etale A B := c.etale
  letI : Module.FaithfullyFlat A B := c.faithfullyFlat
  let y := c.value
  let hy := c.lifts
  let x' := restrictGlobal A S i x
  let y' := restrictLift A B S y
  let hy' := restrictLift_spec A B S i x y hy
  let c' : FaithfullyFlatAffineLift S (rI A S i) x' :=
    { coverRing := Cover A B S, commRing := inferInstance, algebra := inferInstance,
      etale := inferInstance, faithfullyFlat := inferInstance, value := y', lifts := hy' }
  have hh : connectingSection (rI A S i)
      (KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of S)) x' =
      restrictHOne A S h := (restrictHOne_connecting A S i x).symm.trans (congrArg _ hx)
  rw [toPicard_of_representative A i _ c hx, toPicard_of_representative S (rI A S i) _ c' hh]
  change picardClassOfLift S (Cover A B S) (rI A S i) x' y' hy' =
    CommRing.Pic.mapAlgebra A S (picardClassOfLift A B i x y hy)
  symm
  unfold picardClassOfLift
  apply picardClass_baseChange_of_eq A B S
  exact restrictLift_transition A B S i x y hy

end

end ManuscriptAudit.AffineEtaleHOnePicardBaseChange

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleHOnePicardBaseChange.toPicard_restrict
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
