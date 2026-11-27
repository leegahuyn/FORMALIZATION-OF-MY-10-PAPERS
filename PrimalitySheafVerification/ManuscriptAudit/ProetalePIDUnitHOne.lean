import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineRechart
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitCech
import PrimalitySheafVerification.ManuscriptAudit.SheafExplicitCechHOne
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! The actual native pro-étale degree-one cohomology of units on a
PID spectrum vanishes by affine covering and faithfully flat descent. -/

namespace ManuscriptAudit.ProetalePIDUnitHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor ProetaleAffineRechart ProetaleTensorFaces
open ProetaleUnitCech (F)
open SingletonCoverRefinement (Covers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]

private abbrev J := Scheme.ProEt.topology (spectrum A)
private abbrev G := AddCommGrpCat.{1}
private abbrev C := Sheaf (J A) G

local instance : EnoughInjectives (C A) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C A)

variable (B : Type) [CommRing B] [Algebra A B] [WeaklyEtale (structureMap A B)]
  [Surjective (structureMap A B)]

/-- The actual weakly étale surjective arrow of affine spectra is a native covering singleton. -/
theorem specCover : Covers (J A) (toTerminal A B) := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.singleton (toTerminal A B)).map
    (Scheme.ProEt.forget (spectrum A) ⋙ Over.forget (spectrum A)) ∈
    Scheme.proetalePrecoverage (spectrum A)
  rw [Presieve.map_singleton]
  change Presieve.singleton (structureMap A B) ∈ Scheme.propQCPrecoverage @WeaklyEtale (spectrum A)
  exact Scheme.Hom.singleton_mem_propQCPrecoverage
    (inferInstanceAs (WeaklyEtale (structureMap A B)))

set_option maxHeartbeats 1600000 in
/-- Degree-one local cokernel lifts on a faithfully flat affine spectrum
extend to actual global lifts. -/
theorem lift_from_spec {I : C A} (i : F A ⟶ I) [Mono i]
    (x : (cokernel i).obj.obj (op (terminal A))) (y : I.obj.obj (op (object A B)))
    (hy : (cokernel.π i).hom.app (op (object A B)) y =
      (cokernel i).obj.map (toTerminal A B).op x) :
    ∃ z : I.obj.obj (op (terminal A)), (cokernel.π i).hom.app _ z = x := by
  let f := toTerminal A B
  let hP := double_isPullback A B
  letI : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).mp
      ⟨inferInstanceAs (Flat (structureMap A B)), inferInstanceAs (Surjective (structureMap A B))⟩)
  letI : Nontrivial B := by
    let p : PrimeSpectrum A := Classical.choice inferInstance
    obtain ⟨q, _⟩ := (inferInstanceAs (Surjective (structureMap A B))).surj p
    exact PrimeSpectrum.nontrivial q
  obtain ⟨b, hb, hbCocycle⟩ := SheafExplicitCechHOne.exists_cocycle i f (p₀ A B) (p₁ A B) hP
    (e₀₁ A B) (e₀₂ A B) (e₁₂ A B) (face_first_first A B) (face_second_first A B)
    (face_second_second A B) x y hy
  obtain ⟨a, ha⟩ := ProetaleUnitCech.exists_primitive A B b hbCocycle
  apply SheafExplicitCechHOne.exists_global_lift i f (p₀ A B) (p₁ A B) hP
    (specCover A B) x y hy a
  rw [← ha]
  exact hb

set_option maxHeartbeats 1600000 in
/-- The actual native pro-étale H¹ of multiplicative units on a PID
spectrum is zero. -/
theorem HOne_subsingleton : Subsingleton (Sheaf.H (F A) 1) := by
  let I := Injective.under (F A)
  let i : F A ⟶ I := Injective.ι (F A)
  let T := terminal A
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale (spectrum A)
  letI : IsAffine T.left := inferInstanceAs (IsAffine (spectrum A))
  apply SheafH1Descent.H1_subsingleton_of_global_lifts i hT
  let π := cokernel.π i
  letI : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' G π).mpr inferInstance
  intro x
  obtain ⟨W, f, ha, _, hs, _, y, hy⟩ :=
    ProetaleAffineSingletonLift.exists_singleton_cover_lift (T := T) π x
  letI := ha
  let B : Type := coordinateRing A W
  letI : CommRing B := inferInstanceAs (CommRing (coordinateRing A W))
  letI : Algebra A B := coordinateAlgebra A W
  letI : WeaklyEtale (structureMap A B) := coordinateChartWeaklyEtale A W
  letI : Surjective (structureMap A B) := coordinateChartSurjective A W hs
  let c := rechart A W
  let y' := I.obj.map c.op y
  apply lift_from_spec A B i x y'
  change π.hom.app _ (I.obj.map c.op y) = _
  rw [NatTrans.naturality_apply π.hom c.op y, hy, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, rechart_comp_toTerminal]

end
end ManuscriptAudit.ProetalePIDUnitHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetalePIDUnitHOne.specCover,
      ``ManuscriptAudit.ProetalePIDUnitHOne.lift_from_spec,
      ``ManuscriptAudit.ProetalePIDUnitHOne.HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
