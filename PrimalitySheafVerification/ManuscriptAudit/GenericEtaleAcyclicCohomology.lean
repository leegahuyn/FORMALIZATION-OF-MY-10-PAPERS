import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDirectImageHOneEmbedding
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleCohomologyAcyclic
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleAcyclicSections

/-! Positive cohomology of the actual generic-point direct image of an acyclic field sheaf. -/

namespace ManuscriptAudit.GenericEtaleAcyclicSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FieldEtaleCohomologyAcyclic FieldEtaleSkyscraperResolution SmallEtaleBaseChange

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (A F : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field F]
  [Algebra A F] [IsFractionRing A F]

private abbrev X := Spec (CommRingCat.of A)
private abbrev Y := Spec (CommRingCat.of F)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev D := directImage (j A F) AddCommGrpCat.{0}
private abbrev C := Sheaf (Y F).smallEtaleTopology AddCommGrpCat.{0}

/-- The native generic-point direct image of a sheaf with acyclic
finite Galois sections on all field charts has no positive cohomology. -/
theorem directImage_H_succ_subsingleton (M : C F)
    (hM : HasAcyclicGaloisSections F M) (n : ℕ) :
    Subsingleton (Sheaf.H ((D A F).obj M) (n + 1)) := by
  induction n generalizing M with
  | zero =>
    obtain ⟨g, hg⟩ := AffineEtaleDirectImageHOneEmbedding.HOne_embedding
      (CommRingCat.of A) (CommRingCat.of F) (j A F) M
    have h := FieldEtaleCohomologyAcyclic.H_succ_subsingleton F M hM 0
    exact ⟨fun x y ↦ hg (h.elim _ _)⟩
  | succ n ih =>
    let I := injectivePresentation F M
    let S := ShortComplex.cokernelSequence I.f
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact I.f)
      (inferInstanceAs (Mono I.f)) (inferInstanceAs (Epi (cokernel.π I.f)))
    let G := D A F
    let T := S.map G
    have hT : T.ShortExact :=
      directImage_shortExact A F S hS (fun L _ g _ ↦
        HasAcyclicGaloisSections.chartHOne F hM L g)
    letI : G.PreservesInjectiveObjects :=
      AffineEtaleMorphism.fullDirectImage_preservesInjectiveObjects
        (CommRingCat.of A) (CommRingCat.of F) (j A F)
    letI : Injective T.X₂ := inferInstanceAs (Injective (G.obj I.J))
    have hQ : HasAcyclicGaloisSections F S.X₃ :=
      quotient_hasAcyclicGaloisSections F M hM
    exact SheafCohomologyDimensionShift.H_succ_subsingleton_of_injectiveMiddle T hT (n + 1)
      (ih S.X₃ hQ)

end

end ManuscriptAudit.GenericEtaleAcyclicSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GenericEtaleAcyclicSections.directImage_H_succ_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
