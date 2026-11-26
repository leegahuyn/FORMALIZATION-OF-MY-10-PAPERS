import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationFiber
import PrimalitySheafVerification.ManuscriptAudit.NodalAwayNormalization

/-! The actual affine nodal normalization is an isomorphism away from the
rational conductor, with a Cartesian square of the two principal opens. -/

namespace ManuscriptAudit.NodalNormalizationPuncture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalConductor (coordinates x)
open NodalAwayNormalization (nodeX normalizationEquiv)
open NodalNormalizationFiber (A B affineNode affineLine affineNormalization)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

abbrev nodeRing := Localization.Away (nodeX K)
abbrev lineRing := Localization.Away (x K)

abbrev nodePuncture := Spec (CommRingCat.of (nodeRing K))
abbrev linePuncture := Spec (CommRingCat.of (lineRing K))

def nodePunctureMap : nodePuncture K ⟶ affineNode K :=
  Spec.map (CommRingCat.ofHom (algebraMap (A K) (nodeRing K)))

def linePunctureMap : linePuncture K ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom (algebraMap (B K) (lineRing K)))

instance nodePunctureMap_open : IsOpenImmersion (nodePunctureMap K) :=
  IsOpenImmersion.of_isLocalization (S := nodeRing K) (nodeX K)

instance linePunctureMap_open : IsOpenImmersion (linePunctureMap K) :=
  IsOpenImmersion.of_isLocalization (S := lineRing K) (x K)

def linePunctureIsoNode : linePuncture K ≅ nodePuncture K :=
  Scheme.Spec.mapIso (normalizationEquiv K).toRingEquiv.toCommRingCatIso.op

private theorem normalization_on_scalar (a : A K) :
    normalizationEquiv K (algebraMap (A K) (nodeRing K) a) =
      algebraMap (B K) (lineRing K) a.val := by
  change (Localization.awayMapₐ (coordinates K).val (nodeX K))
    (algebraMap (A K) (nodeRing K) a) = _
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq] <;> rfl

theorem puncture_square :
    (linePunctureIsoNode K).hom ≫ nodePunctureMap K =
      linePunctureMap K ≫ affineNormalization K := by
  change Spec.map (CommRingCat.ofHom (normalizationEquiv K).toRingEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (A K) (nodeRing K))) =
    Spec.map (CommRingCat.ofHom (algebraMap (B K) (lineRing K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (A K) (B K)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact normalization_on_scalar K

private theorem nodePuncture_range :
    (nodePunctureMap K).opensRange = PrimeSpectrum.basicOpen (nodeX K) := by
  apply SetLike.coe_injective
  exact PrimeSpectrum.localization_away_comap_range (nodeRing K) (nodeX K)

private theorem linePuncture_range :
    (linePunctureMap K).opensRange = PrimeSpectrum.basicOpen (x K) := by
  apply SetLike.coe_injective
  exact PrimeSpectrum.localization_away_comap_range (lineRing K) (x K)

private theorem pullback_puncture_range :
    (pullback.snd (nodePunctureMap K) (affineNormalization K)).opensRange =
      PrimeSpectrum.basicOpen (x K) := by
  rw [Scheme.Hom.opensRange_pullbackSnd, nodePuncture_range, affineNormalization,
    SpecMap_preimage_basicOpen]
  rfl

private def comparison :
    linePuncture K ≅ pullback (nodePunctureMap K) (affineNormalization K) :=
  IsOpenImmersion.isoOfRangeEq (linePunctureMap K)
    (pullback.snd (nodePunctureMap K) (affineNormalization K))
    (congrArg (fun W : (affineLine K).Opens => (W : Set (affineLine K)))
      ((linePuncture_range K).trans (pullback_puncture_range K).symm))

private theorem comparison_snd :
    (comparison K).hom ≫ pullback.snd (nodePunctureMap K) (affineNormalization K) =
      linePunctureMap K :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem comparison_fst :
    (comparison K).hom ≫ pullback.fst (nodePunctureMap K) (affineNormalization K) =
      (linePunctureIsoNode K).hom := by
  apply (cancel_mono (nodePunctureMap K)).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, comparison_snd, puncture_square]

/-- The displayed principal-open square of actual nodal normalization is Cartesian. -/
theorem normalization_puncture_isPullback :
    IsPullback (linePunctureIsoNode K).hom (linePunctureMap K) (nodePunctureMap K)
      (affineNormalization K) :=
  IsPullback.of_iso_pullback ⟨puncture_square K⟩ (comparison K)
    (comparison_fst K) (comparison_snd K)

end
end ManuscriptAudit.NodalNormalizationPuncture

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNormalizationPuncture.normalization_puncture_isPullback
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
