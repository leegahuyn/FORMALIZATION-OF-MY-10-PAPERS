import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.RingTheory.Smooth.Flat
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitComparison

/-!
# The generic-point unit map is a monomorphism

An étale algebra is flat over its base. For a domain this makes the
coordinate-ring map into the tensor-product generic fiber injective,
including on disconnected affine étale objects. Affine restriction then
detects the monomorphism of sheaves on the full small étale site.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The actual map of units on any affine étale algebra chart is a
monomorphism, also when its coordinate ring has zero divisors. -/
theorem genericPointUnitsHom_onAlgebra_mono (A B F : Type) [CommRing A] [IsDomain A]
    [CommRing B] [Field F] [Algebra A B] [Algebra A F] [IsFractionRing A F]
    [Algebra.Etale A B] :
    Mono ((genericPointUnitsHom A F).hom.app (op (algebraEtaleObject A B))) := by
  let t : B →ₐ[A] F ⊗[A] B := Algebra.TensorProduct.includeRight
  have ht : Function.Injective t :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective A F)
  let i := ringUnits.map (CommRingCat.ofHom t.toRingHom)
  letI : Mono i := (AddCommGrpCat.mono_iff_injective i).mpr (by
    intro x y h
    apply Additive.ext
    apply Units.ext
    apply ht
    exact congrArg (fun u : Additive (F ⊗[A] B)ˣ => (u.toMul : F ⊗[A] B)) h)
  let e := affineUnitSectionsIso A B
  let e' := genericUnitSectionsIso A B F
  let m := (genericPointUnitsHom A F).hom.app (op (algebraEtaleObject A B))
  have h : m ≫ e'.hom = e.hom ≫ i := genericPointUnitsHom_onAffine A B F
  refine ⟨fun {Z} a b hab => ?_⟩
  apply (cancel_mono e.hom).mp
  apply (cancel_mono i).mp
  simpa only [Category.assoc, ← h] using congrArg (fun k => k ≫ e'.hom) hab

set_option maxHeartbeats 900000 in
/-- The monomorphism holds on every object of the actual small affine étale site. -/
theorem genericPointUnitsHom_onAffineSite_mono (A F : Type) [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (U : (Spec (CommRingCat.of A)).AffineEtale) :
    Mono ((genericPointUnitsHom A F).hom.app
      (op ((Scheme.AffineEtale.Spec (Spec (CommRingCat.of A))).obj U))) := by
  let X := Spec (CommRingCat.of A)
  let R : CommRingCat.{0} := unop U.left
  obtain ⟨a, ha⟩ := Spec.map_surjective U.hom
  letI : Algebra A R := a.hom.toAlgebra
  have haEtale : Etale (Spec.map a) := ha.symm ▸ U.prop
  letI : Algebra.Etale A R := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp haEtale)
  have heq : Spec.map (CommRingCat.ofHom (algebraMap A R)) = U.hom :=
    (congrArg Spec.map (CommRingCat.ofHom_hom a)).trans ha
  let V := (Scheme.AffineEtale.Spec X).obj U
  let W := algebraEtaleObject A R
  let e : W ≅ V := MorphismProperty.Over.isoMk (Iso.refl (Spec R)) (by
    change 𝟙 (Spec R) ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap A R))
    exact (Category.id_comp U.hom).trans heq.symm)
  let m := genericPointUnitsHom A F
  let I := (fullCoordinateUnitSheaf X).obj.map e.hom.op
  let J := (genericUnitImage A F).obj.map e.hom.op
  have h : I ≫ m.hom.app (op W) = m.hom.app (op V) ≫ J := m.hom.naturality e.hom.op
  letI : IsIso I := by dsimp [I]; infer_instance
  letI : Mono (m.hom.app (op W)) := genericPointUnitsHom_onAlgebra_mono A R F
  change Mono (m.hom.app (op V))
  refine ⟨fun {Z} f g hfg => ?_⟩
  apply (cancel_mono I).mp
  apply (cancel_mono (m.hom.app (op W))).mp
  simpa only [Category.assoc, h] using congrArg (fun k => k ≫ J) hfg

set_option maxHeartbeats 900000 in
/-- The canonical map from regular units to the generic-point direct image
is monic on the full small étale site of an affine domain. -/
theorem genericPointUnitsHom_mono (A F : Type) [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F] : Mono (genericPointUnitsHom A F) := by
  let X := Spec (CommRingCat.of A)
  let R := (Scheme.AffineEtale.sheafEquiv X AddCommGrpCat.{0}).inverse
  let m := genericPointUnitsHom A F
  have h : Mono (R.map m).hom := (NatTrans.mono_iff_mono_app _).2 (by
    intro U
    change Mono (m.hom.app (op ((Scheme.AffineEtale.Spec X).obj (unop U))))
    exact genericPointUnitsHom_onAffineSite_mono A F (unop U))
  letI : Mono (R.map m).hom := h
  exact R.mono_of_mono_map (Sheaf.Hom.mono_of_presheaf_mono (R.map m))

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GenericEtaleUnitSections.genericPointUnitsHom_onAlgebra_mono,
      ``ManuscriptAudit.GenericEtaleUnitSections.genericPointUnitsHom_onAffineSite_mono,
      ``ManuscriptAudit.GenericEtaleUnitSections.genericPointUnitsHom_mono] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
