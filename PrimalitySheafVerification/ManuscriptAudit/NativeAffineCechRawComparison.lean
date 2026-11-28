import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCechConerveSiteArrowMaps
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineUnderRingRawSections

/-! Actual Čech terms of the native inverse image are the raw
affine sections of their literal ring conerve, compatibly with maps. -/

namespace ManuscriptAudit.NativeAffineCechRawComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineCechConerveSiteComparison (siteMap native property_degree siteIso)
open AffineCechConerveSiteArrowMaps (siteSquare siteIso_naturality)
open AffineCechConerveSpecLimit (degree)
open NativeAffineUnderRingRawSections (groups restriction)
open NativeAffineEtaleKanComparison (toNative)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev R := CommRingCat.of A
private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

abbrev nativePresheaf := ((EtaleProetaleInverseImage.inverseImage (X (A := A))).obj I).obj

variable (f : Arrow (Under (R (A := A))))
  [WeaklyEtale (Spec.map f.left.hom)] [WeaklyEtale (Spec.map f.right.hom)]

abbrev nativeArrow := siteMap @WeaklyEtale f inferInstance inferInstance
abbrev nerve (n : ℕ) := native @WeaklyEtale f inferInstance inferInstance n

instance degree_weaklyEtale (n : ℕ) : WeaklyEtale (Spec.map (degree f n).hom) :=
  property_degree @WeaklyEtale f inferInstance inferInstance n

private abbrev j (n : ℕ) := siteIso @WeaklyEtale f inferInstance inferInstance n

/-- Read the actual raw affine section in the literal native Čech term. -/
def comparison (n : ℕ) : groups I (degree f n) ⟶ (nativePresheaf I).obj (op (nerve f n)) :=
  (toNative (X (A := A)) I).app (op (NativeAffineUnderRingRawSections.chart (degree f n))) ≫
    (nativePresheaf I).map (j f n).inv.op

set_option maxHeartbeats 4500000 in
/-- Actual affine section comparison gives a bijection on the actual Čech term. -/
theorem comparison_bijective
    (h : ∀ (V : (X (A := A)).ProEt), IsAffine V.left →
      Function.Bijective ((toNative (X (A := A)) I).app (op V))) (n : ℕ) :
    Function.Bijective (comparison I f n) := by
  have hs : Function.Surjective ((nativePresheaf I).map (j f n).inv.op) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  have hi : Function.Injective ((nativePresheaf I).map (j f n).inv.op) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  exact Function.Bijective.comp ⟨hi, hs⟩ (h _ inferInstance)

variable {f} {g : Arrow (Under (R (A := A)))}
  [WeaklyEtale (Spec.map g.left.hom)] [WeaklyEtale (Spec.map g.right.hom)]
  (s : f ⟶ g)

set_option maxHeartbeats 6000000 in
/-- No face map is substituted: the comparison commutes with the actual
Čech restriction induced by the actual square of covers. -/
theorem comparison_natural (n : ℕ) :
    comparison I f n ≫ (nativePresheaf I).map
        ((Arrow.mapCechNerve (siteSquare @WeaklyEtale inferInstance inferInstance inferInstance inferInstance s)).app
          (op ⦋n⦌)).op =
      restriction I ((Arrow.mapCechConerve s).app ⦋n⦌) ≫ comparison I g n := by
  let η := toNative (X (A := A)) I
  let p := (Arrow.mapCechConerve s).app ⦋n⦌
  let q := (Arrow.mapCechNerve
    (siteSquare @WeaklyEtale inferInstance inferInstance inferInstance inferInstance s)).app (op ⦋n⦌)
  let a := NativeAffineUnderRingRawSections.arrow p
  have hn : a ≫ (j f n).hom = (j g n).hom ≫ q :=
    siteIso_naturality @WeaklyEtale inferInstance inferInstance inferInstance inferInstance s n
  have h : q ≫ (j f n).inv = (j g n).inv ≫ a := by
    apply (cancel_mono (j f n).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, hn, Iso.inv_hom_id_assoc]
  change (η.app _ ≫ (nativePresheaf I).map (j f n).inv.op) ≫ (nativePresheaf I).map q.op =
    (NativeAffineEtaleKanComparison.raw (X (A := A)) I).map a.op ≫
      (η.app _ ≫ (nativePresheaf I).map (j g n).inv.op)
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp,
    ← Category.assoc, ← η.naturality, Category.assoc]

end
end ManuscriptAudit.NativeAffineCechRawComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineCechRawComparison.comparison_bijective,
      ``ManuscriptAudit.NativeAffineCechRawComparison.comparison_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
