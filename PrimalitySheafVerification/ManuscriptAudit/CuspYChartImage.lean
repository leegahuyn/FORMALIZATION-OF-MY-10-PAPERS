import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartOverlapAlgebra

/-!
The Laurent parametrizations are the same actual scheme map in the
projective plane. Their dense images identify the schematic-image
ideals of the original affine cusp and the affine line in the
second chart.
-/

namespace ManuscriptAudit.CuspYChartImage

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspPunctured CuspProperCompactification CuspYChartAlgebra CuspYChartOverlapAlgebra

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 512

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

/-- The Laurent line using the affine cusp normalization coordinate. -/
def laurentToCusp : Spec (CommRingCat.of (LaurentRing K)) ⟶ affineCusp K :=
  Spec.map (CommRingCat.ofHom (cuspLaurent K).toRingHom)

/-- The Laurent line using the inverse coordinate in the infinity chart. -/
def laurentToLine : Spec (CommRingCat.of (LaurentRing K)) ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  Spec.map (CommRingCat.ofHom (lineLaurent K).toRingHom)

private def yzChartι : Spec (CommRingCat.of (YZChartRing K)) ⟶ plane K :=
  Proj.awayι (grading K) (yz K) (SetLike.mul_mem_graded (X_mem_one K 1) (X_mem_one K 2))
    (by decide)

private theorem cuspPlaneViaYZ :
    laurentToCusp K ≫ cuspInPlane K =
      Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ yzChartι K := by
  have hmap :
      laurentToCusp K ≫ Spec.map (CommRingCat.ofHom (affineChartEvaluation K)) =
        Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ Spec.map (CommRingCat.ofHom (zToYZ K)) := by
    unfold laurentToCusp
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_z K).symm)
  rw [cuspInPlane_as_Z_chart, ← Category.assoc, hmap, Category.assoc]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ f)
    (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 2) (by decide)
      (X_mem_one K 1) (show yz K = z K * y K from mul_comm _ _))

private theorem linePlaneViaYZ :
    laurentToLine K ≫ lineInPlane K =
      Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ yzChartι K := by
  have hmap :
      laurentToLine K ≫ Spec.map (CommRingCat.ofHom (evalYChart K)) =
        Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ Spec.map (CommRingCat.ofHom (yToYZ K)) := by
    unfold laurentToLine
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_y K).symm)
  unfold lineInPlane
  rw [← Category.assoc, hmap, Category.assoc]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ f)
    (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 1) (by decide)
      (X_mem_one K 2) (show yz K = y K * z K from rfl))

/-- The two Laurent chart maps agree in the actual projective plane. -/
theorem laurentPlane_eq :
    laurentToCusp K ≫ cuspInPlane K = laurentToLine K ≫ lineInPlane K :=
  (cuspPlaneViaYZ K).trans (linePlaneViaYZ K).symm

private theorem specMap_dominant_of_injective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := f)).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

theorem cuspKernel_lineKernel :
    (cuspInPlane K).ker = (lineInPlane K).ker := by
  haveI : IsDominant (laurentToCusp K) :=
    specMap_dominant_of_injective _ (Polynomial.toLaurent_injective.comp Subtype.val_injective)
  haveI : IsDominant (laurentToLine K) :=
    specMap_dominant_of_injective _
      (LaurentPolynomial.invert.injective.comp Polynomial.toLaurent_injective)
  haveI : IsSchemeTheoreticallyDominant (laurentToCusp K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : IsSchemeTheoreticallyDominant (laurentToLine K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hC : (laurentToCusp K ≫ cuspInPlane K).ker = (cuspInPlane K).ker := by
    rw [Scheme.Hom.ker_comp, (laurentToCusp K).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hY : (laurentToLine K ≫ lineInPlane K).ker = (lineInPlane K).ker := by
    rw [Scheme.Hom.ker_comp, (laurentToLine K).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  exact hC.symm.trans ((congrArg Scheme.Hom.ker
    (laurentPlane_eq K)).trans hY)


end

end ManuscriptAudit.CuspYChartImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspYChartImage.laurentPlane_eq,
      ``ManuscriptAudit.CuspYChartImage.cuspKernel_lineKernel] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
