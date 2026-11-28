import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerCartesian
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleHTwoLower

/-! The proper cusp's actual overlap may be presented by its explicit
Laurent spectrum, with the same projections and relative power. -/

namespace ManuscriptAudit.CuspLaurentNativeCoverGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (affineOpen projectiveCusp)
open CuspProperYChart (lineOpen)
open CuspChartIntersection (overlapIsoLaurent laurentToAffineLine)
open CuspChartIntersectionMaps (laurentToAffineCusp laurent_maps_commute
  overlapIsoLaurent_inv_toAffineCusp overlapIsoLaurent_inv_toAffineLine)
open CuspNativeProetaleHTwoLower (overlapOpen cover)
open CuspRelativePowerMap
open CuspRelativePowerCartesian (overlap_preimage)
open ProetaleOpenLocalLifts (openObject openArrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

instance affineLeg_openImmersion : IsOpenImmersion (laurentToAffineCusp K) := by
  rw [← overlapIsoLaurent_inv_toAffineCusp]
  infer_instance

/-- The actual common open displayed as the Laurent spectrum. -/
abbrev inclusion : Spec (CommRingCat.of (LaurentPolynomial K)) ⟶ projectiveCusp K :=
  laurentToAffineCusp K ≫ affineOpen K

abbrev first : openObject (inclusion K) ⟶ openObject (affineOpen K) :=
  MorphismProperty.Over.homMk (laurentToAffineCusp K) (by
    change laurentToAffineCusp K ≫ (𝟙 _ ≫ affineOpen K) = 𝟙 _ ≫ inclusion K
    simp only [Category.id_comp])

abbrev second : openObject (inclusion K) ⟶ openObject (lineOpen K) :=
  MorphismProperty.Over.homMk (laurentToAffineLine K) (by
    change laurentToAffineLine K ≫ (𝟙 _ ≫ lineOpen K) = 𝟙 _ ≫ inclusion K
    simp only [Category.id_comp]
    exact (laurent_maps_commute K).symm)

theorem scheme_isPullback :
    IsPullback (laurentToAffineCusp K) (laurentToAffineLine K) (affineOpen K) (lineOpen K) :=
  IsPullback.of_iso_pullback ⟨laurent_maps_commute K⟩ (overlapIsoLaurent K).symm
    (overlapIsoLaurent_inv_toAffineCusp K) (overlapIsoLaurent_inv_toAffineLine K)

theorem native_isPullback :
    IsPullback (first K) (second K) (openArrow (affineOpen K)) (openArrow (lineOpen K)) :=
  ProetaleAffineTensor.underlying_isPullback (scheme_isPullback K)

private theorem inclusion_formula :
    inclusion K = (overlapIsoLaurent K).inv ≫ overlapOpen K := by
  change laurentToAffineCusp K ≫ affineOpen K =
    (overlapIsoLaurent K).inv ≫ pullback.fst (affineOpen K) (lineOpen K) ≫ affineOpen K
  rw [← Category.assoc, overlapIsoLaurent_inv_toAffineCusp]

theorem relative_cartesian (m : ℕ) (hm : 2 ≤ m) :
    IsPullback (overlapMap K m) (inclusion K) (inclusion K) (projectiveMap K m hm) := by
  have hRange : (inclusion K).opensRange = (overlapOpen K).opensRange := by
    rw [inclusion_formula, Scheme.Hom.opensRange_comp_of_isIso]
  apply IsOpenImmersion.isPullback
  · change (laurentToAffineCusp K ≫ affineOpen K) ≫ projectiveMap K m hm =
      overlapMap K m ≫ (laurentToAffineCusp K ≫ affineOpen K)
    rw [Category.assoc, affine_projectiveMap, ← Category.assoc, affine_overlap_commutes,
      Category.assoc]
  · rw [hRange]
    exact overlap_preimage K m hm

end
end ManuscriptAudit.CuspLaurentNativeCoverGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspLaurentNativeCoverGeometry.native_isPullback,
      ``ManuscriptAudit.CuspLaurentNativeCoverGeometry.relative_cartesian] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
