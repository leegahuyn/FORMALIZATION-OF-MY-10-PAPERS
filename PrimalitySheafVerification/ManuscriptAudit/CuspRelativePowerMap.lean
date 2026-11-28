import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Gluing
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerCoordinates
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersectionMaps

/-! The coefficient-preserving power maps glue on the actual projective cusp. -/

namespace ManuscriptAudit.CuspRelativePowerMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspPunctured (CuspSubalgebra)
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen affine_chart_cover)
open CuspChartIntersection (laurentToAffineLine overlapIsoLaurent)
open CuspChartIntersectionMaps (laurentToAffineCusp laurent_maps_commute
  overlapIsoLaurent_inv_toAffineLine overlapIsoLaurent_inv_toAffineCusp)
open CuspRelativePowerCoordinates (cuspPower laurentPower)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

private abbrev A := affineCusp K
private abbrev Y := Spec (CommRingCat.of (Polynomial K))
private abbrev W := Spec (CommRingCat.of (LaurentPolynomial K))

/-- The actual affine line chart endomorphism. -/
def lineMap (m : ℕ) : Y K ⟶ Y K :=
  Spec.map (CommRingCat.ofHom (Polynomial.expand K m).toRingHom)

/-- The actual affine cusp chart endomorphism. -/
def affineMap (m : ℕ) (hm : 2 ≤ m) : A K ⟶ A K :=
  Spec.map (CommRingCat.ofHom (cuspPower K m hm).toRingHom)

/-- The actual Laurent overlap endomorphism. -/
def overlapMap (m : ℕ) : W K ⟶ W K :=
  Spec.map (CommRingCat.ofHom (laurentPower K m).toRingHom)

private abbrev inverseLaurent : Polynomial K →ₐ[K] LaurentPolynomial K :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

private theorem affineLaurent_formula :
    laurentToAffineCusp K = Spec.map (CommRingCat.ofHom
      ((inverseLaurent K).comp (CuspSubalgebra K).val).toRingHom) := by
  unfold CuspChartIntersectionMaps.laurentToAffineCusp CuspYChartImage.laurentToCusp
  rw [← Spec.map_comp] <;> rfl

theorem line_overlap_commutes (m : ℕ) :
    laurentToAffineLine K ≫ lineMap K m = overlapMap K m ≫ laurentToAffineLine K := by
  unfold CuspChartIntersection.laurentToAffineLine lineMap overlapMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact DFunLike.congr_fun (CuspRelativePowerCoordinates.toLaurent_commutes K m).symm f

theorem affine_overlap_commutes (m : ℕ) (hm : 2 ≤ m) :
    laurentToAffineCusp K ≫ affineMap K m hm = overlapMap K m ≫ laurentToAffineCusp K := by
  rw [affineLaurent_formula]
  unfold affineMap overlapMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact DFunLike.congr_fun (CuspRelativePowerCoordinates.inverseLaurent_commutes K m).symm f.val

private def chart : Bool → Scheme.{u}
  | false => A K
  | true => Y K

private def inclusion : (i : Bool) → chart K i ⟶ projectiveCusp K
  | false => affineOpen K
  | true => lineOpen K

private def cover : (projectiveCusp K).OpenCover.{0} where
  I₀ := Bool
  X := chart K
  f := inclusion K
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      have hx : x ∈ Set.range (affineOpen K) ∪ Set.range (lineOpen K) := by
        have hCover : Set.range (affineOpen K) ∪ Set.range (lineOpen K) = Set.univ :=
          congrArg (fun O : (projectiveCusp K).Opens ↦ (O : Set (projectiveCusp K)))
            (affine_chart_cover K)
        rw [hCover]
        exact Set.mem_univ x
      rcases hx with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · intro i
      cases i <;> infer_instance

variable (m : ℕ) (hm : 2 ≤ m)

private def localMap : (i : Bool) → chart K i ⟶ projectiveCusp K
  | false => affineMap K m hm ≫ affineOpen K
  | true => lineMap K m ≫ lineOpen K

private theorem agree_mixed :
    pullback.fst (affineOpen K) (lineOpen K) ≫ localMap K m hm false =
      pullback.snd (affineOpen K) (lineOpen K) ≫ localMap K m hm true := by
  apply (cancel_epi (overlapIsoLaurent K).inv).mp
  simp only [← Category.assoc, overlapIsoLaurent_inv_toAffineCusp,
    overlapIsoLaurent_inv_toAffineLine]
  change laurentToAffineCusp K ≫ (affineMap K m hm ≫ affineOpen K) =
    laurentToAffineLine K ≫ (lineMap K m ≫ lineOpen K)
  rw [← Category.assoc, ← Category.assoc, affine_overlap_commutes, line_overlap_commutes,
    Category.assoc, Category.assoc, laurent_maps_commute]

private theorem agree_same {U V : Scheme.{u}} (j : U ⟶ V) [Mono j] (g : U ⟶ V) :
    pullback.fst j j ≫ g = pullback.snd j j ≫ g :=
  congrArg (fun a ↦ a ≫ g) ((cancel_mono j).mp pullback.condition)

private theorem agree (i j : Bool) :
    pullback.fst ((cover K).f i) ((cover K).f j) ≫ localMap K m hm i =
      pullback.snd ((cover K).f i) ((cover K).f j) ≫ localMap K m hm j := by
  cases i <;> cases j
  · exact agree_same _ _
  · exact agree_mixed K m hm
  · change pullback.fst (lineOpen K) (affineOpen K) ≫ localMap K m hm true =
      pullback.snd (lineOpen K) (affineOpen K) ≫ localMap K m hm false
    apply (cancel_epi (pullbackSymmetry (affineOpen K) (lineOpen K)).hom).mp
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd] using (agree_mixed K m hm).symm
  · exact agree_same _ _

/-- The actual endomorphism glued on the projective cusp from its two open charts. -/
def projectiveMap : projectiveCusp K ⟶ projectiveCusp K :=
  (cover K).glueMorphisms (localMap K m hm) (agree K m hm)

@[reassoc]
theorem affine_projectiveMap :
    affineOpen K ≫ projectiveMap K m hm = affineMap K m hm ≫ affineOpen K :=
  (cover K).ι_glueMorphisms _ _ false

@[reassoc]
theorem line_projectiveMap :
    lineOpen K ≫ projectiveMap K m hm = lineMap K m ≫ lineOpen K :=
  (cover K).ι_glueMorphisms _ _ true

end
end ManuscriptAudit.CuspRelativePowerMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspRelativePowerMap.line_overlap_commutes,
      ``ManuscriptAudit.CuspRelativePowerMap.affine_overlap_commutes,
      ``ManuscriptAudit.CuspRelativePowerMap.affine_projectiveMap,
      ``ManuscriptAudit.CuspRelativePowerMap.line_projectiveMap] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
