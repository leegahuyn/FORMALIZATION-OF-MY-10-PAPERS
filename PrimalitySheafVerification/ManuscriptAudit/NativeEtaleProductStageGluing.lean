import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.RingTheory.Etale.Pi
import PrimalitySheafVerification.ManuscriptAudit.FiniteProductSpectrumOpen
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! On the actual finite disjoint union of affine étale stages, the
actual sections are the product of the component sections. -/

namespace ManuscriptAudit.NativeEtaleProductStageGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap specMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private theorem underlying_isSheaf :
    Presieve.IsSheaf (X (A := A)).smallEtaleTopology (I.obj ⋙ CategoryTheory.forget G.{u}) := by
  letI : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget G.{u}) :=
    AddCommGrpCat.adj.rightAdjoint_preservesLimits
  exact (isSheaf_iff_isSheaf_of_type (X (A := A)).smallEtaleTopology _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget G.{u}) I.property)

private theorem empty_subsingleton (U : (X (A := A)).Etale) [IsEmpty U.left] :
    Subsingleton (I.obj.obj (op U)) := by
  let P := I.obj ⋙ CategoryTheory.forget G.{u}
  let V : PEmpty.{u + 1} → (X (A := A)).Etale := PEmpty.elim
  let f : ∀ i, V i ⟶ U := fun i ↦ PEmpty.elim i
  have hc : Sieve.ofArrows V f ∈ (X (A := A)).smallEtaleTopology U :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
      (Set.eq_univ_of_forall fun x ↦ isEmptyElim x)
  obtain ⟨y, _, h⟩ := (Presieve.isSheafFor_arrows_iff (P := P) f).mp
    ((underlying_isSheaf I).isSheafFor _ hc) (fun i ↦ PEmpty.elim i) (fun i ↦ PEmpty.elim i)
  exact ⟨fun a b ↦ (h a (fun i ↦ PEmpty.elim i)).trans (h b (fun i ↦ PEmpty.elim i)).symm⟩

variable {ι : Type u} [Finite ι] (C : ι → Type u) [∀ i, CommRing (C i)]
  [∀ i, Algebra A (C i)] [∀ i, Algebra.Etale A (C i)]

private instance (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D] :
    Etale (structureMap A D) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap A D))).mpr ((RingHom.etale_algebraMap).mpr inferInstance)

/-- An actual affine étale scheme identified by its given algebra. -/
abbrev objectOf (D : Type u) [CommRing D] [Algebra A D] [Algebra.Etale A D] :
    (X (A := A)).Etale :=
  Scheme.Etale.mk (structureMap A D)

/-- The genuine inclusion of one affine component of the product. -/
abbrev component (i : ι) :
    objectOf (A := A) (C i) ⟶ objectOf (A := A) (∀ j, C j) :=
  MorphismProperty.Over.homMk (specMap A (Pi.evalAlgHom A C i))
    (ProetaleAffineTensor.specMap_structureMap A (Pi.evalAlgHom A C i))

set_option maxHeartbeats 3900000 in
/-- Arbitrary affine-stage values glue uniquely on the literal affine
product stage. Intersections of distinct components are empty in the
actual site, so no matching condition is needed. -/
theorem existsUnique_sections (x : ∀ i, I.obj.obj (op (objectOf (A := A) (C i)))) :
    ∃! y : I.obj.obj (op (objectOf (A := A) (∀ i, C i))),
      ∀ i, I.obj.map (component (A := A) C i).op y = x i := by
  let P := I.obj ⋙ CategoryTheory.forget G.{u}
  let V (i : ι) := objectOf (A := A) (C i)
  let T := objectOf (A := A) (∀ i, C i)
  let f (i : ι) : V i ⟶ T := component (A := A) C i
  have hCov : Sieve.ofArrows V f ∈ (X (A := A)).smallEtaleTopology T := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    exact Set.eq_univ_of_forall (fun p ↦ Set.mem_iUnion.mpr
      (FiniteProductSpectrumOpen.exists_component C p))
  have hComp : Presieve.Arrows.Compatible P f x := by
    intro i j W a b hab
    have hSch : a.left ≫ (f i).left = b.left ≫ (f j).left :=
      congrArg (fun d : W ⟶ T ↦ d.left) hab
    by_cases hij : i = j
    · subst j
      letI : IsOpenImmersion (f i).left := FiniteProductSpectrumOpen.projection_isOpenImmersion C i
      have he : a = b := by
        apply MorphismProperty.Over.Hom.ext
        exact (cancel_mono (f i).left).mp hSch
      rw [he]
    · letI : IsEmpty W.left := ⟨fun w ↦ by
        have he := congrArg (fun d : W.left ⟶ T.left ↦ d w) hSch
        change FiniteProductSpectrumOpen.projection C i (a.left w) =
          FiniteProductSpectrumOpen.projection C j (b.left w) at he
        have hSigma : (PrimeSpectrum.sigmaToPiHomeo C) ⟨i, a.left w⟩ =
            (PrimeSpectrum.sigmaToPiHomeo C) ⟨j, b.left w⟩ := by
          rw [PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply,
            PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply]
          exact he
        exact hij (congrArg Sigma.fst ((PrimeSpectrum.sigmaToPiHomeo C).injective hSigma))⟩
      exact @Subsingleton.elim _ (empty_subsingleton I W) _ _
  exact (Presieve.isSheafFor_arrows_iff (P := P) f).mp
    ((underlying_isSheaf I).isSheafFor _ hCov) x hComp

end
end ManuscriptAudit.NativeEtaleProductStageGluing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeEtaleProductStageGluing.existsUnique_sections
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
