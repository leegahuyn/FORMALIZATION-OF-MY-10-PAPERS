import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.FiniteSkyscraperSumHOne

/-!
# Finite closed support on a Zariski space

For a topological abelian sheaf concentrated on finitely many closed
points, the natural units of the stalk–skyscraper adjunction identify the
sheaf with the product of the skyscrapers of its stalks. Its native first
sheaf cohomology vanishes by the finite-sum calculation.
-/

namespace ManuscriptAudit.FiniteClosedSkyscraperDecomposition

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.FiniteSkyscraperSumHOne
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev G := AddCommGrpCat.{0}

private abbrev stalkAt {X : TopCat.{0}} (x : X) : AbelianSheaf X ⥤ G :=
  TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x

private theorem stalkAt_preservesFiniteLimits {X : TopCat.{0}} (x : X) :
    PreservesFiniteLimits (stalkAt x) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x))

private theorem mapProduct_isZero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {ι : Type*} (T : C ⥤ D) (S : ι → C)
    [HasProduct S] [PreservesLimit (Discrete.functor S) T]
    (h : ∀ i, IsZero (T.obj (S i))) : IsZero (T.obj (∏ᶜ S)) := by
  apply (IsZero.iff_id_eq_zero _).2
  exact Fan.IsLimit.hom_ext
    (isLimitOfHasProductOfPreservesLimit T S) _ _ (fun i => (h i).eq_of_tgt _ _)

private theorem mapProduct_projection_isIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {ι : Type*} (T : C ⥤ D) (S : ι → C)
    [HasProduct S] [PreservesLimit (Discrete.functor S) T] (j : ι)
    (h : ∀ i, i ≠ j → IsZero (T.obj (S i))) : IsIso (T.map (Pi.π S j)) := by
  classical
  let hc := isLimitOfHasProductOfPreservesLimit T S
  let legs : (i : ι) → T.obj (S j) ⟶ T.obj (S i) :=
    fun i => if e : j = i then eqToHom (congrArg (fun k => T.obj (S k)) e) else 0
  let u : T.obj (S j) ⟶ T.obj (∏ᶜ S) := Fan.IsLimit.lift hc legs
  have hu : u ≫ T.map (Pi.π S j) = 𝟙 _ := by
    exact (Fan.IsLimit.fac hc legs j).trans (by simp [legs])
  have hv : T.map (Pi.π S j) ≫ u = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext hc
    intro i
    by_cases hi : i = j
    · subst i
      change (T.map (Pi.π S j) ≫ u) ≫ T.map (Pi.π S j) = 𝟙 _ ≫ T.map (Pi.π S j)
      rw [Category.assoc, hu, Category.comp_id, Category.id_comp]
    · exact (h i hi).eq_of_tgt _ _
  let e : T.obj (∏ᶜ S) ≅ T.obj (S j) :=
    ⟨T.map (Pi.π S j), u, hv, hu⟩
  exact e.isIso_hom

/-- The actual skyscraper with coefficient the stalk of the original sheaf. -/
def pointFactor {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) (p : P) :
    AbelianSheaf X :=
  pointSummand (p : X) ((stalkAt (p : X)).obj F)

private def pointUnit {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) (p : P) :
    F ⟶ pointFactor F P p := by
  classical
  exact (stalkSkyscraperSheafAdjunction (C := G) (p : X)).unit.app F

/-- The single morphism given by the units of the stalk–skyscraper adjunctions. -/
def toPointProduct {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) :
    F ⟶ ∏ᶜ pointFactor F P :=
  Pi.lift (pointUnit F P)

private theorem unit_stalk_isIso {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) (p : P) :
    IsIso ((stalkAt (p : X)).map (pointUnit F P p)) := by
  classical
  let e := skyscraperPresheafStalkOfSpecializes (p : X) ((stalkAt (p : X)).obj F)
    (specializes_rfl : Specializes (p : X) (p : X))
  have h : (stalkAt (p : X)).map (pointUnit F P p) ≫ e.hom = 𝟙 _ :=
    (stalkSkyscraperSheafAdjunction (C := G) (p : X)).left_triangle_components F
  have he : (stalkAt (p : X)).map (pointUnit F P p) = e.inv := by
    apply (cancel_mono e.hom).mp
    exact h.trans e.inv_hom_id.symm
  rw [he]
  exact e.isIso_inv

private theorem factor_stalk_isZero {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X)
    (hClosed : ∀ p ∈ P, IsClosed ({p} : Set X)) (p : P) {x : X} (hx : x ≠ (p : X)) :
    IsZero ((stalkAt x).obj (pointFactor F P p)) := by
  classical
  have h : ¬ Specializes (p : X) x := by
    intro hs
    exact hx (Set.mem_singleton_iff.mp
      (hs.mem_closed (hClosed (p : X) p.property) (by simp)))
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal (p : X)
    ((stalkAt (p : X)).obj F) h).isZero

/-- A sheaf supported on finitely many closed points is canonically the product
of the skyscrapers of its stalks. -/
theorem toPointProduct_isIso {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) [Finite P]
    (hClosed : ∀ p ∈ P, IsClosed ({p} : Set X)) (hSupport : stalkSupport F ⊆ P) :
    IsIso (toPointProduct F P) := by
  classical
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (C := G) (toPointProduct F P)).2
  intro x
  let T := stalkAt x
  change IsIso (T.map (toPointProduct F P))
  letI : PreservesFiniteLimits T := stalkAt_preservesFiniteLimits x
  by_cases hx : x ∈ P
  · let p : P := ⟨x, hx⟩
    let π := Pi.π (pointFactor F P) p
    haveI : IsIso (T.map π) := by
      apply mapProduct_projection_isIso T (pointFactor F P) p
      intro q hq
      apply factor_stalk_isZero F P hClosed q (x := x)
      intro h
      exact hq (Subtype.ext h.symm)
    have hLeg : toPointProduct F P ≫ π = pointUnit F P p :=
      Pi.lift_π (pointUnit F P) p
    have hComp : T.map (toPointProduct F P) ≫ T.map π = T.map (pointUnit F P p) :=
      (T.map_comp (toPointProduct F P) π).symm.trans
        (congrArg (fun f : F ⟶ pointFactor F P p => T.map f) hLeg)
    haveI : IsIso (T.map (toPointProduct F P) ≫ T.map π) := by
      rw [hComp]
      exact unit_stalk_isIso F P p
    exact IsIso.of_isIso_comp_right (T.map (toPointProduct F P)) (T.map π)
  · have hSrc : IsZero (T.obj F) := by
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      apply not_nontrivial_iff_subsingleton.mp
      intro hn
      exact hx (hSupport (show x ∈ stalkSupport F from hn))
    have hTgt : IsZero (T.obj (∏ᶜ pointFactor F P)) := by
      apply mapProduct_isZero T (pointFactor F P)
      intro p
      exact factor_stalk_isZero F P hClosed p (x := x) (fun he =>
        hx (by simpa [he] using p.property))
    exact isIso_of_source_target_iso_zero (T.map (toPointProduct F P)) hSrc.isoZero hTgt.isoZero

/-- The canonical isomorphism with the product of point skyscrapers. -/
def pointProductIso {X : TopCat.{0}} (F : AbelianSheaf X) (P : Set X) [Finite P]
    (hClosed : ∀ p ∈ P, IsClosed ({p} : Set X)) (hSupport : stalkSupport F ⊆ P) :
    F ≅ ∏ᶜ pointFactor F P := by
  letI := toPointProduct_isIso F P hClosed hSupport
  exact asIso (toPointProduct F P)

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

local instance sheaf_hasCoproduct {X : TopCat.{0}} {ι : Type} (S : ι → AbelianSheaf X) :
    HasCoproduct S := ClosedPointSupportDetection.abelianSheaf_hasDiscreteColimit X (Discrete.functor S)

/-- The degree-one Zariski cohomology of any sheaf with finite closed stalk support vanishes. -/
theorem H1_subsingleton_of_finite_closed_support {X : TopCat.{0}} (F : AbelianSheaf X)
    (P : Set X) [Finite P] (hClosed : ∀ p ∈ P, IsClosed ({p} : Set X))
    (hSupport : stalkSupport F ⊆ P) : Subsingleton (F.H 1) := by
  let e : F ≅ ∐ pointFactor F P :=
    pointProductIso F P hClosed hSupport ≪≫ biproductIso (pointFactor F P)
  letI : Subsingleton ((∐ pointFactor F P).H 1) :=
    finiteCoproduct_H1_subsingleton (pointFactor F P)
      (fun p => pointSummand_isFlasque (p : X) ((stalkAt (p : X)).obj F))
  let h := (Sheaf.functorH (Opens.grothendieckTopology X) 1).mapIso e
  exact h.addCommGroupIsoToAddEquiv.injective.subsingleton

end

end ManuscriptAudit.FiniteClosedSkyscraperDecomposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteClosedSkyscraperDecomposition.toPointProduct_isIso,
      ``ManuscriptAudit.FiniteClosedSkyscraperDecomposition.pointProductIso,
      ``ManuscriptAudit.FiniteClosedSkyscraperDecomposition.H1_subsingleton_of_finite_closed_support] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
