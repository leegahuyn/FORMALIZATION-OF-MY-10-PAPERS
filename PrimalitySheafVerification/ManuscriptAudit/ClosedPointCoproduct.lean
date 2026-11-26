import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.ExactSupportDetection

namespace ManuscriptAudit.ClosedPointSupportDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 4000
set_option maxHeartbeats 12000
set_option maxRecDepth 512

private abbrev G := AddCommGrpCat.{0}

/-- The point factor used for the native support witness. -/
def pointFactor {X : TopCat.{0}} (P : Set X) (p : P) : AbelianSheaf X := by
  classical
  exact skyscraperSheaf (p : X) (AddCommGrpCat.of (ZMod 2))

/-- Abelian sheaves have each small discrete colimit by their native
Grothendieck abelian structure. Keeping the shape explicit avoids searching
through unrelated general colimit constructions at each use. -/
set_option synthInstance.maxHeartbeats 30000 in
set_option maxHeartbeats 50000 in
theorem abelianSheaf_hasDiscreteColimit (X : TopCat.{0}) {ι : Type}
    (D : Discrete ι ⥤ AbelianSheaf X) : HasColimit D :=
  let h : HasColimitsOfSize.{0, 0} (AbelianSheaf X) := IsGrothendieckAbelian.hasColimits
  (h.has_colimits_of_shape (Discrete ι)).has_colimit D

local instance pointFactor_hasCoproduct {X : TopCat.{0}} (P : Set X) :
    HasCoproduct (pointFactor P) :=
  abelianSheaf_hasDiscreteColimit X (Discrete.functor (pointFactor P))

/-- Coproduct of the point factors, also for an infinite indexing set. -/
def supportSheaf (X : TopCat.{0}) (P : Set X) : AbelianSheaf X :=
  ∐ pointFactor P

theorem mapCoproduct_isZero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {ι : Type*} (F : C ⥤ D) (objects : ι → C)
    [HasCoproduct objects] [PreservesColimit (Discrete.functor objects) F]
    (h : ∀ i, IsZero (F.obj (objects i))) : IsZero (F.obj (∐ objects)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  exact Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit F objects) _ _
    (fun i => (h i).eq_of_src _ _)

private theorem exists_ι_split {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} (S : ι → C) [HasCoproduct S] (i : ι) :
    ∃ r : (∐ S) ⟶ S i, Sigma.ι S i ≫ r = 𝟙 _ := by
  classical
  let legs : (j : ι) → S j ⟶ S i :=
    fun j => if h : j = i then eqToHom (congrArg S h) else 0
  exact ⟨Sigma.desc legs, by rw [Sigma.ι_desc]; simp [legs]⟩

/-- Every factor remains a retract after applying any functor to abelian groups. -/
theorem supportSheaf_nontrivial_of_factor {X : TopCat.{0}} (P : Set X) (p : P)
    (T : AbelianSheaf X ⥤ G) (hp : Nontrivial (T.obj (pointFactor P p))) :
    Nontrivial (T.obj (supportSheaf X P)) := by
  letI := hp
  let j : pointFactor P p ⟶ supportSheaf X P := Sigma.ι (pointFactor P) p
  obtain ⟨r, hr⟩ := exists_ι_split (pointFactor P) p
  have h : T.map j ≫ T.map r = 𝟙 _ := by rw [← T.map_comp, hr, T.map_id]
  have hl : Function.LeftInverse (T.map r) (T.map j) := by
    intro a
    change (T.map j ≫ T.map r) a = a
    rw [h, AddCommGrpCat.id_apply]
  exact hl.injective.nontrivial

end

end ManuscriptAudit.ClosedPointSupportDetection
