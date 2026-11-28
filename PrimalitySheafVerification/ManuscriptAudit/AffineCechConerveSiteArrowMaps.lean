import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCechConerveSiteComparison

/-! The affine conerve-to-nerve comparison respects the actual arrows
between covers and all Čech-stage restriction maps. -/

namespace ManuscriptAudit.AffineCechConerveSiteArrowMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineCechConerveSiteComparison (Site forget map siteMap native property_degree siteIso schemeIso_vertex)
open CechNerveLowDegrees (vertex N)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : CommRingCat.{u}} (P : MorphismProperty Scheme.{u})
  [HasFiniteLimits (Site (A := A) P)]
  [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) (forget (A := A) P)]
  [P.RespectsIso]

variable {f g : Arrow (Under A)}
  (fL : P (Spec.map f.left.hom)) (fR : P (Spec.map f.right.hom))
  (gL : P (Spec.map g.left.hom)) (gR : P (Spec.map g.right.hom))
  (s : f ⟶ g)

/-- The actual square of schemes is the opposite of the ring square. -/
def siteSquare : Arrow.mk (siteMap P g gL gR) ⟶ Arrow.mk (siteMap P f fL fR) :=
  Arrow.homMk (map P s.right fR gR) (map P s.left fL gL) (by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map s.right.right ≫ Spec.map f.hom.right =
      Spec.map g.hom.right ≫ Spec.map s.left.right
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg (Under.forget A).map s.w.symm))

private theorem map_vertex (n : ℕ) (i : Fin (n + 1)) :
    (Arrow.mapCechNerve (siteSquare P fL fR gL gR s)).app (op ⦋n⦌) ≫ vertex (siteMap P f fL fR) n i =
      vertex (siteMap P g gL gR) n i ≫ (siteSquare P fL fR gL gR s).left := by
  rw [Arrow.mapCechNerve_app]
  exact WidePullback.lift_π _ _ _ _ _

private theorem vertex_map (n : ℕ) (i : Fin (n + 1)) :
    AffineCechConerveSpecLimit.vertex f n i ≫ (Arrow.mapCechConerve s).app ⦋n⦌ =
      s.right ≫ AffineCechConerveSpecLimit.vertex g n i := by
  rw [Arrow.mapCechConerve_app]
  exact WidePushout.ι_desc _ _ _ _ _

private theorem hom_ext_vertices {C : Type*} [Category* C] [HasFiniteLimits C]
    {U T W : C} (a : U ⟶ T) (n : ℕ) {p q : W ⟶ N a n}
    (h : ∀ i, p ≫ vertex a n i = q ≫ vertex a n i) : p = q := by
  apply WidePullback.hom_ext
  · exact h
  · rw [← WidePullback.π_arrow (fun _ : Fin (n + 1) ↦ a) (0 : Fin (n+1)),
      ← Category.assoc, ← Category.assoc, h]

set_option maxHeartbeats 5400000 in
/-- The section comparison retains the actual maps on every
nerve term of a square of affine coverings. -/
theorem siteIso_naturality (n : ℕ) :
    map P ((Arrow.mapCechConerve s).app ⦋n⦌) (property_degree P f fL fR n)
        (property_degree P g gL gR n) ≫ (siteIso P f fL fR n).hom =
      (siteIso P g gL gR n).hom ≫
        (Arrow.mapCechNerve (siteSquare P fL fR gL gR s)).app (op ⦋n⦌) := by
  apply hom_ext_vertices (siteMap P f fL fR) n
  intro i
  rw [Category.assoc, Category.assoc, map_vertex]
  apply MorphismProperty.Over.Hom.ext
  change Spec.map ((Arrow.mapCechConerve s).app ⦋n⦌).right ≫
      (AffineCechConerveSiteComparison.schemeIso P f fL fR n).hom ≫
        (vertex (siteMap P f fL fR) n i).left =
    (AffineCechConerveSiteComparison.schemeIso P g gL gR n).hom ≫
      (vertex (siteMap P g gL gR) n i).left ≫ Spec.map s.right.right
  rw [schemeIso_vertex, ← Category.assoc, schemeIso_vertex, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg (Under.forget A).map (vertex_map s n i))

end
end ManuscriptAudit.AffineCechConerveSiteArrowMaps

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineCechConerveSiteArrowMaps.siteIso_naturality
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
