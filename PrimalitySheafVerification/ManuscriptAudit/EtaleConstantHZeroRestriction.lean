import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperCohomology
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary

/-! Actual sections of a constant abelian sheaf on a preconnected étale
object all extend as constants to any larger étale object over the base. -/

namespace ManuscriptAudit.EtaleConstantHZeroRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Opposite
open SheafPresheafHOneBoundary EtaleContinuousMapSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev C := AddCommGrpCat.{u}

private def fromSection {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology C)
    (U : X.Etale) : F.obj.obj (op U) ≃ F.H' 0 U :=
  (sectionEquiv X.smallEtaleTopology F U).symm.trans Ext.homEquiv₀.symm

private theorem fromSection_restrict {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology C)
    {U V : X.Etale} (f : V ⟶ U) (s : F.obj.obj (op U)) :
    (F.cohomologyPresheaf 0).map f.op (fromSection F U s) =
      fromSection F V (F.obj.map f.op s) := by
  change (Ext.mk₀ ((freeYoneda X.smallEtaleTopology).map f)).comp
    (Ext.mk₀ (sectionHom X.smallEtaleTopology F U s)) rfl =
      Ext.mk₀ (sectionHom X.smallEtaleTopology F V (F.obj.map f.op s))
  rw [Ext.mk₀_comp_mk₀, sectionHom_restrict]

private theorem sections_restrict_surjective {X : Scheme.{u}} (M : C)
    {U V : X.Etale} (f : V ⟶ U) [PreconnectedSpace V.left] [Nonempty V.left] :
    Function.Surjective (((constantSheaf X.smallEtaleTopology C).obj M).obj.map f.op) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  let F := (constantSheaf X.smallEtaleTopology C).obj M
  let G := continuousMapSheaf X M
  let e := (sheafToPresheaf X.smallEtaleTopology C).mapIso (constantSheafContinuousMapIso X M)
  intro y
  let c : ContinuousMap V.left M := e.hom.app (op V) y
  let p : V.left := Classical.choice inferInstance
  let z : G.obj.obj (op U) := ContinuousMap.const U.left (c p)
  have hc : G.obj.map f.op z = c := by
    apply ContinuousMap.ext
    intro q
    change c p = c q
    exact TotallyDisconnectedSpace.eq_of_continuous c c.continuous p q
  refine ⟨e.inv.app (op U) z, ?_⟩
  have h := ConcreteCategory.congr_hom (e.inv.naturality f.op) z
  change e.inv.app (op V) (G.obj.map f.op z) =
    F.obj.map f.op (e.inv.app (op U) z) at h
  rw [hc] at h
  refine h.symm.trans ?_
  exact (e.app (op V)).hom_inv_id_apply y

/-- Native degree-zero restriction to a nonempty preconnected étale object
is surjective for constant coefficients. -/
theorem restriction_surjective {X : Scheme.{u}} (M : C)
    {U V : X.Etale} (f : V ⟶ U) [PreconnectedSpace V.left] [Nonempty V.left] :
    let F := (constantSheaf X.smallEtaleTopology C).obj M
    Function.Surjective ((F.cohomologyPresheaf 0).map f.op) := by
  let F := (constantSheaf X.smallEtaleTopology C).obj M
  intro y
  obtain ⟨s, rfl⟩ := (fromSection F V).surjective y
  obtain ⟨t, ht⟩ := sections_restrict_surjective M f s
  refine ⟨fromSection F U t, ?_⟩
  rw [fromSection_restrict, ht]

end
end ManuscriptAudit.EtaleConstantHZeroRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleConstantHZeroRestriction.restriction_surjective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
