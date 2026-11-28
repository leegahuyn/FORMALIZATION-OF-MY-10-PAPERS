import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.ProetaleObjectRestriction

/-! Local lifts on a weakly étale restriction give actual covering sieves. -/

namespace ManuscriptAudit.ProetaleRestrictionLocalLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension (proetalePostcompose postcomposeCoverPreserving)
open ProetaleBaseChange (baseChange)
open ProetaleObjectRestriction (restriction)

noncomputable section
universe u v

variable {Y X : Scheme.{u}} (j : Y ⟶ X) [WeaklyEtale j]

private abbrev A := AddCommGrpCat.{v}
private abbrev C (W : Scheme.{u}) := Sheaf (Scheme.ProEt.topology W) A.{v}

/-- A local restriction lift defines a covering pullback of the original image sieve. -/
theorem covering_on_restriction {U : X.ProEt} {Z : Y.ProEt}
    (p : (proetalePostcompose j).obj Z ⟶ U)
    {F G : C.{u,v} X} (α : F ⟶ G)
    [Sheaf.IsLocallySurjective ((restriction j A.{v}).map α)]
    (s : G.obj.obj (op U)) :
    (Presheaf.imageSieve α.hom s).pullback p ∈
      Scheme.ProEt.topology X ((proetalePostcompose j).obj Z) := by
  let L := proetalePostcompose j
  let s' : ((restriction j A.{v}).obj G).obj.obj (op Z) := G.obj.map p.op s
  let R : Sieve Z := Presheaf.imageSieve ((restriction j A.{v}).map α).hom s'
  have hR : R ∈ Scheme.ProEt.topology Y Z :=
    Presheaf.imageSieve_mem (Scheme.ProEt.topology Y)
      ((restriction j A.{v}).map α).hom (U := op Z) s'
  have hpush := (postcomposeCoverPreserving j).cover_preserve hR
  obtain ⟨ι, V, g, hg⟩ := Sieve.exists_eq_ofArrows R
  rw [hg, Sieve.functorPushforward_ofArrows] at hpush
  refine (Scheme.ProEt.topology X).superset_covering ?_ hpush
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨k⟩
  have hmem : R (g k) := hg.symm ▸ Sieve.ofArrows_mk V g k
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_⟩
  change α.hom.app (op (L.obj (V k))) b = G.obj.map (L.map (g k) ≫ p).op s
  rw [op_comp, G.obj.map_comp, ConcreteCategory.comp_apply]
  exact hb

end
end ManuscriptAudit.ProetaleRestrictionLocalLift
open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleRestrictionLocalLift.covering_on_restriction
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
