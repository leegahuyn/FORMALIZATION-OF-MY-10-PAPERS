import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineProetaleChartTransport
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawSingletonSeparated
import PrimalitySheafVerification.ManuscriptAudit.ProetaleRawAffineSingletonComparison

/-! Actual chart coordinates transfer raw separatedness to every
affine singleton cover of the native pro-étale site. -/

namespace ManuscriptAudit.NativeAffineRawSingletonSeparationTransport

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor (spectrum structureMap specMap)
open NativeAffineProetaleChartTransport (coordinateRing chartIso chartAlgebraMap chartIso_natural)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeAffineEtaleKanComparison (raw)
open AffineEtaleStageColimit (FiniteTupleApproximation)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]
  (I : Sheaf (spectrum A).smallEtaleTopology AddCommGrpCat.{u + 1})

private abbrev P := raw (spectrum A) I

private theorem map_map {U V W : (spectrum A).ProEt} (f : U ⟶ V) (g : V ⟶ W)
    (x : (P I).obj (op W)) :
    (P I).map f.op ((P I).map g.op x) = (P I).map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Surjectivity of the actual arrow is preserved by both affine chart isomorphisms. -/
theorem chart_algebra_surjective {V W : (spectrum A).ProEt} [IsAffine V.left] [IsAffine W.left]
    (f : V ⟶ W) (hf : Function.Surjective f.left) :
    Function.Surjective (specMap A (chartAlgebraMap f)) := by
  let e := chartIso V
  let j := chartIso W
  let k := chartAlgebraMap f
  have he : e.inv.left ≫ e.hom.left = 𝟙 V.left :=
    congrArg (fun x : V ⟶ V ↦ x.left) e.inv_hom_id
  have hh : specMap A k ≫ j.hom.left = e.hom.left ≫ f.left :=
    congrArg (fun x : ProetaleAffineTensor.object A (coordinateRing V) ⟶ W ↦ x.left) (chartIso_natural f)
  intro z
  obtain ⟨w, hw⟩ := hf (j.hom.left z)
  refine ⟨e.inv.left w, ?_⟩
  have h : j.hom.left (specMap A k (e.inv.left w)) = j.hom.left z := by
    have h₁ : j.hom.left (specMap A k (e.inv.left w)) =
        f.left (e.hom.left (e.inv.left w)) :=
      congrArg (fun t : (ProetaleAffineTensor.object A (coordinateRing V)).left ⟶ W.left ↦
        t (e.inv.left w)) hh
    have h₂ : e.hom.left (e.inv.left w) = w :=
      congrArg (fun t : V.left ⟶ V.left ↦ t w) he
    exact h₁.trans ((congrArg f.left h₂).trans hw)
  have hInv (x : (ProetaleAffineTensor.object A (coordinateRing W)).left) :
      j.inv.left (j.hom.left x) = x := by
    have h' : j.hom.left ≫ j.inv.left =
        𝟙 (ProetaleAffineTensor.object A (coordinateRing W)).left :=
      congrArg (fun x ↦ x.left) j.hom_inv_id
    exact congrArg (fun t : (ProetaleAffineTensor.object A (coordinateRing W)).left ⟶
      (ProetaleAffineTensor.object A (coordinateRing W)).left ↦ t x) h'
  exact (hInv _).symm.trans ((congrArg j.inv.left h).trans (hInv _))

set_option maxHeartbeats 4800000 in
/-- The actual raw presheaf is separated on every actual affine
singleton cover when all affine charts have finite étale approximation. -/
theorem affineSingletonSeparated
    (hApprox : ∀ (B : Type u) [CommRing B] [Algebra A B],
      WeaklyEtale (structureMap A B) → FiniteTupleApproximation A B) :
    ProetaleRawAffineSingletonComparison.AffineSingletonSeparated (P I) := by
  intro V W f hV hW _ hf x y hxy
  letI := hV
  letI := hW
  let e := chartIso V
  let j := chartIso W
  let k := chartAlgebraMap f
  have h : (P I).map (chartMap k).op ((P I).map j.hom.op x) =
      (P I).map (chartMap k).op ((P I).map j.hom.op y) := by
    rw [map_map, map_map, chartIso_natural f, ← map_map, ← map_map, hxy]
  have he := NativeAffineEtaleRawSingletonSeparated.restrict_injective I
    (hApprox (coordinateRing W) inferInstance) k (chart_algebra_surjective f hf.surj) h
  have hi (z : (P I).obj (op W)) :
      (P I).map j.inv.op ((P I).map j.hom.op z) = z := by
    rw [map_map, j.inv_hom_id]
    simp
  exact (hi x).symm.trans ((congrArg ((P I).map j.inv.op) he).trans (hi y))

end
end ManuscriptAudit.NativeAffineRawSingletonSeparationTransport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawSingletonSeparationTransport.affineSingletonSeparated
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
