import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawSingletonGluing
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawSingletonSeparationTransport

/-! The coordinate comparison transports actual raw singleton
gluing to every native affine covering arrow. -/

namespace ManuscriptAudit.NativeAffineRawSingletonGluingTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap specMap)
open NativeAffineProetaleChartTransport (coordinateRing chartIso chartAlgebraMap chartIso_natural)
open NativeAffineRawSingletonSeparationTransport (chart_algebra_surjective)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeAffineEtaleKanComparison (raw)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Sheaf (spectrum A).smallEtaleTopology AddCommGrpCat.{u + 1})

private abbrev P := raw (spectrum A) I

private theorem map_map {U V W : (spectrum A).ProEt} (f : U ⟶ V) (g : V ⟶ W)
    (x : (P I).obj (op W)) :
    (P I).map f.op ((P I).map g.op x) = (P I).map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

set_option maxHeartbeats 11000000 in
/-- Actual affine weakly étale singleton gluing for the native raw
presheaf follows from finite approximation of each coordinate chart. -/
theorem affineSingletonGluing
    (hApprox : ∀ (B : Type u) [CommRing B] [Algebra A B],
      WeaklyEtale (structureMap A B) → FiniteTupleApproximation A B) :
    ProetaleRawAffineSingletonComparison.AffineSingletonGluing (P I) := by
  intro V W f hV hW hf hSurj x hx
  letI := hV
  letI := hW
  let B := coordinateRing W
  let D := coordinateRing V
  let k : B →ₐ[A] D := chartAlgebraMap f
  letI : Algebra B D := k.toRingHom.toAlgebra
  letI : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq (fun a ↦ (k.commutes a).symm)
  let e := chartIso V
  let j := chartIso W
  let g := chartMap k
  have hNat : g ≫ j.hom = e.hom ≫ f := chartIso_natural f
  have he : g.left = e.hom.left ≫ f.left ≫ j.inv.left := by
    have h : g = e.hom ≫ f ≫ j.inv := by
      apply (cancel_mono j.hom).mp
      rw [hNat]
      simp [Category.assoc]
    exact congrArg (fun p ↦ p.left) h
  letI : WeaklyEtale f.left := hf
  letI : WeaklyEtale (structureMap B D) := by
    change WeaklyEtale g.left
    rw [he]
    let S := Scheme.ProEt.forget (spectrum A) ⋙ Over.forget _
    letI : IsIso e.hom.left := inferInstanceAs (IsIso (S.map e.hom))
    letI : IsIso j.inv.left := inferInstanceAs (IsIso (S.map j.inv))
    infer_instance
  have hs : pullback.fst g g ≫ e.hom ≫ f = pullback.snd g g ≫ e.hom ≫ f := by
    rw [← hNat, ← Category.assoc, ← Category.assoc, pullback.condition]
  let t := pullback.lift (pullback.fst g g ≫ e.hom) (pullback.snd g g ≫ e.hom)
    (by simpa only [Category.assoc] using hs)
  have ht₁ : t ≫ pullback.fst f f = pullback.fst g g ≫ e.hom := pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd f f = pullback.snd g g ≫ e.hom := pullback.lift_snd _ _ _
  let y := (P I).map e.hom.op x
  have hy : (P I).map (pullback.fst g g).op y = (P I).map (pullback.snd g g).op y := by
    rw [show y = (P I).map e.hom.op x from rfl, map_map, map_map,
      ← ht₁, ← ht₂, ← map_map, ← map_map, hx]
  obtain ⟨pre, hpre⟩ := NativeAffineRawSingletonGluing.exists_glue I
    (hApprox B inferInstance) (hApprox D inferInstance) (chart_algebra_surjective f hSurj) y hy
  let r := (P I).map j.inv.op pre
  have hr : (P I).map j.hom.op r = pre := by
    rw [show r = (P I).map j.inv.op pre from rfl, map_map, j.hom_inv_id]
    simp
  have h : (P I).map e.hom.op ((P I).map f.op r) = (P I).map e.hom.op x := by
    rw [map_map, ← hNat, ← map_map, hr]
    exact hpre
  have hz (z : (P I).obj (op V)) : (P I).map e.inv.op ((P I).map e.hom.op z) = z := by
    rw [map_map, e.inv_hom_id]
    simp
  exact ⟨r, (hz _).symm.trans ((congrArg ((P I).map e.inv.op) h).trans (hz _))⟩

end
end ManuscriptAudit.NativeAffineRawSingletonGluingTransport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawSingletonGluingTransport.affineSingletonGluing
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
