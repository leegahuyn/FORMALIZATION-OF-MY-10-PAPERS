import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleLiftingCover
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleProductGluing
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover

/-!
# One affine étale cover carrying a local lift

A finite local lifting family can be combined into a single affine
étale cover, using the product of its rings and gluing sections over
the disjoint open components. This works over any affine étale object.
-/

namespace ManuscriptAudit.AffineEtaleSingletonLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {X : Scheme.{u}} {U : X.AffineEtale}

private abbrev underlying (X : Scheme.{u}) : X.AffineEtale ⥤ Scheme.{u} :=
  Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X ⋙ Over.forget X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3400000 in
/-- Locally liftable sections lift on one actual affine étale cover. -/
theorem exists_singleton_cover_lift
    {P Q : Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}}
    (q : P ⟶ Q) [Sheaf.IsLocallySurjective q] (x : Q.obj.obj (op U)) :
    ∃ (W : X.AffineEtale) (v : W ⟶ U),
      Sieve.generate (Presieve.singleton v) ∈ Scheme.AffineEtale.topology X U ∧
      ∃ y : P.obj.obj (op W), q.hom.app (op W) y = Q.obj.map v.op x := by
  classical
  obtain ⟨n, V, f, hf, hcover⟩ :=
    AffineEtaleLiftingCover.finite_indexed_jointly_surjective_lifts q x
  let A := U.left.unop
  let B (k : Fin n) : CommRingCat.{u} := (V k).left.unop
  let a (k : Fin n) : A ⟶ B k := (f k).left.unop
  letI : ∀ k, Algebra (A : Type u) (B k : Type u) := fun k ↦ (a k).hom.toAlgebra
  letI : ∀ k, Algebra.Etale (A : Type u) (B k : Type u) := fun k ↦ by
    have hEt : Etale (Spec.map (a k)) := by
      change Etale ((Scheme.AffineEtale.Spec X).map (f k)).left
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hEt)
  have hPrime : ∀ z : PrimeSpectrum A, ∃ k, ∃ p : PrimeSpectrum (B k),
      PrimeSpectrum.comap (algebraMap A (B k)) p = z := hcover
  let C := (k : Fin n) → B k
  obtain ⟨hEt, hFaithful⟩ :=
    AffineEtaleCoverProduct.product_affine_etale_faithfullyFlat (fun k : Fin n ↦ (B k : Type u)) hPrime
  letI : Algebra.Etale A C := hEt
  letI : Module.FaithfullyFlat A C := hFaithful
  let aPi : A ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap A C)
  let g : Spec (AffineEtaleProductGluing.productRing B) ⟶ X := Spec.map aPi ≫ U.hom
  letI : Etale (Spec.map aPi) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A C))
  letI : Etale U.hom := U.prop
  letI : Etale g := by change Etale (Spec.map aPi ≫ U.hom); infer_instance
  let W := AffineEtaleProductGluing.productObject B g
  let v : W ⟶ U := MorphismProperty.CostructuredArrow.homMk aPi.op trivial rfl
  have hCov : Sieve.generate (Presieve.singleton v) ∈ Scheme.AffineEtale.topology X U := by
    rw [← Presieve.ofArrows_of_unique (fun _ : Unit ↦ v)]
    change Sieve.ofArrows (fun _ : Unit ↦ W) (fun _ : Unit ↦ v) ∈ _
    rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense,
      Sieve.functorPushforward_ofArrows]
    apply KummerSiteCover.singleton_mem_smallEtaleTopology
    change Function.Surjective (PrimeSpectrum.comap (algebraMap A C))
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  let xW := Q.obj.map v.op x
  have hComponents (k : Fin n) :
      ∃ y : P.obj.obj (op (AffineEtaleProductGluing.componentObject B g k)),
        q.hom.app (op (AffineEtaleProductGluing.componentObject B g k)) y =
          Q.obj.map (AffineEtaleProductGluing.componentArrow B g k).op xW := by
    let Vc := AffineEtaleProductGluing.componentObject B g k
    let vc : Vc ⟶ W := AffineEtaleProductGluing.componentArrow B g k
    let ev : AffineEtaleProductGluing.productRing B ⟶ B k :=
      CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ (B j : Type u)) k)
    have hm : aPi ≫ ev = a k := by
      apply CommRingCat.hom_ext
      exact RingHom.ext fun _ ↦ rfl
    have hComponent : Vc.hom = (V k).hom := by
      change Spec.map ev ≫ Spec.map aPi ≫ U.hom = (V k).hom
      rw [← Category.assoc, ← Spec.map_comp, hm]
      exact (f k).w
    let e : Vc ≅ V k := MorphismProperty.CostructuredArrow.isoMk
      (Iso.refl (V k).left) trivial trivial (by
        change Scheme.Spec.map (𝟙 ((V k).left)) ≫ (V k).hom = Vc.hom
        rw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact hComponent.symm)
    have hArrow : e.hom ≫ f k = vc ≫ v := by
      apply (underlying X).map_injective
      change Spec.map (𝟙 (B k)) ≫ Spec.map (a k) = Spec.map ev ≫ Spec.map aPi
      rw [Spec.map_id, Category.id_comp, ← Spec.map_comp, hm]
    obtain ⟨z, hz⟩ := hf k
    refine ⟨P.obj.map e.hom.op z, ?_⟩
    change q.hom.app (op Vc) (P.obj.map e.hom.op z) = Q.obj.map vc.op (Q.obj.map v.op x)
    calc
      _ = Q.obj.map e.hom.op (q.hom.app (op (V k)) z) :=
        NatTrans.naturality_apply q.hom e.hom.op z
      _ = Q.obj.map e.hom.op (Q.obj.map (f k).op x) := by rw [hz]
      _ = Q.obj.map (e.hom ≫ f k).op x := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      _ = Q.obj.map vc.op (Q.obj.map v.op x) := by
        rw [hArrow, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  obtain ⟨y, hy⟩ := AffineEtaleProductGluing.exists_lift_from_component_lifts B g q xW hComponents
  exact ⟨W, v, hCov, y, hy⟩

end

end ManuscriptAudit.AffineEtaleSingletonLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleSingletonLift.exists_singleton_cover_lift
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
