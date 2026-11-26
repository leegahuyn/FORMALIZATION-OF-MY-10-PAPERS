import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.RingTheory.Smooth.Flat
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizationHom
import PrimalitySheafVerification.ManuscriptAudit.CuspScheme

/-!
# Map descent for affine étale schemes along cusp normalization

The algebraic hom-set bijection computes the map of the actual over-category
pullback functor. The comparison explicitly uses the projections of the
fiber product and their descriptions on the tensor-product affine chart.
-/

namespace ManuscriptAudit.CuspEtaleHom

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

private abbrev A (K : Type u) [Field K] := CuspPunctured.CuspSubalgebra K
private abbrev B (K : Type u) [Field K] := Polynomial K

private abbrev specAlgebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

set_option backward.isDefEq.respectTransparency false in
private def specOverHomEquiv (R P T : Type u) [CommRing R] [CommRing P] [CommRing T]
    [Algebra R P] [Algebra R T] :
    (P →ₐ[R] T) ≃
      (Over.mk (specAlgebraMap R T) ⟶ Over.mk (specAlgebraMap R P)) where
  toFun f :=
    Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specAlgebraMap R P =
        specAlgebraMap R T
      simp only [specAlgebraMap, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      exact f.commutes)
  invFun g :=
    { (Spec.preimage g.left).hom with
      commutes' := fun r => by
        have h : CommRingCat.ofHom (algebraMap R P) ≫ Spec.preimage g.left =
            CommRingCat.ofHom (algebraMap R T) := by
          have hg : g.left ≫ specAlgebraMap R P = specAlgebraMap R T := Over.w g
          simpa only [specAlgebraMap, Spec.preimage_comp, Spec.preimage_map] using
            congrArg Spec.preimage hg
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r }
  left_inv f := by
    apply AlgHom.ext
    intro x
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom x = f x
    rw [Spec.preimage_map]
    rfl
  right_inv g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Spec.preimage g.left).hom) = g.left
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]

variable (K : Type u) [Field K]

private def chart (P : Type u) [CommRing P] [Algebra (A K) P] :
    pullback (specAlgebraMap (A K) P) (CuspScheme.cuspMap K) ≅
      Spec (CommRingCat.of (B K ⊗[A K] P)) := by
  change pullback (specAlgebraMap (A K) P) (specAlgebraMap (A K) (B K)) ≅
    Spec (CommRingCat.of (B K ⊗[A K] P))
  exact pullbackSymmetry (specAlgebraMap (A K) P) (specAlgebraMap (A K) (B K)) ≪≫
    pullbackSpecIso (A K) (B K) P

private abbrev specRight (P : Type u) [CommRing P] [Algebra (A K) P] :
    Spec (CommRingCat.of (B K ⊗[A K] P)) ⟶ Spec (CommRingCat.of P) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : P →ₐ[A K] B K ⊗[A K] P).toRingHom)

@[reassoc (attr := simp)]
private theorem chart_hom_fst (P : Type u) [CommRing P] [Algebra (A K) P] :
    (chart K P).hom ≫ specRight K P =
      pullback.fst (specAlgebraMap (A K) P) (CuspScheme.cuspMap K) := by
  simp [chart, specAlgebraMap, specRight, CuspScheme.cuspMap, CuspScheme.inclusion, Category.assoc]

@[reassoc (attr := simp)]
private theorem chart_hom_snd (P : Type u) [CommRing P] [Algebra (A K) P] :
    (chart K P).hom ≫ specAlgebraMap (B K) (B K ⊗[A K] P) =
      pullback.snd (specAlgebraMap (A K) P) (CuspScheme.cuspMap K) := by
  simp [chart, specAlgebraMap, specRight, CuspScheme.cuspMap, CuspScheme.inclusion, Category.assoc]

@[reassoc (attr := simp)]
private theorem chart_inv_fst (P : Type u) [CommRing P] [Algebra (A K) P] :
    (chart K P).inv ≫ pullback.fst (specAlgebraMap (A K) P) (CuspScheme.cuspMap K) =
      specRight K P := by
  rw [← chart_hom_fst K P, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
private theorem chart_inv_snd (P : Type u) [CommRing P] [Algebra (A K) P] :
    (chart K P).inv ≫ pullback.snd (specAlgebraMap (A K) P) (CuspScheme.cuspMap K) =
      specAlgebraMap (B K) (B K ⊗[A K] P) := by
  rw [← chart_hom_snd K P, Iso.inv_hom_id_assoc]

private def overChart (P : Type u) [CommRing P] [Algebra (A K) P] :
    (Over.pullback (CuspScheme.cuspMap K)).obj (Over.mk (specAlgebraMap (A K) P)) ≅
      Over.mk (specAlgebraMap (B K) (B K ⊗[A K] P)) :=
  Over.isoMk (chart K P) (chart_hom_snd K P)

variable {P T : Type u} [CommRing P] [CommRing T] [Algebra (A K) P] [Algebra (A K) T]

set_option backward.isDefEq.respectTransparency false in
private theorem map_comp_overChart (f : P →ₐ[A K] T) :
    (Over.pullback (CuspScheme.cuspMap K)).map (specOverHomEquiv (A K) P T f) ≫
        (overChart K P).hom =
      (overChart K T).hom ≫
        specOverHomEquiv (B K) (B K ⊗[A K] P) (B K ⊗[A K] T)
          (Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f) := by
  let m := specOverHomEquiv (A K) P T f
  let F := Over.pullback (CuspScheme.cuspMap K)
  let fB := Algebra.TensorProduct.map (AlgHom.id (B K) (B K)) f
  let n := specOverHomEquiv (B K) (B K ⊗[A K] P) (B K ⊗[A K] T) fB
  have hn : n.left ≫ specRight K P = specRight K T ≫ m.left := by
    change Spec.map (CommRingCat.ofHom fB.toRingHom) ≫ specRight K P =
      specRight K T ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    simp only [specRight, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change fB ((1 : B K) ⊗ₜ[A K] x) = (1 : B K) ⊗ₜ[A K] f x
    simp [fB]
  have hbase : n.left ≫ specAlgebraMap (B K) (B K ⊗[A K] P) =
      specAlgebraMap (B K) (B K ⊗[A K] T) := Over.w n
  apply Over.OverMorphism.ext
  change (F.map m).left ≫ (chart K P).hom = (chart K T).hom ≫ n.left
  apply (cancel_mono (chart K P).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, chart_inv_fst, hn, chart_hom_fst_assoc,
      F, Over.pullback_map_left, pullback.lift_fst]
  · simp only [Category.assoc, chart_inv_snd, hbase, chart_hom_snd,
      F, Over.pullback_map_left, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pullback functor has bijective map on homs for affine charts
whose source algebra is flat and whose target algebra is formally unramified. -/
theorem overPullback_map_bijective_of_algebras [Algebra.FormallyUnramified (A K) P]
    [Module.Flat (A K) T] :
    Function.Bijective ((Over.pullback (CuspScheme.cuspMap K)).map :
      (Over.mk (specAlgebraMap (A K) T) ⟶ Over.mk (specAlgebraMap (A K) P)) → _) := by
  let eL := specOverHomEquiv (A K) P T
  let eR := specOverHomEquiv (B K) (B K ⊗[A K] P) (B K ⊗[A K] T)
  let eC :
      (Over.mk (specAlgebraMap (B K) (B K ⊗[A K] T)) ⟶
        Over.mk (specAlgebraMap (B K) (B K ⊗[A K] P))) ≃
      ((Over.pullback (CuspScheme.cuspMap K)).obj (Over.mk (specAlgebraMap (A K) T)) ⟶
        (Over.pullback (CuspScheme.cuspMap K)).obj (Over.mk (specAlgebraMap (A K) P))) :=
    { toFun := fun g => (overChart K T).hom ≫ g ≫ (overChart K P).inv
      invFun := fun g => (overChart K T).inv ≫ g ≫ (overChart K P).hom
      left_inv := by intro g; simp
      right_inv := by intro g; simp }
  let e := eL.symm.trans ((CuspNormalizationHom.homEquiv K P T).trans (eR.trans eC))
  have he :
      (e : _ → _) = (Over.pullback (CuspScheme.cuspMap K)).map := by
    funext m
    obtain ⟨f, rfl⟩ := eL.surjective m
    change eC (eR (CuspNormalizationHom.homEquiv K P T (eL.symm (eL f)))) =
      (Over.pullback (CuspScheme.cuspMap K)).map (eL f)
    rw [Equiv.symm_apply_apply, CuspNormalizationHom.homEquiv_apply]
    have h := congrArg (fun g => g ≫ (overChart K P).inv) (map_comp_overChart K f).symm
    simpa only [eC, eR, eL, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  rw [← he]
  exact e.bijective

set_option backward.isDefEq.respectTransparency false in
/-- Cusp normalization pullback is bijective on morphisms between any two actual
affine étale schemes over the cusp. -/
theorem overPullback_map_bijective (T P : CommRingCat.{u})
    (f : Spec T ⟶ Spec (CommRingCat.of (A K))) (g : Spec P ⟶ Spec (CommRingCat.of (A K)))
    [Etale f] [Etale g] :
    Function.Bijective ((Over.pullback (CuspScheme.cuspMap K)).map :
      (Over.mk f ⟶ Over.mk g) → _) := by
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  letI : Algebra (A K) T := f'.hom.toAlgebra
  letI : Algebra (A K) P := g'.hom.toAlgebra
  letI : Algebra.Etale (A K) T := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := f')).mp ‹Etale (Spec.map f')›)
  letI : Algebra.Etale (A K) P := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := g')).mp ‹Etale (Spec.map g')›)
  have hf : specAlgebraMap (A K) T = Spec.map f' :=
    congrArg Spec.map (CommRingCat.ofHom_hom f')
  have hg : specAlgebraMap (A K) P = Spec.map g' :=
    congrArg Spec.map (CommRingCat.ofHom_hom g')
  simpa only [hf, hg] using
    (overPullback_map_bijective_of_algebras K (P := P) (T := T))

end

end ManuscriptAudit.CuspEtaleHom

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspEtaleHom.overPullback_map_bijective_of_algebras,
      ``ManuscriptAudit.CuspEtaleHom.overPullback_map_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
