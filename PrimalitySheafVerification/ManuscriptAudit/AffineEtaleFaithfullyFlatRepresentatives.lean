import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AddCommGrpImageFactorization
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleLiftingCover
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleProductGluing
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitCocycle
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-!
# Faithfully flat affine local representatives of degree-one unit cohomology

A section of the cokernel of the injective embedding lifts on a
finite affine étale family. The ring product gives one faithfully flat
étale cover.
-/

namespace ManuscriptAudit.AffineEtaleFaithfullyFlatRepresentatives

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AffineEtaleTensorOverlap KummerUnitsSheaf

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

variable (R : Type) [CommRing R]

private abbrev X := Spec (CommRingCat.of R)
private abbrev J := Scheme.AffineEtale.topology (X R)
private abbrev G := coordinateUnitSheaf (X R)

variable {I : Sheaf (J R) AddCommGrpCat.{0}}

/-- One actual affine faithfully flat étale chart on which a global cokernel
section lifts to the representative sheaf. -/
structure FaithfullyFlatAffineLift (i : G R ⟶ I)
    (x : (cokernel i).obj.obj (op (baseObject R))) where
  coverRing : Type
  [commRing : CommRing coverRing]
  [algebra : Algebra R coverRing]
  [etale : Algebra.Etale R coverRing]
  [faithfullyFlat : Module.FaithfullyFlat R coverRing]
  value : I.obj.obj (op (ofAlgebra R coverRing))
  lifts : (cokernel.π i).hom.app (op (ofAlgebra R coverRing)) value =
    (cokernel i).obj.map (coverArrow R coverRing).op x

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- A section of the cokernel has an actual lift on a single faithfully flat
affine étale chart, obtained by taking the product of finitely many local charts. -/
theorem exists_faithfullyFlatAffineLift (i : G R ⟶ I)
    (x : (cokernel i).obj.obj (op (baseObject R))) :
    Nonempty (FaithfullyFlatAffineLift R i x) := by
  letI : ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization AddCommGrpCat.{0} :=
    AddCommGrpImageFactorization.functorialSurjectiveInjectiveFactorization
  let Q := cokernel i
  let q : I ⟶ Q := cokernel.π i
  let U := baseObject R
  have hT : IsTerminal U :=
    KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)
  apply SheafH1Descent.H1_subsingleton_of_global_lifts i hT
  intro x
  letI : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{0} q).mpr inferInstance
  obtain ⟨n, V, f, hf, hcover⟩ := AffineEtaleLiftingCover.finite_indexed_jointly_surjective_lifts q x
  let A (k : Fin n) : CommRingCat.{0} := (V k).left.unop
  let a (k : Fin n) : CommRingCat.of R ⟶ A k := (f k).left.unop
  letI : ∀ k, Algebra R (A k) := fun k => (a k).hom.toAlgebra
  letI : ∀ k, Algebra.Etale R (A k) := fun k => by
    have he : Etale (Spec.map (a k)) := by
      change Etale ((Scheme.AffineEtale.Spec (X R)).map (f k)).left
      infer_instance
    exact (RingHom.etale_algebraMap).mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp he)
  have hPrime : ∀ z : PrimeSpectrum R, ∃ k, ∃ p : PrimeSpectrum (A k),
      PrimeSpectrum.comap (algebraMap R (A k)) p = z := hcover
  let B := (k : Fin n) → A k
  obtain ⟨hEt, hFaithful⟩ :=
    AffineEtaleCoverProduct.product_affine_etale_faithfullyFlat (fun k : Fin n => (A k : Type)) hPrime
  letI : Algebra.Etale R B := hEt
  letI : Module.FaithfullyFlat R B := hFaithful
  let g : Spec (AffineEtaleProductGluing.productRing A) ⟶ X R :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  letI : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R B))
  let W := AffineEtaleProductGluing.productObject A g
  let v : W ⟶ U := coverArrow R B
  let xW : Q.obj.obj (op W) := Q.obj.map v.op x
  have hComponents (k : Fin n) :
      ∃ y : I.obj.obj (op (AffineEtaleProductGluing.componentObject A g k)),
        q.hom.app (op (AffineEtaleProductGluing.componentObject A g k)) y =
          Q.obj.map (AffineEtaleProductGluing.componentArrow A g k).op xW := by
    let Vc := AffineEtaleProductGluing.componentObject A g k
    let vc : Vc ⟶ W := AffineEtaleProductGluing.componentArrow A g k
    have hComponent : Vc.hom = (V k).hom := by
      change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j => (A j : Type)) k)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) = (V k).hom
      rw [← Spec.map_comp]
      have hm : CommRingCat.ofHom (algebraMap R B) ≫
          CommRingCat.ofHom (Pi.evalRingHom (fun j => (A j : Type)) k) = a k := by
        ext z
        rfl
      rw [hm]
      have hw := (f k).w
      first
      | change Spec.map (a k) ≫ 𝟙 (X R) = (V k).hom at hw
        simpa only [Category.comp_id] using hw
      | change Spec.map (a k) ≫ 𝟙 (X R) = (V k).hom ≫ 𝟙 (X R) at hw
        simpa only [Category.comp_id] using hw
    let e : Vc ≅ V k := MorphismProperty.CostructuredArrow.isoMk
      (Iso.refl (V k).left) trivial trivial (by
        change Scheme.Spec.map (𝟙 ((V k).left)) ≫ (V k).hom = Vc.hom
        rw [CategoryTheory.Functor.map_id, Category.id_comp]
        exact hComponent.symm)
    have hArrow : e.hom ≫ f k = vc ≫ v := hT.hom_ext _ _
    obtain ⟨z, hz⟩ := hf k
    refine ⟨I.obj.map e.hom.op z, ?_⟩
    change q.hom.app (op Vc) (I.obj.map e.hom.op z) = Q.obj.map vc.op (Q.obj.map v.op x)
    calc
      _ = Q.obj.map e.hom.op (q.hom.app (op (V k)) z) := NatTrans.naturality_apply q.hom e.hom.op z
      _ = Q.obj.map e.hom.op (Q.obj.map (f k).op x) := by rw [hz]
      _ = Q.obj.map (e.hom ≫ f k).op x := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      _ = Q.obj.map vc.op (Q.obj.map v.op x) := by
        rw [hArrow, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  obtain ⟨y, hy⟩ := AffineEtaleProductGluing.exists_lift_from_component_lifts A g q xW hComponents
  exact ⟨{
    coverRing := B
    commRing := inferInstance
    algebra := inferInstance
    etale := hEt
    faithfullyFlat := hFaithful
    value := y
    lifts := hy }⟩

/-- Each native first unit cohomology class has a finite faithfully flat
affine representative. -/
theorem exists_faithfullyFlatAffineRepresentative (i : G R ⟶ I) [Mono i] [Injective I]
    (h : Sheaf.H (G R) 1) :
    ∃ x : (cokernel i).obj.obj (op (baseObject R)),
      SheafH1Descent.connectingSection i
        (KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)) x = h ∧
      Nonempty (FaithfullyFlatAffineLift R i x) := by
  obtain ⟨x, hx⟩ := SheafH1Descent.connectingSection_surjective i
    (KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)) h
  exact ⟨x, hx, exists_faithfullyFlatAffineLift R i x⟩


end

end ManuscriptAudit.AffineEtaleFaithfullyFlatRepresentatives

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleFaithfullyFlatRepresentatives.exists_faithfullyFlatAffineLift,
      ``ManuscriptAudit.AffineEtaleFaithfullyFlatRepresentatives.exists_faithfullyFlatAffineRepresentative] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
