import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOneToPicard

/-! The genuine affine H¹ comparison with the Picard group is independent
of the choice of injective sheaf used to represent its classes. -/

namespace ManuscriptAudit.AffineEtalePicardEmbeddingIndependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TensorProduct
open AffineEtaleTensorOverlap AffineEtaleFaithfullyFlatRepresentatives AffineEtaleHOneToPicard
open AffineEtalePicardClass AffineEtaleUnitCocycle AffineEtalePicardSameCover
open KummerUnitsSheaf SheafH1Descent SheafSectionDifference
open TwistedTensorEqualizer FaithfullyFlatCocyclePicard

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt doubleEtale

variable (A : Type) [CommRing A]

private abbrev X := Spec (CommRingCat.of A)
private abbrev J₀ := Scheme.AffineEtale.topology (X A)
private abbrev C := Sheaf (J₀ A) AddCommGrpCat.{0}
private abbrev G := coordinateUnitSheaf (X A)
private abbrev Z := (constantSheaf (J₀ A) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift.{0} ℤ))
private abbrev terminal := KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of A)

private abbrev seq {F I : C A} (i : F ⟶ I) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

private theorem short_exact {F I : C A} (i : F ⟶ I) [Mono i] : (seq A i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

variable {I J : C A} (i : G A ⟶ I) (k : G A ⟶ J) [Mono i] [Mono k]

private def compareCokernels (f : I ⟶ J) (hf : i ≫ f = k) : cokernel i ⟶ cokernel k :=
  cokernel.map i k (𝟙 _) f (by simpa only [Category.id_comp] using hf)

private theorem compare_cokernel_π (f : I ⟶ J) (hf : i ≫ f = k) :
    cokernel.π i ≫ compareCokernels A i k f hf = f ≫ cokernel.π k := by
  simp [compareCokernels]

private theorem connecting_compare (f : I ⟶ J) (hf : i ≫ f = k)
    (x : (cokernel i).obj.obj (op (baseObject A))) :
    connectingSection k (terminal A) ((compareCokernels A i k f hf).hom.app (op (baseObject A)) x) =
      connectingSection i (terminal A) x := by
  let q := compareCokernels A i k f hf
  let comparison : seq A i ⟶ seq A k :=
    { τ₁ := 𝟙 _, τ₂ := f, τ₃ := q
      comm₁₂ := by simpa only [Category.id_comp] using hf.symm
      comm₂₃ := (compare_cokernel_π A i k f hf).symm }
  have h := (short_exact A i).extClass_naturality (short_exact A k) comparison
  change (short_exact A i).extClass.comp (Ext.mk₀ (𝟙 (G A))) (add_zero 1) =
    (Ext.mk₀ q).comp (short_exact A k).extClass (zero_add 1) at h
  have he : (short_exact A i).extClass =
      (Ext.mk₀ q).comp (short_exact A k).extClass (zero_add 1) := by
    simpa only [Ext.comp_mk₀_id] using h
  unfold connectingSection
  change ((Sheaf.H.equiv₀ (cokernel k) (terminal A)).symm
      (q.hom.app (op (baseObject A)) x)).comp _ (zero_add 1) =
    ((Sheaf.H.equiv₀ (cokernel i) (terminal A)).symm x).comp _ (zero_add 1)
  rw [← Sheaf.H.equiv₀_symm_naturality, Sheaf.H.map_apply, he]
  exact Ext.comp_assoc_of_second_deg_zero _ _ _ _


private theorem class_congr (B : Type) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {t s : (Double A B)ˣ} (ht : IsCocycle A B t) (hs : IsCocycle A B s) (h : t = s) :
    picardClass A B t ht = picardClass A B s hs := by
  subst s
  rfl

/-- Every pair of genuine injective embeddings gives the same native
Picard class for each actual first étale unit cohomology class. -/
theorem toPicard_independent [Injective I] [Injective J] (h : Sheaf.H (G A) 1) :
    toPicard A i h = toPicard A k h := by
  let f := Injective.factorThru k i
  have hf := Injective.comp_factorThru k i
  let q := compareCokernels A i k f hf
  obtain ⟨x, hx, ⟨c⟩⟩ := exists_faithfullyFlatAffineRepresentative A i h
  let B := c.coverRing
  letI : CommRing B := c.commRing
  letI : Algebra A B := c.algebra
  letI : Algebra.Etale A B := c.etale
  letI : Module.FaithfullyFlat A B := c.faithfullyFlat
  let y := c.value
  let x' := q.hom.app (op (baseObject A)) x
  let y' := f.hom.app (op (ofAlgebra A B)) y
  have hy' : (cokernel.π k).hom.app (op (ofAlgebra A B)) y' =
      (cokernel k).obj.map (coverArrow A B).op x' := by
    have he := compare_cokernel_π A i k f hf
    have e := congrArg (fun s : I ⟶ cokernel k => s.hom.app (op (ofAlgebra A B)) y) he
    change _ = (cokernel.π k).hom.app _ y' at e
    rw [← e]
    change q.hom.app (op (ofAlgebra A B)) ((cokernel.π i).hom.app (op (ofAlgebra A B)) y) = _
    rw [c.lifts]
    exact NatTrans.naturality_apply q.hom (coverArrow A B).op x
  let c' : FaithfullyFlatAffineLift A k x' :=
    { coverRing := B, commRing := inferInstance, algebra := inferInstance, etale := inferInstance,
      faithfullyFlat := inferInstance, value := y', lifts := hy' }
  have hx' : connectingSection k (terminal A) x' = h :=
    (connecting_compare A i k f hf x).trans hx
  rw [toPicard_of_representative A i h c hx, toPicard_of_representative A k h c' hx']
  change picardClassOfLift A B i x y c.lifts = picardClassOfLift A B k x' y' hy'
  have ht : transition A B i x y c.lifts = transition A B k x' y' hy' := by
    apply (Additive.ofMul (α := (B ⊗[A] B)ˣ)).injective
    let D := ofAlgebra A (B ⊗[A] B)
    apply section_injective k D
    have he := congrArg (fun g : G A ⟶ J =>
      g.hom.app (op D) (Additive.ofMul (transition A B i x y c.lifts))) hf
    change f.hom.app (op D) (i.hom.app (op D) _) = k.hom.app (op D) _ at he
    rw [← he, transition_image, transition_image]
    change (f.hom.app (op D)).hom (_ - _) = _
    rw [map_sub]
    change f.hom.app (op D) (I.obj.map (firstProjection A B).op y) -
      f.hom.app (op D) (I.obj.map (secondProjection A B).op y) = _
    rw [NatTrans.naturality_apply f.hom (firstProjection A B).op y,
      NatTrans.naturality_apply f.hom (secondProjection A B).op y]
  unfold picardClassOfLift
  apply class_congr A B
  exact ht

end

end ManuscriptAudit.AffineEtalePicardEmbeddingIndependence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtalePicardEmbeddingIndependence.toPicard_independent
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
