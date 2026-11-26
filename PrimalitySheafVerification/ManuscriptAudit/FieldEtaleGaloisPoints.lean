import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.Field

/-! Nonempty affine étale objects over a field admit finite Galois points. -/

namespace ManuscriptAudit.FieldEtaleGaloisPoints

open CategoryTheory AlgebraicGeometry
open IntermediateField

noncomputable section

theorem exists_finiteGalois_extension (K E : Type) [Field K] [Field E]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (_ : IsGalois K L), Nonempty (E →ₐ[K] L) := by
  let f : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  letI : Algebra E (SeparableClosure K) := f.toAlgebra
  letI : IsScalarTower K E (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let L := normalClosure K E (SeparableClosure K)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(normalClosure.algHomEquiv K E (SeparableClosure K)).symm f⟩⟩

theorem exists_finiteGalois_point (K B : Type) [Field K] [CommRing B] [Nontrivial B]
    [Algebra K B] [Algebra.Etale K B] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (_ : IsGalois K L), Nonempty (B →ₐ[K] L) := by
  obtain ⟨I, _, E, hE, hAlg, e, hExt⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := B)).mp inferInstance
  letI : ∀ i, Field (E i) := hE
  letI : ∀ i, Algebra K (E i) := hAlg
  have hI : Nonempty I := by
    by_contra hn
    letI : IsEmpty I := not_nonempty_iff.mp hn
    have hz : e (0 : B) = e 1 := by
      funext i
      exact isEmptyElim i
    exact zero_ne_one (e.injective hz)
  let i := Classical.choice hI
  letI : Module.Finite K (E i) := (hExt i).1
  letI : Algebra.IsSeparable K (E i) := (hExt i).2
  obtain ⟨L, _, _, _, _, ⟨f⟩⟩ := exists_finiteGalois_extension K (E i)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨f.comp ((Pi.evalAlgHom K E i).comp e.toAlgHom)⟩⟩

theorem finiteGalois_spec_map_etale (K L : Type) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  letI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  letI : Algebra.Etale K L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)

theorem exists_finiteGalois_spec_factor (K : Type) [Field K] (B : CommRingCat.{0})
    [Nontrivial B] (f : CommRingCat.of K ⟶ B) [Etale (Spec.map f)] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (_ : IsGalois K L) (g : Spec (CommRingCat.of L) ⟶ Spec B),
        g ≫ Spec.map f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  algebraize [f.hom]
  letI : Algebra.Etale K B := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (show Etale (Spec.map f) from inferInstance))
  obtain ⟨L, _, _, _, _, ⟨b⟩⟩ := exists_finiteGalois_point K B
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom b.toRingHom), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun x => b.commutes x

end
end ManuscriptAudit.FieldEtaleGaloisPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FieldEtaleGaloisPoints.exists_finiteGalois_extension,
      ``ManuscriptAudit.FieldEtaleGaloisPoints.exists_finiteGalois_point,
      ``ManuscriptAudit.FieldEtaleGaloisPoints.finiteGalois_spec_map_etale,
      ``ManuscriptAudit.FieldEtaleGaloisPoints.exists_finiteGalois_spec_factor] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
