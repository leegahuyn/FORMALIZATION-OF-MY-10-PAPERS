import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import PrimalitySheafVerification.ManuscriptAudit.EtaleLocusOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.PrincipalDivisibilityLocus

/-! An affine open of the actual étale locus carries all rational
expressions whose denominators divide the numerators on its stalks. -/

namespace ManuscriptAudit.AffineOpenStageSections

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor (structureMap specMap)
open PrincipalDivisibilityLocus
  (divisibilityOpen mem_divisibilityOpen_iff dvd_of_forall_atPrime map_dvd_atPrime)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] [Algebra.FinitePresentation A D]

set_option maxHeartbeats 3300000 in
/-- For an actual affine open containing the chart image, a family of
regular fractions becomes a family of global sections of its étale ring. -/
theorem exists_stage (g : D →ₐ[A] B) (U : (ProetaleAffineTensor.spectrum D).Opens) (hAff : IsAffineOpen U)
    (hImage : Set.range (specMap A g) ⊆ Set.range U.ι)
    (hEt : (U : Set (ProetaleAffineTensor.spectrum D)) ⊆ Algebra.etaleLocus A D)
    {ι : Type u} (a : ι → A) (d : ι → D) (z : ι → B)
    (hDiv : ∀ i, (U : Set (ProetaleAffineTensor.spectrum D)) ⊆
      (divisibilityOpen (algebraMap A D (a i)) (d i) : Set (PrimeSpectrum D)))
    (hReg : ∀ i, IsLeftRegular (algebraMap A B (a i)))
    (hEq : ∀ i, g (d i) = algebraMap A B (a i) * z i) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.Etale A C ∧ ∃ k : C →ₐ[A] B, ∀ i, ∃ w : C, k w = z i := by
  letI : IsAffine U.toScheme := hAff
  let C : CommRingCat.{u} := Scheme.Γ.obj (op U.toScheme)
  let e : U.toScheme ≅ Spec C := U.toScheme.isoSpec
  let v : Spec C ⟶ ProetaleAffineTensor.spectrum D := e.inv ≫ U.ι
  let w : ProetaleAffineTensor.spectrum B ⟶ U.toScheme := IsOpenImmersion.lift U.ι (specMap A g) hImage
  let u : ProetaleAffineTensor.spectrum B ⟶ Spec C := w ≫ e.hom
  let φ : CommRingCat.of D ⟶ C := Spec.preimage v
  let ψ : C ⟶ CommRingCat.of B := Spec.preimage u
  letI : Algebra D C := φ.hom.toAlgebra
  letI : Algebra A C := Algebra.compHom C (algebraMap A D)
  letI : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq' rfl
  have hφ : Spec.map φ = v := Spec.map_preimage v
  have hψ : Spec.map ψ = u := Spec.map_preimage u
  have hφψ : φ ≫ ψ = CommRingCat.ofHom g.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ]
    change (w ≫ e.hom) ≫ e.inv ≫ U.ι = specMap A g
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.lift_fac U.ι (specMap A g) hImage
  have hK (x : D) : ψ.hom (algebraMap D C x) = g x :=
    RingHom.congr_fun (congrArg (fun m : CommRingCat.of D ⟶ CommRingCat.of B ↦ m.hom) hφψ) x
  let k : C →ₐ[A] B :=
    { toRingHom := ψ.hom
      commutes' := fun x ↦ by
        rw [IsScalarTower.algebraMap_apply A D C]
        exact (hK _).trans (g.commutes x) }
  have hStruct : v ≫ structureMap A D = structureMap A C := by
    rw [← hφ]
    exact ProetaleAffineTensor.specMap_structureMap A (IsScalarTower.toAlgHom A D C)
  have hEtScheme : Etale (structureMap A C) := by
    rw [← hStruct]
    change Etale ((e.inv ≫ U.ι) ≫ structureMap A D)
    rw [Category.assoc]
    letI : Etale (U.ι ≫ structureMap A D) := EtaleLocusOpenRestriction.etale A D U hEt
    infer_instance
  have hEtRing : Algebra.Etale A C :=
    RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (algebraMap A C))).mp hEtScheme)
  refine ⟨C, inferInstance, inferInstance, hEtRing, k, fun i ↦ ?_⟩
  have hD : algebraMap D C (algebraMap A D (a i)) ∣ algebraMap D C (d i) := by
    apply dvd_of_forall_atPrime
    intro p
    let q := PrimeSpectrum.comap (algebraMap D C) p
    have hq : q ∈ U := by
      change Spec.map φ p ∈ U
      rw [hφ]
      exact (e.inv p).property
    exact map_dvd_atPrime (algebraMap D C) q.asIdeal p.asIdeal rfl
      ((mem_divisibilityOpen_iff _ _ q).mp (hDiv i hq))
  obtain ⟨y, hy⟩ := hD
  refine ⟨y, (hReg i) ?_⟩
  change algebraMap A B (a i) * k y = algebraMap A B (a i) * z i
  have hL : k (algebraMap D C (algebraMap A D (a i))) = algebraMap A B (a i) :=
    (hK _).trans (g.commutes (a i))
  have hR : k (algebraMap D C (d i)) = g (d i) := hK _
  calc
    _ = k (algebraMap D C (algebraMap A D (a i)) * y) := by rw [map_mul k, hL]
    _ = g (d i) := (congrArg k hy.symm).trans hR
    _ = _ := hEq i

end
end ManuscriptAudit.AffineOpenStageSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineOpenStageSections.exists_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
