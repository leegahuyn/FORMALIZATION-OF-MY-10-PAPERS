import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.TorsionFree
import PrimalitySheafVerification.ManuscriptAudit.EtalePrincipalStageSections
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineLocalExtension
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineNormalStageStalk

/-! Finite families of actual functions on a weakly étale affine
chart locally descend to a genuine affine étale stage over the affine line. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineFiniteStage

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open WeaklyEtaleAffineLineGenericStage (F genericFibre inclusion inclusion_injective)
open WeaklyEtaleAffineLineFiniteNormalization (model model_finite)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

set_option maxHeartbeats 3100000 in
/-- Given finitely many elements of the actual affine chart and an
actual prime, a principal open containing that prime admits a map to
an affine étale stage on which all those elements are represented. -/
theorem exists_etale_neighborhood (r : Ideal B) [r.IsPrime]
    {κ : Type u} [Fintype κ] (z : κ → B) :
    ∃ (b : B), b ∉ r ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (R K) C),
        Algebra.Etale (R K) C ∧
        ∃ j : C →ₐ[R K] Localization.Away b,
          ∀ i, ∃ x : C, j x = algebraMap B (Localization.Away b) (z i) := by
  let A := R K
  let G := genericFibre K B
  let s : Set G := Set.range (fun i ↦ inclusion K B (z i))
  let E := Algebra.adjoin (F K) s
  have hE := WeaklyEtaleAffineLineGenericStage.adjoin_finite_etale K B s (Set.finite_range _)
  letI : Module.Finite (F K) E := hE.1
  letI : Algebra.Etale (F K) E := hE.2
  letI : Algebra A E := Algebra.compHom E (algebraMap A (F K))
  letI : IsScalarTower A (F K) E := IsScalarTower.of_algebraMap_eq' rfl
  let f : E →ₐ[Polynomial K] genericFibre K B := E.val.restrictScalars A
  have hf : Function.Injective f := Subtype.val_injective
  obtain ⟨ι, hι, L, hField, hAlg, e, hExt⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (F K) E).mp hE.2
  letI : Finite ι := hι
  letI (i : ι) : Field (L i) := hField i
  letI (i : ι) : Algebra (F K) (L i) := hAlg i
  letI (i : ι) : Algebra A (L i) := Algebra.compHom (L i) (algebraMap A (F K))
  letI (i : ι) : IsScalarTower A (F K) (L i) := IsScalarTower.of_algebraMap_eq' rfl
  letI (i : ι) : Module.Finite (F K) (L i) := (hExt i).1
  letI (i : ι) : Algebra.IsSeparable (F K) (L i) := (hExt i).2
  let D := model K L
  obtain ⟨g, hg, _, hDen⟩ :=
    WeaklyEtaleAffineLineFiniteNormalization.exists_model_map K B L (E := E) e f
      (show Function.Injective f from hf)
  let q := r.comap g.toRingHom
  letI : q.IsPrime := Ideal.IsPrime.comap g.toRingHom
  obtain ⟨hDomain, hVal, hUn⟩ :=
    WeaklyEtaleAffineLineNormalStageStalk.local_properties K B L g r
  letI : IsDomain (Localization.AtPrime q) := hDomain
  letI : ValuationRing (Localization.AtPrime q) := hVal
  letI : Algebra.IsUnramifiedAt A q := hUn
  let φ := CommRingCat.ofHom (algebraMap A B)
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp
    ((Flat.SpecMap_iff (f := φ)).mp (inferInstanceAs (Flat (structureMap A B))))
  letI : Module.IsTorsionFree A D :=
    Function.Injective.moduleIsTorsionFree g hg (fun a x ↦ g.toLinearMap.map_smul a x)
  letI : Module.Flat A D := inferInstance
  letI : Module.Finite A D := model_finite K L
  letI : Algebra.FinitePresentation A D := inferInstance
  have hLoc (i : κ) : ∃ v : Localization.AtPrime q,
      Localization.localRingHom q r g.toRingHom rfl v =
        algebraMap B (Localization.AtPrime r) (z i) := by
    let x : E := ⟨inclusion K B (z i), Algebra.subset_adjoin (Set.mem_range_self i)⟩
    obtain ⟨a, d, hd⟩ := hDen x
    have hEq : g d = algebraMap A B a * z i := by
      apply inclusion_injective K B
      rw [hd, map_mul, (inclusion K B).commutes]
      change f ((a : A) • x) = _
      rw [Algebra.smul_def, map_mul, f.commutes] <;> rfl
    exact WeaklyEtaleAffineLineLocalExtension.exists_local_preimage g r q rfl a
      (nonZeroDivisors.ne_zero a.property) d (z i) hEq
  obtain ⟨t, b, _, hb, hEt, j, _, hz⟩ :=
    EtalePrincipalStageSections.exists_etale_stage g q r rfl z hLoc
  exact ⟨b, hb, Localization.Away t, inferInstance, inferInstance, hEt, j, hz⟩

end
end ManuscriptAudit.WeaklyEtaleAffineLineFiniteStage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineFiniteStage.exists_etale_neighborhood
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
