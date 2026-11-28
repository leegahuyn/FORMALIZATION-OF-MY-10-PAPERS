import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineGlobalStageFromModel

/-! A finite family on the actual weakly étale affine-line chart
is represented over one actual affine étale algebra globally. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineGlobalStage

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open WeaklyEtaleAffineLineGenericStage (F genericFibre inclusion inclusion_injective)
open WeaklyEtaleAffineLineFiniteNormalization (model)
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

set_option maxHeartbeats 3100000 in
/-- All members of a finite family on the entire actual affine chart
are the images of elements on a single affine étale stage over the affine line. -/
theorem exists_global_stage {κ : Type u} [Finite κ] (z : κ → B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (R K) C),
      Algebra.Etale (R K) C ∧ ∃ j : C →ₐ[R K] B, ∀ i, ∃ x : C, j x = z i := by
  classical
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
  obtain ⟨g, hg, _, hDen⟩ :=
    WeaklyEtaleAffineLineFiniteNormalization.exists_model_map K B L (E := E) e f
      (show Function.Injective f from hf)
  have h (i : κ) : ∃ (a : A) (d : model K L), a ≠ 0 ∧ g d = algebraMap A B a * z i := by
    let x : E := ⟨inclusion K B (z i), Algebra.subset_adjoin (Set.mem_range_self i)⟩
    obtain ⟨a, d, hd⟩ := hDen x
    refine ⟨a, d, nonZeroDivisors.ne_zero a.property, inclusion_injective K B ?_⟩
    calc
      inclusion K B (g d) = f (a • x) := hd
      _ = algebraMap A G a * inclusion K B (z i) := by
        change f ((a : A) • x) = _
        rw [Algebra.smul_def, map_mul, f.commutes] <;> rfl
      _ = inclusion K B (algebraMap A B a * z i) := by
        rw [map_mul, (inclusion K B).commutes]
  choose a d ha hEq using h
  exact WeaklyEtaleAffineLineGlobalStageFromModel.exists_stage K B L g hg a d z ha hEq

end
end ManuscriptAudit.WeaklyEtaleAffineLineGlobalStage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineGlobalStage.exists_global_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
