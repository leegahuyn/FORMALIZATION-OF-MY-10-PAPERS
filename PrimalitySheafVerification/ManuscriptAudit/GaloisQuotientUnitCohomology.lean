import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Unit cohomology of a quotient Galois group

The units fixed by a normal subgroup are the units of its fixed
field. Under the quotient Galois correspondence the two actions
on those units agree.
-/

namespace ManuscriptAudit.GaloisQuotientUnitCohomology

open CategoryTheory Rep

noncomputable section

variable (F L : Type) [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
variable (S : Subgroup (L ≃ₐ[F] L)) [S.Normal]

private abbrev B := (Rep.ofAlgebraAutOnUnits F L).quotientToInvariants S
private abbrev C := Rep.ofAlgebraAutOnUnits F (IntermediateField.fixedField S)

private def fixedUnitsInclusion :
    (C F L S).V →ₗ[ℤ] (B F L S).V := by
  let M := IntermediateField.fixedField S
  let f : Additive Mˣ →ₗ[ℤ] Additive Lˣ :=
    (Units.map (algebraMap M L)).toAdditive.toIntLinearMap
  refine f.codRestrict _ (fun a s ↦ ?_)
  apply Additive.toMul.injective
  apply Units.ext
  let x : M := (Additive.toMul a).val
  change (s : L ≃ₐ[F] L) (x : L) = (x : L)
  exact (IntermediateField.mem_fixedField_iff S (x : L)).mp x.property s s.property

/-- Fixed units are exactly the units of the actual fixed field. -/
def fixedUnitsEquiv : (C F L S).V ≃ₗ[ℤ] (B F L S).V := by
  let M := IntermediateField.fixedField S
  refine LinearEquiv.ofBijective (fixedUnitsInclusion F L S) ⟨?_, ?_⟩
  · intro a b hab
    apply Additive.toMul.injective
    apply Units.ext
    apply (algebraMap M L).injective
    exact congrArg (fun y : (B F L S).V ↦ (Additive.toMul y.1).val) hab
  · intro x
    let u : Lˣ := Additive.toMul x.1
    have hu : (u : L) ∈ M := by
      apply (IntermediateField.mem_fixedField_iff S (u : L)).mpr
      intro s hs
      have h := x.property (⟨s, hs⟩ : S)
      exact congrArg (fun y : Additive Lˣ ↦ (Additive.toMul y).val) h
    let v : M := ⟨u.val, hu⟩
    have hv : v ≠ 0 := fun h ↦ u.ne_zero (congrArg Subtype.val h)
    refine ⟨Additive.ofMul (Units.mk0 v hv), ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    rfl

private theorem fixedUnitsInclusion_intertwines (σ : L ≃ₐ[F] L) (a : (C F L S).V) :
    (B F L S).ρ (QuotientGroup.mk' S σ) (fixedUnitsInclusion F L S a) =
      fixedUnitsInclusion F L S
        ((C F L S).ρ (IsGalois.normalAutEquivQuotient S (QuotientGroup.mk' S σ)) a) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  let M := IntermediateField.fixedField S
  let x : M := (Additive.toMul a).val
  change σ (algebraMap M L x) = algebraMap M L
    (IsGalois.normalAutEquivQuotient S (σ : (L ≃ₐ[F] L) ⧸ S) x)
  rw [IsGalois.normalAutEquivQuotient_apply]
  exact (AlgEquiv.restrictNormal_commutes σ M x).symm

/-- The quotient representation on fixed units has the cohomology of
the Galois group of the actual fixed-field extension. -/
def quotientCohomologyIso (n : ℕ) :
    groupCohomology (B F L S) n ≅ groupCohomology (C F L S) n := by
  let e := fixedUnitsEquiv F L S
  apply groupCohomology.mapIso (B := B F L S) (A := C F L S)
    (IsGalois.normalAutEquivQuotient S) e.symm _ n
  intro g
  obtain ⟨σ, rfl⟩ := (QuotientGroup.mk'_surjective S) g
  apply LinearMap.ext
  intro x
  apply e.injective
  change e (e.symm ((B F L S).ρ (QuotientGroup.mk' S σ) x)) =
    e ((C F L S).ρ (IsGalois.normalAutEquivQuotient S (QuotientGroup.mk' S σ)) (e.symm x))
  have h := fixedUnitsInclusion_intertwines F L S σ (e.symm x)
  change (B F L S).ρ (QuotientGroup.mk' S σ) (e (e.symm x)) =
    e ((C F L S).ρ (IsGalois.normalAutEquivQuotient S (QuotientGroup.mk' S σ)) (e.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end

end ManuscriptAudit.GaloisQuotientUnitCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisQuotientUnitCohomology.fixedUnitsEquiv,
      ``ManuscriptAudit.GaloisQuotientUnitCohomology.quotientCohomologyIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
