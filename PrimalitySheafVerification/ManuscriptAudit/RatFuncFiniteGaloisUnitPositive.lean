import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexGroupCohomology
import PrimalitySheafVerification.ManuscriptAudit.GaloisQuotientUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.GaloisSubgroupUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.GroupCohomologyNormalSubgroupAcyclic
import PrimalitySheafVerification.ManuscriptAudit.PGroupCyclicNormal
import PrimalitySheafVerification.ManuscriptAudit.RatFuncCyclicUnitPositive

/-!
# Positive unit cohomology of all finite Galois extensions over K(t)

For p-groups, a central cyclic subgroup and the quotient give the
subgroup and quotient vanishing hypotheses for dimension shifting.
The finite-index trace detects the resulting vanishing on Sylow
subgroups in every positive degree.
-/

namespace ManuscriptAudit.RatFuncTsen

open CategoryTheory CategoryTheory.Limits
open GaloisSubgroupUnitCohomology GaloisQuotientUnitCohomology

private theorem ofModuleIso {A B : ModuleCat ℤ} (e : A ≅ B) (h : Subsingleton B) :
    Subsingleton A := by
  have hinj : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact ⟨fun x y ↦ hinj (h.elim _ _)⟩

set_option maxHeartbeats 1800000 in
private theorem pGroup_units_H_succ_aux (K : Type) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] :
    ∀ (n : ℕ) (F L : Type) [Field F] [Field L] [Algebra (RatFunc K) F]
      [FiniteDimensional (RatFunc K) F] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Nat.card (L ≃ₐ[F] L) = n → IsPGroup p (L ≃ₐ[F] L) →
      ∀ i : ℕ, Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) (i + 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F L _ _ _ _ _ _ _ hCard hp
    let G := L ≃ₐ[F] L
    let A := Rep.ofAlgebraAutOnUnits F L
    by_cases hG : Subsingleton G
    · letI := hG
      exact finiteExtension_cyclic_units_H_succ_subsingleton K F L
    letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hG
    obtain ⟨S, hNormal, hCyclic, hLt⟩ := PGroupCyclicNormal.exists_cyclic_normal_smaller hp
    letI := hNormal
    letI := hCyclic
    let M := IntermediateField.fixedField S
    letI : Algebra (RatFunc K) M :=
      ((algebraMap F M).comp (algebraMap (RatFunc K) F)).toAlgebra
    letI : IsScalarTower (RatFunc K) F M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : FiniteDimensional (RatFunc K) M := Module.Finite.trans (R := RatFunc K) F M
    letI : IsGalois M L := IsGalois.of_fixed_field L S
    let eS := IntermediateField.subgroupEquivAlgEquiv S
    letI : IsCyclic (L ≃ₐ[M] L) := isCyclic_of_surjective eS eS.surjective
    let eQ := IsGalois.normalAutEquivQuotient S
    have hpQ : IsPGroup p (M ≃ₐ[F] M) := (hp.to_quotient S).of_equiv eQ
    have hCardQ : Nat.card (M ≃ₐ[F] M) < n := by
      calc
        Nat.card (M ≃ₐ[F] M) = Nat.card (G ⧸ S) := (Nat.card_congr eQ.toEquiv).symm
        _ < Nat.card G := hLt
        _ = n := hCard
    have hSub Sdegree :
        IsZero (groupCohomology (Rep.res S.subtype A) (Sdegree + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr <|
        ofModuleIso (fixedFieldCohomologyIso F L S (Sdegree + 1))
          (finiteExtension_cyclic_units_H_succ_subsingleton K M L Sdegree)
    have hQuot Qdegree :
        IsZero (groupCohomology (A.quotientToInvariants S) (Qdegree + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr <|
        ofModuleIso (quotientCohomologyIso F L S (Qdegree + 1))
          (ih _ hCardQ F M rfl hpQ Qdegree)
    intro i
    exact ModuleCat.subsingleton_of_isZero
      (GroupCohomologyNormalSubgroupAcyclic.H_succ_isZero S i A hSub hQuot)

/-- All positive cohomology of the unit representation vanishes for a
finite Galois p-extension of any finite extension of K(t). -/
theorem pGroup_units_H_succ_subsingleton (K F L : Type) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (p : ℕ) [Fact p.Prime] (hp : IsPGroup p (L ≃ₐ[F] L)) (i : ℕ) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) (i + 1)) :=
  pGroup_units_H_succ_aux K p _ F L rfl hp i

/-- All positive group cohomology of the unit representation vanishes
for every finite Galois extension of a finite extension of K(t). -/
theorem finiteGalois_units_H_succ_subsingleton (K F L : Type) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (i : ℕ) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) (i + 1)) := by
  apply FiniteIndexGroupCohomology.subsingleton_of_sylow
  intro p hp P
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup (L ≃ₐ[F] L) := P
  let M := IntermediateField.fixedField S
  letI : Algebra (RatFunc K) M :=
    ((algebraMap F M).comp (algebraMap (RatFunc K) F)).toAlgebra
  letI : IsScalarTower (RatFunc K) F M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional (RatFunc K) M := Module.Finite.trans (R := RatFunc K) F M
  letI : IsGalois M L := IsGalois.of_fixed_field L S
  have hP : IsPGroup p (L ≃ₐ[M] L) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv S)
  exact ofModuleIso (fixedFieldCohomologyIso F L S (i + 1))
    (pGroup_units_H_succ_subsingleton K M L p hP i)

/-- Specialization to the rational function field itself. -/
theorem rationalFunction_finiteGalois_units_H_succ_subsingleton (K L : Type)
    [Field K] [IsAlgClosed K] [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [IsGalois (RatFunc K) L] (i : ℕ) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits (RatFunc K) L) (i + 1)) :=
  finiteGalois_units_H_succ_subsingleton K (RatFunc K) L i

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncTsen.pGroup_units_H_succ_subsingleton,
      ``ManuscriptAudit.RatFuncTsen.finiteGalois_units_H_succ_subsingleton,
      ``ManuscriptAudit.RatFuncTsen.rationalFunction_finiteGalois_units_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
