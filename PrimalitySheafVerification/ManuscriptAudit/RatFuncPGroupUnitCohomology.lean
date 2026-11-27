import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GaloisQuotientUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.GaloisSubgroupUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.GroupH2NormalSubgroup
import PrimalitySheafVerification.ManuscriptAudit.PGroupCyclicNormal
import PrimalitySheafVerification.ManuscriptAudit.RatFuncFiniteExtensionUnitCohomology

/-!
# Unit cohomology of finite Galois p-extensions over K(t)

In the cyclic subgroup, the second group vanishes by Tsen's norm
surjectivity and the first by Hilbert 90. Induction on the smaller
quotient over the fixed field and the degree-two normal subgroup
argument give vanishing for the original Galois p-group.
-/

namespace ManuscriptAudit.RatFuncTsen

open CategoryTheory
open GaloisSubgroupUnitCohomology GaloisQuotientUnitCohomology

private theorem fromModuleIso {A B : ModuleCat ℤ} (e : A ≅ B) (h : Subsingleton B) :
    Subsingleton A := by
  have inj : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact ⟨fun x y ↦ inj (h.elim _ _)⟩

private theorem cyclic_units_HTwo (K F L : Type) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [IsCyclic (L ≃ₐ[F] L)] :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[F] L)
  exact finiteExtension_cyclic_units_even_subsingleton K F L g hg 2 (by decide)

private theorem galoisUnits_HTwo_of_normal (F L : Type) [Field F] [Field L] [Algebra F L]
    (S : Subgroup (L ≃ₐ[F] L)) [S.Normal]
    (hOne : Subsingleton (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits F L)) 1))
    (hTwo : Subsingleton (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits F L)) 2))
    (hQuot : Subsingleton (groupCohomology ((Rep.ofAlgebraAutOnUnits F L).quotientToInvariants S) 2)) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) := by
  let G := L ≃ₐ[F] L
  let A := Additive Lˣ
  let B := Rep.ofDistribMulAction ℤ G A
  let C := Rep.ofDistribMulAction ℤ S A
  have hb : B = Rep.ofAlgebraAutOnUnits F L := rfl
  have hc : C = Rep.res S.subtype (Rep.ofAlgebraAutOnUnits F L) := rfl
  have h₁ : Subsingleton (groupCohomology C 1) := by rw [hc]; exact hOne
  have h₂ : Subsingleton (groupCohomology C 2) := by rw [hc]; exact hTwo
  have h₃ : Subsingleton (groupCohomology (B.quotientToInvariants S) 2) := by
    rw [hb]
    exact hQuot
  have h : Subsingleton (groupCohomology B 2) :=
    GroupTwoCocycleConjugation.H2_subsingleton_of_normal (G := G) (A := A) S h₁ h₂ h₃
  rwa [hb] at h

set_option maxHeartbeats 1800000 in
private theorem pGroup_units_HTwo_aux (K : Type) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] :
    ∀ (n : ℕ) (F L : Type) [Field F] [Field L] [Algebra (RatFunc K) F]
      [FiniteDimensional (RatFunc K) F] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Nat.card (L ≃ₐ[F] L) = n → IsPGroup p (L ≃ₐ[F] L) →
      Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F L _ _ _ _ _ _ _ hCard hp
    let G := L ≃ₐ[F] L
    by_cases hG : Subsingleton G
    · letI := hG
      exact cyclic_units_HTwo K F L
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
    have hTwoS := fromModuleIso (fixedFieldCohomologyIso F L S 2) (cyclic_units_HTwo K M L)
    let eQ := IsGalois.normalAutEquivQuotient S
    have hpQ : IsPGroup p (M ≃ₐ[F] M) := (hp.to_quotient S).of_equiv eQ
    have hCardQ : Nat.card (M ≃ₐ[F] M) < n := by
      calc
        Nat.card (M ≃ₐ[F] M) = Nat.card (G ⧸ S) := (Nat.card_congr eQ.toEquiv).symm
        _ < Nat.card G := hLt
        _ = n := hCard
    have hTwoQ := fromModuleIso (quotientCohomologyIso F L S 2)
      (ih _ hCardQ F M rfl hpQ)
    exact galoisUnits_HTwo_of_normal F L S (restricted_HOne_subsingleton F L S) hTwoS hTwoQ

/-- Degree-two cohomology of the unit representation vanishes for a
finite Galois p-extension of any finite extension of K(t). -/
theorem pGroup_units_HTwo_subsingleton (K F L : Type) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (p : ℕ) [Fact p.Prime] (hp : IsPGroup p (L ≃ₐ[F] L)) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2) :=
  pGroup_units_HTwo_aux K p _ F L rfl hp

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RatFuncTsen.pGroup_units_HTwo_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
