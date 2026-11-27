import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GaloisCokernelDescent
import PrimalitySheafVerification.ManuscriptAudit.GaloisInjectiveHOne
import PrimalitySheafVerification.ManuscriptAudit.GaloisUnitSectionSequence
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyDimensionShift

/-! Finite Galois H² vanishing implies degree-two vanishing for the actual field unit sheaf. -/

namespace ManuscriptAudit.FieldEtaleUnitsHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open FieldEtaleGaloisCovers GaloisCoverAction GroupCohomologyBoundary KummerUnitsSheaf

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

noncomputable section

variable (K : Type) [Field K]

private abbrev X := Spec (CommRingCat.of K)
private abbrev J := (X K).smallEtaleTopology
private abbrev fieldUnits := fullCoordinateUnitSheaf (X K)

private def allFiniteGaloisHTwoVanish : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L],
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)

private theorem galois_unitCokernel_HOne_subsingleton
    (L : Type) [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    {I : Sheaf (J K) AddCommGrpCat.{0}} [Injective I]
    (i : fieldUnits K ⟶ I) [Mono i]
    (h : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)) :
    Subsingleton (groupCohomology (sectionsRep K L (cokernel i)) 1) := by
  let S := unitSectionSequence K L i
  let e := (groupCohomology.functor ℤ (L ≃ₐ[K] L) 2).mapIso (unitSectionIso K L)
  have hinj := (ModuleCat.mono_iff_injective e.hom).mp (inferInstance : Mono e.hom)
  have hFirst : Subsingleton (groupCohomology S.X₁ 2) :=
    ⟨fun a b => hinj (h.elim (e.hom a) (e.hom b))⟩
  exact HOne_subsingleton_of_middle_and_HTwo S (unitSectionSequence_shortExact K L i)
    (injective_sections_HOne_subsingleton K L I) hFirst

private theorem unitCokernel_HOne_subsingleton
    {I : Sheaf (J K) AddCommGrpCat.{0}} [Injective I]
    (i : fieldUnits K ⟶ I) [Mono i] (h : allFiniteGaloisHTwoVanish K) :
    Subsingleton (Sheaf.H (cokernel i) 1) := by
  let Q := cokernel i
  let P := Injective.under Q
  let j : Q ⟶ P := Injective.ι Q
  letI : Mono j := inferInstanceAs (Mono (Injective.ι Q))
  let hT : IsTerminal (terminalObject K) := terminalObject_isTerminal K
  apply SheafH1Descent.H1_subsingleton_of_global_lifts j hT
  intro x
  obtain ⟨L, hF, hA, hM, hG, y, hy⟩ := exists_cokernel_lift_on_finiteGalois_cover K j x
  letI := hF
  letI := hA
  letI := hM
  letI := hG
  exact exists_global_cokernel_lift_of_HOne K L j
    (galois_unitCokernel_HOne_subsingleton K L i (h L)) x y hy

theorem unitSheaf_HTwo_subsingleton_of_finiteGalois
    (h : ∀ (L : Type) [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L],
      Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)) :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of K))) 2) := by
  let F := fieldUnits K
  let I := Injective.under F
  let i : F ⟶ I := Injective.ι F
  let S := ShortComplex.cokernelSequence i
  letI : Mono i := inferInstanceAs (Mono (Injective.ι F))
  letI : Injective S.X₂ := inferInstanceAs (Injective I)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) (inferInstanceAs (Mono i))
    (inferInstanceAs (Epi (cokernel.π i)))
  let e := SheafCohomologyDimensionShift.hOneQuotientEquivHTwo S hS
  have hOne : Subsingleton (Sheaf.H S.X₃ 1) := unitCokernel_HOne_subsingleton K i h
  exact ⟨fun a b => e.symm.injective (hOne.elim (e.symm a) (e.symm b))⟩

end
end ManuscriptAudit.FieldEtaleUnitsHTwo

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FieldEtaleUnitsHTwo.unitSheaf_HTwo_subsingleton_of_finiteGalois
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
