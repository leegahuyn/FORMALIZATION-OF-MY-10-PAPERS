import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import PrimalitySheafVerification.ManuscriptAudit.AddCommGrpImageFactorization
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleGaloisCovers
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! Lifts of native cokernel sections exist on finite Galois covers of the field. -/

namespace ManuscriptAudit.FieldEtaleGaloisCovers

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

theorem galoisArrow_is_cover (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsGalois K L] :
    Sieve.generate (Presieve.singleton (galoisArrow K L)) ∈
      (Spec (CommRingCat.of K)).smallEtaleTopology (terminalObject K) := by
  apply KummerSiteCover.singleton_mem_smallEtaleTopology
  intro y
  let x : (galoisObject K L).left := Classical.choice
    (inferInstance : Nonempty (PrimeSpectrum L))
  exact ⟨x, Subsingleton.elim _ _⟩

theorem exists_cokernel_lift_on_finiteGalois_cover (K : Type) [Field K]
    {F I : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{0}}
    (i : F ⟶ I) (x : (cokernel i).obj.obj (op (terminalObject K))) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (_ : IsGalois K L) (z : I.obj.obj (op (galoisObject K L))),
        (cokernel.π i).hom.app _ z =
          (cokernel i).obj.map (galoisArrow K L).op x := by
  letI := AddCommGrpImageFactorization.functorialSurjectiveInjectiveFactorization
  have h := SheafH1Descent.cokernel_section_lift_sieve_mem i x
  obtain ⟨L, hF, hA, hM, hG, hz⟩ :=
    coveringSieve_has_finiteGalois_arrow K (Presheaf.imageSieve (cokernel.π i).hom x) h
  letI := hF
  letI := hA
  letI := hM
  letI := hG
  obtain ⟨z, hz⟩ := hz
  exact ⟨L, hF, hA, hM, hG, z, hz⟩

end
end ManuscriptAudit.FieldEtaleGaloisCovers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FieldEtaleGaloisCovers.galoisArrow_is_cover,
      ``ManuscriptAudit.FieldEtaleGaloisCovers.exists_cokernel_lift_on_finiteGalois_cover] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
