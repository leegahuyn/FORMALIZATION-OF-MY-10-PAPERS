import Lean.Util.CollectAxioms
import Mathlib.RingTheory.FinitePresentation
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageColimit

/-! Maps from finitely presented algebras into the actual chart
factor through actual affine étale stages. -/

namespace ManuscriptAudit.AffineEtaleStageFinitePresentationLift

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B P : Type u} [CommRing A] [CommRing B] [CommRing P]
  [Algebra A B] [Algebra A P] [WeaklyEtale (structureMap A B)]

set_option maxHeartbeats 3100000 in
/-- The actual finite family of polynomial relations is imposed
after a single actual étale refinement, preserving the chart map. -/
theorem exists_factorization [Algebra.FinitePresentation A P]
    (hApprox : FiniteTupleApproximation A B) (g : P →ₐ[A] B) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra A Q), Algebra.Etale A Q ∧
      ∃ (a : P →ₐ[A] Q) (b : Q →ₐ[A] B), b.comp a = g := by
  classical
  obtain ⟨n, f, hf, hFg⟩ := Algebra.FinitePresentation.out (R := A) (A := P)
  let z (i : Fin n) := g (f (MvPolynomial.X i))
  obtain ⟨C, hR, hA, hE, k, hk⟩ := hApprox (fun i : ULift.{u} (Fin n) ↦ z i.down)
  letI : CommRing C := hR
  letI : Algebra A C := hA
  letI : Algebra.Etale A C := hE
  choose y hy using hk
  let m : MvPolynomial (Fin n) A →ₐ[A] C := MvPolynomial.aeval (fun i ↦ y (ULift.up i))
  have hm : k.comp m = g.comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    change k (MvPolynomial.aeval (fun j ↦ y (ULift.up j)) (MvPolynomial.X i)) = z i
    rw [MvPolynomial.aeval_X]
    exact hy (ULift.up i)
  obtain ⟨s, hS⟩ := hFg
  have hSpan : Ideal.span (s : Set (MvPolynomial (Fin n) A)) = RingHom.ker f.toRingHom := hS
  let r (a : s) := m a.val
  have hzero (a : s) : k (r a) = 0 := by
    have ha : a.val ∈ RingHom.ker f.toRingHom := hSpan ▸ Ideal.subset_span a.property
    have hfa : f a.val = 0 := ha
    change (k.comp m) a.val = 0
    rw [hm]
    change g (f a.val) = 0
    rw [hfa, map_zero]
  obtain ⟨Q, hQ, hQA, hEt, q, l, hlq, hKill⟩ :=
    AffineEtaleStageGlobalRelations.exists_refinement hApprox k r hzero
  letI : CommRing Q := hQ
  letI : Algebra A Q := hQA
  letI : Algebra.Etale A Q := hEt
  have hK : RingHom.ker f.toRingHom ≤ RingHom.ker (q.comp m).toRingHom := by
    rw [← hSpan]
    apply Ideal.span_le.mpr
    intro a ha
    exact hKill ⟨a, ha⟩
  let u := AlgHom.liftOfSurjective f hf (q.comp m) hK
  refine ⟨Q, inferInstance, inferInstance, hEt, u, l, ?_⟩
  ext x
  obtain ⟨p, rfl⟩ := hf x
  change l (u (f p)) = g (f p)
  unfold u
  rw [AlgHom.liftOfSurjective_apply]
  exact (DFunLike.congr_fun hlq (m p)).trans (DFunLike.congr_fun hm p)

end
end ManuscriptAudit.AffineEtaleStageFinitePresentationLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageFinitePresentationLift.exists_factorization
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
