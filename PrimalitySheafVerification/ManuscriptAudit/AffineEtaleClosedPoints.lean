import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.DedekindDomain.Factorization
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleGenericField

/-!
# Closed points under affine étale morphisms of integral curves

A height-one point cannot lie over the generic point: the latter has a
field as its fiber on an integral affine étale chart. Above each closed
point there are only finitely many points by the actual residue-field
fiber of the morphism.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open AffineEtaleGenericField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.Etale A B]

private theorem comap_ne_bot (q : HeightOneSpectrum B) :
    q.asIdeal.comap (algebraMap A B) ≠ ⊥ := by
  intro h
  let F := FractionRing A
  let L := F ⊗[A] B
  let M := Algebra.algebraMapSubmonoid B A⁰
  letI : Field L := (genericFiber_isField A B F).toField
  letI : IsFractionRing B L := genericFiber_isFractionRing A B F
  letI : IsLocalization M L := IsLocalization.tensorRight F A⁰
  have hDisj : Disjoint (M : Set B) (q.asIdeal : Set B) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a, ha, rfl⟩ hq
    have ha' : a ∈ q.asIdeal.comap (algebraMap A B) := hq
    rw [h] at ha'
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (Ideal.mem_bot.mp ha')
  let J := Ideal.map (algebraMap B L) q.asIdeal
  letI : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M L q.asIdeal q.isPrime hDisj
  have hJ : J = ⊥ := Ideal.eq_bot_of_prime J
  have hUnder : J.under B = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint M L q.isPrime hDisj
  rw [hJ, Ideal.under_def, ← RingHom.ker_eq_comap_bot, RingHom.ker_eq_bot.mpr
    (IsFractionRing.injective B L)] at hUnder
  exact q.ne_bot hUnder.symm

/-- The actual contraction on height-one points of integral affine étale charts. -/
def comap (q : HeightOneSpectrum B) : HeightOneSpectrum A :=
  ⟨q.asIdeal.comap (algebraMap A B), q.asIdeal.comap_isPrime _, comap_ne_bot A B q⟩

/-- Each fiber of contraction is finite, using the actual residue-field
fiber and its artinian spectrum. -/
theorem finite_comap_fiber (p : HeightOneSpectrum A) :
    Finite {q : HeightOneSpectrum B // comap A B q = p} := by
  letI : p.asIdeal.IsPrime := p.isPrime
  let L := p.asIdeal.Fiber B
  letI : Module.Finite p.asIdeal.ResidueField L :=
    Algebra.FormallyUnramified.finite_of_free p.asIdeal.ResidueField L
  letI : IsArtinianRing L := IsArtinianRing.of_finite p.asIdeal.ResidueField L
  let e := PrimeSpectrum.primesOverOrderIsoFiber A B p.asIdeal
  let f : {q : HeightOneSpectrum B // comap A B q = p} → p.asIdeal.primesOver B :=
    fun q ↦ ⟨q.val.asIdeal, q.val.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal q.property).symm⟩⟩
  apply Finite.of_injective (fun q ↦ e (f q))
  intro q r h
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  exact congrArg Subtype.val (e.injective h)

end

end ManuscriptAudit.AffineEtaleClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleClosedPoints.comap,
      ``ManuscriptAudit.AffineEtaleClosedPoints.finite_comap_fiber] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
