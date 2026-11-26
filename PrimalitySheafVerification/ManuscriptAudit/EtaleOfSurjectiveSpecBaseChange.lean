import Lean
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! A finite algebra already flat and finitely presented can be tested for étaleness
after a base change surjective on prime spectra. The proof uses the support of its
module of Kähler differentials. -/

open Algebra TensorProduct

namespace ManuscriptAudit.EtaleOfSurjectiveSpecBaseChange

section Modules

variable (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

theorem subsingleton_of_tensor_subsingleton
    (hSpec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    (hTensor : Subsingleton (B ⊗[A] M)) : Subsingleton M := by
  classical
  by_contra hM
  obtain ⟨p, hp⟩ :=
    (Module.nonempty_support_iff (R := A) (M := M)).mpr
      (not_subsingleton_iff_nontrivial.mp hM)
  let k := p.asIdeal.ResidueField
  letI : Nontrivial (k ⊗[A] B) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap (R := A) (S := B) p).mpr (hSpec p)
  letI : Module.Free k (k ⊗[A] B) := inferInstance
  letI : Subsingleton (B ⊗[A] M) := hTensor
  have hBoth : Subsingleton ((k ⊗[A] B) ⊗[k] (k ⊗[A] M)) :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange A k B M).symm.subsingleton
  have hFiber : Subsingleton (k ⊗[A] M) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k (k ⊗[A] B)).mp hBoth
  exact not_nontrivial_iff_subsingleton.mpr hFiber
    ((Module.mem_support_iff_nontrivial_residueField_tensorProduct (M := M) p).mp hp)

end Modules

theorem etale_of_tensor_etale (A B T : Type*) [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Module.Finite A T] [Module.Flat A T]
    [Algebra.FinitePresentation A T] [Algebra.Etale B (B ⊗[A] T)]
    (hSpec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Algebra.Etale A T := by
  letI : Algebra T (B ⊗[A] T) := Algebra.TensorProduct.rightAlgebra
  have hTensor : Subsingleton (B ⊗[A] Ω[T⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase A B T (B ⊗[A] T)).subsingleton
  letI : Module.Finite A Ω[T⁄A] := Module.Finite.trans T Ω[T⁄A]
  letI : Algebra.FormallyUnramified A T :=
    ⟨subsingleton_of_tensor_subsingleton A B Ω[T⁄A] hSpec hTensor⟩
  exact Algebra.Etale.of_formallyUnramified_of_flat

end ManuscriptAudit.EtaleOfSurjectiveSpecBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleOfSurjectiveSpecBaseChange.subsingleton_of_tensor_subsingleton,
      ``ManuscriptAudit.EtaleOfSurjectiveSpecBaseChange.etale_of_tensor_etale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
