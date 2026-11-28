import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps

/-! Actual affine étale stages have tensor
products and coequalize parallel stage maps over the actual chart. -/

namespace ManuscriptAudit.AffineEtaleStageCoequalizer

open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A S C B : Type u} [CommRing A] [CommRing S] [CommRing C] [CommRing B]
  [Algebra A S] [Algebra A C] [Algebra A B]

/-- The tensor product is an actual affine étale common stage and
its canonical map to the actual chart extends both stage maps. -/
theorem tensor_stage [Algebra.Etale A S] [Algebra.Etale A C]
    (f : S →ₐ[A] B) (g : C →ₐ[A] B) :
    Algebra.Etale A (S ⊗[A] C) ∧
      ∃ k : S ⊗[A] C →ₐ[A] B, k.comp includeLeft = f ∧ k.comp includeRight = g :=
  ⟨Algebra.Etale.comp A S (S ⊗[A] C),
    lift f g (fun _ _ ↦ Commute.all _ _),
    lift_comp_includeLeft f g (fun _ _ ↦ Commute.all _ _),
    lift_comp_includeRight' f g (fun _ _ ↦ Commute.all _ _)⟩

set_option maxHeartbeats 2600000 in
/-- Parallel maps from an étale stage agree after the actual open-and-closed
diagonal quotient, which still maps to the given chart. -/
theorem exists_coequalizer [Algebra.Etale A S] [Algebra.Etale A C]
    (f g : S →ₐ[A] C) (k : C →ₐ[A] B) (hk : k.comp f = k.comp g) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra A Q), Algebra.Etale A Q ∧
      ∃ (q : C →ₐ[A] Q) (l : Q →ₐ[A] B), q.comp f = q.comp g ∧ l.comp q = k := by
  let T := S ⊗[A] S
  let m : T →ₐ[A] S := lift (AlgHom.id A S) (AlgHom.id A S) (fun _ _ ↦ Commute.all _ _)
  let t : T →ₐ[A] C := lift f g (fun _ _ ↦ Commute.all _ _)
  letI : Algebra T S := m.toRingHom.toAlgebra
  have hmL (x : S) : m (x ⊗ₜ[A] (1 : S)) = x := by change x * 1 = x; exact mul_one x
  have hmR (x : S) : m ((1 : S) ⊗ₜ[A] x) = x := by change 1 * x = x; exact one_mul x
  letI : IsScalarTower S T S := IsScalarTower.of_algebraMap_eq (fun x ↦ (hmL x).symm)
  have hmSurj : Function.Surjective (algebraMap T S) := fun x ↦ ⟨x ⊗ₜ[A] (1 : S), hmL x⟩
  have hmEt : Algebra.FormallyEtale T S :=
    Algebra.FormallyEtale.of_restrictScalars (R := S) (A := T) (B := S)
  letI : Algebra.Etale A T := Algebra.Etale.comp A S T
  let I : Ideal T := RingHom.ker m.toRingHom
  have hIFg : I.FG := Algebra.FinitePresentation.ker_fG_of_surjective m hmSurj
  have hI : I * I = I := (Algebra.FormallyEtale.iff_of_surjective hmSurj).mp hmEt
  let J := I.map t.toRingHom
  have hJ : IsIdempotentElem J := by
    change I.map t.toRingHom * I.map t.toRingHom = I.map t.toRingHom
    rw [← Ideal.map_mul, hI]
  have ht : k.comp t = (k.comp f).comp m := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change k (t (x ⊗ₜ[A] y)) = k (f (m (x ⊗ₜ[A] y)))
    have hh : k (g y) = k (f y) := (DFunLike.congr_fun hk y).symm
    change k (f x * g y) = k (f (x * y))
    rw [map_mul, map_mul, map_mul, hh]
  have hker : J ≤ RingHom.ker k.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change m x = 0 at hx
    change k (t x) = 0
    have he := DFunLike.congr_fun ht x
    change k (t x) = k (f (m x)) at he
    rw [he, hx, map_zero, map_zero]
  let Q := C ⧸ J
  let q : C →ₐ[A] Q := Ideal.Quotient.mkₐ A J
  let l : Q →ₐ[A] B := Ideal.Quotient.liftₐ J k hker
  letI : Algebra.FormallyEtale C Q :=
    (Algebra.FormallyEtale.iff_of_surjective
      (show Function.Surjective (algebraMap C Q) from Ideal.Quotient.mk_surjective)).mpr (by
        change IsIdempotentElem (RingHom.ker (Ideal.Quotient.mk J))
        rw [Ideal.mk_ker]
        exact hJ)
  letI : Algebra.FinitePresentation A Q := Algebra.FinitePresentation.quotient (I := J)
    (hIFg.map t.toRingHom)
  have hEt : Algebra.Etale A Q := ⟨Algebra.FormallyEtale.comp A C Q, inferInstance⟩
  refine ⟨Q, inferInstance, inferInstance, hEt, q, l, ?_, ?_⟩
  · ext x
    change q (f x) = q (g x)
    have hM : (x ⊗ₜ[A] (1 : S)) - ((1 : S) ⊗ₜ[A] x) ∈ I := by
      change m ((x ⊗ₜ[A] (1 : S)) - ((1 : S) ⊗ₜ[A] x)) = 0
      rw [map_sub, hmL, hmR, sub_self]
    have hDiff : f x - g x ∈ J := by
      have hh := Ideal.mem_map_of_mem t.toRingHom hM
      change t ((x ⊗ₜ[A] (1 : S)) - ((1 : S) ⊗ₜ[A] x)) ∈ J at hh
      rw [map_sub] at hh
      change f x * g 1 - f 1 * g x ∈ J at hh
      simpa only [map_one, mul_one, one_mul] using hh
    have hZero : q (f x - g x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hDiff
    rw [map_sub] at hZero
    exact sub_eq_zero.mp hZero
  · ext x
    rfl

end
end ManuscriptAudit.AffineEtaleStageCoequalizer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageCoequalizer.tensor_stage,
      ``ManuscriptAudit.AffineEtaleStageCoequalizer.exists_coequalizer] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
