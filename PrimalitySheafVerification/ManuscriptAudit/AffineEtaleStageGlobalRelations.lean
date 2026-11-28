import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCoequalizer
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAnnihilatorMap

/-! Finitely many elements whose images agree on the whole actual
chart agree after an actual affine étale refinement. -/

namespace ManuscriptAudit.AffineEtaleStageGlobalRelations

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open WeaklyEtaleAnnihilatorMap (commonAnnihilator annihilates)
open scoped BigOperators TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B] [Algebra.Etale A C] [WeaklyEtale (structureMap A B)]

set_option maxHeartbeats 3400000 in
/-- Refine a stage to kill all given relations. Only the actual
finite tuple approximation on the chart is required. -/
theorem exists_refinement
    (hApprox : ∀ {ι : Type u} [Finite ι] (w : ι → B),
      ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E),
        Algebra.Etale A E ∧ ∃ g : E →ₐ[A] B, ∀ i, ∃ x : E, g x = w i)
    (k : C →ₐ[A] B) {κ : Type u} [Finite κ] (z : κ → C) (hz : ∀ i, k (z i) = 0) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra A Q), Algebra.Etale A Q ∧
      ∃ (q : C →ₐ[A] Q) (l : Q →ₐ[A] B), l.comp q = k ∧ ∀ i, q (z i) = 0 := by
  classical
  letI : Etale (structureMap A C) :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (f := CommRingCat.ofHom (algebraMap A C))).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  letI : WeaklyEtale (structureMap A C) := inferInstance
  let J := commonAnnihilator z
  let v : J → B := fun j ↦ k (j : C)
  have hV : Set.range v = k.toRingHom '' (J : Set C) := by
    ext b
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hone : (1 : B) ∈ Submodule.span B (Set.range v) := by
    rw [hV]
    change (1 : B) ∈ J.map k.toRingHom
    rw [WeaklyEtaleAnnihilatorMap.map_eq_top k z hz]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (v := v)).mp hone
  have hSum : ∑ i ∈ c.support, c i * v i = 1 := by
    simpa only [Finsupp.sum, smul_eq_mul] using hc
  let τ := {i : J // i ∈ c.support}
  obtain ⟨E, hRing, hAlg, hEt, g, hg⟩ := hApprox (fun i : τ ↦ c i.val)
  letI : CommRing E := hRing
  letI : Algebra A E := hAlg
  letI : Algebra.Etale A E := hEt
  choose y hy using hg
  let a (i : J) : E := if hi : i ∈ c.support then y ⟨i, hi⟩ else 0
  have ha (i : J) (hi : i ∈ c.support) : g (a i) = c i := by
    simpa only [a, dif_pos hi] using hy (⟨i, hi⟩ : τ)
  let S := C ⊗[A] E
  let iC : C →ₐ[A] S := Algebra.TensorProduct.includeLeft
  let iE : E →ₐ[A] S := Algebra.TensorProduct.includeRight
  obtain ⟨hEtS, t, hTC, hTE⟩ := AffineEtaleStageCoequalizer.tensor_stage k g
  letI : Algebra.Etale A S := hEtS
  have hC (x : C) : t (iC x) = k x := DFunLike.congr_fun hTC x
  have hE (x : E) : t (iE x) = g x := DFunLike.congr_fun hTE x
  let s : S := ∑ i ∈ c.support, iE (a i) * iC (i : C)
  have hs : t s = 1 := by
    calc
      _ = ∑ i ∈ c.support, c i * v i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul, hE, hC, ha i hi]
      _ = _ := hSum
  have hz' (j : κ) : s * iC (z j) = 0 := by
    change (∑ i ∈ c.support, iE (a i) * iC (i : C)) * iC (z j) = 0
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [mul_assoc, ← map_mul, annihilates z i j, map_zero, mul_zero]
  let Q := Localization.Away s
  let q : C →ₐ[A] Q := (IsScalarTower.toAlgHom A S Q).comp iC
  have hu : IsUnit (t s) := hs.symm ▸ isUnit_one
  let l : Q →ₐ[A] B := IsLocalization.Away.liftAlgHom s (f := t) hu
  refine ⟨Q, inferInstance, inferInstance, inferInstance, q, l, ?_, fun j ↦ ?_⟩
  · ext x
    change l (algebraMap S Q (iC x)) = k x
    exact (IsLocalization.Away.lift_eq s hu _).trans (hC x)
  · apply (IsLocalization.Away.algebraMap_isUnit (S := Q) s).isRegular.left
    change algebraMap S Q s * algebraMap S Q (iC (z j)) = algebraMap S Q s * 0
    rw [← map_mul, hz' j, map_zero, mul_zero]

end
end ManuscriptAudit.AffineEtaleStageGlobalRelations

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageGlobalRelations.exists_refinement
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
