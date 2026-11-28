import Lean.Util.CollectAxioms
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Multiplication by the coefficient modulus is an isomorphism on a
complex annihilated by a coprime integer. Its actual mapping cone has
zero image in the derived category and is acyclic in every degree. -/

namespace ManuscriptAudit.CrossCharacteristicDerivedCone

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

private theorem bezout {p l : ℕ} (hc : p.Coprime l) :
    Nat.gcdA p l * (p : ℤ) + Nat.gcdB p l * (l : ℤ) = 1 := by
  calc
    _ = ((p.gcd l : ℕ) : ℤ) := by
      rw [mul_comm (Nat.gcdA p l) (p : ℤ), mul_comm (Nat.gcdB p l) (l : ℤ)]
      exact (Nat.gcd_eq_gcd_ab p l).symm
    _ = 1 := by rw [show p.gcd l = 1 from hc, Nat.cast_one]

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K : C} {p l : ℕ}

private theorem bezout_smul (hc : p.Coprime l) (hp : (p : ℤ) • 𝟙 K = 0) :
    (Nat.gcdB p l * (l : ℤ)) • 𝟙 K = 𝟙 K := by
  calc
    _ = (Nat.gcdA p l * (p : ℤ) + Nat.gcdB p l * (l : ℤ)) • 𝟙 K := by
      rw [add_smul, ← smul_smul (Nat.gcdA p l) (p : ℤ), hp, smul_zero, zero_add]
    _ = _ := by rw [bezout hc, one_smul]

/-- The inverse of multiplication by `l` is the corresponding Bézout coefficient. -/
def scalarIso (hc : p.Coprime l) (hp : (p : ℤ) • 𝟙 K = 0) : K ≅ K where
  hom := (l : ℤ) • 𝟙 K
  inv := Nat.gcdB p l • 𝟙 K
  hom_inv_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul, mul_comm]
    exact bezout_smul hc hp
  inv_hom_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul]
    exact bezout_smul hc hp

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : CochainComplex C ℤ} {p l : ℕ}

/-- The two-term coefficient cone becomes zero in the actual derived category. -/
theorem derivedCone_isZero [HasDerivedCategory.{max u v} C]
    (hc : p.Coprime l) (hp : (p : ℤ) • 𝟙 K = 0) :
    IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone ((l : ℤ) • 𝟙 K))) := by
  let e := scalarIso hc hp
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle e.hom)
  have hT : T ∈ distTriang (DerivedCategory C) :=
    DerivedCategory.mappingCone_triangle_distinguished e.hom
  have h : IsIso T.mor₁ := by
    change IsIso (DerivedCategory.Q.map e.hom)
    infer_instance
  exact T.isZero₃_of_isIso₁ hT h

/-- Every cohomology object of the actual cone vanishes. -/
theorem cone_exactAt (hc : p.Coprime l) (hp : (p : ℤ) • 𝟙 K = 0) (n : ℤ) :
    (CochainComplex.mappingCone ((l : ℤ) • 𝟙 K)).ExactAt n := by
  letI := HasDerivedCategory.standard C
  let L := CochainComplex.mappingCone ((l : ℤ) • 𝟙 K)
  have h : IsZero (DerivedCategory.Q.obj L) := derivedCone_isZero hc hp
  have h' := (DerivedCategory.homologyFunctor C n).map_isZero h
  exact (HomologicalComplex.exactAt_iff_isZero_homology L n).mpr
    (((DerivedCategory.homologyFunctorFactors C n).app L).isZero_iff.mp h')

end Abelian

private abbrev C := ModuleCat.{0} ℤ

/-- Degreewise annihilation by the residue characteristic suffices. -/
theorem module_cone_exactAt (K : CochainComplex C ℤ) {p l : ℕ}
    (hc : p.Coprime l) (hp : ∀ i (x : K.X i), (p : ℤ) • x = 0) (n : ℤ) :
    (CochainComplex.mappingCone ((l : ℤ) • 𝟙 K)).ExactAt n := by
  apply cone_exactAt hc _ n
  apply HomologicalComplex.hom_ext
  intro i
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) i
  change E.map ((p : ℤ) • 𝟙 K) = E.map 0
  rw [E.map_zsmul, E.map_id, E.map_zero]
  apply ModuleCat.hom_ext
  ext x
  exact hp i x

end
end ManuscriptAudit.CrossCharacteristicDerivedCone

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CrossCharacteristicDerivedCone.scalarIso,
      ``ManuscriptAudit.CrossCharacteristicDerivedCone.derivedCone_isZero,
      ``ManuscriptAudit.CrossCharacteristicDerivedCone.cone_exactAt,
      ``ManuscriptAudit.CrossCharacteristicDerivedCone.module_cone_exactAt] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
