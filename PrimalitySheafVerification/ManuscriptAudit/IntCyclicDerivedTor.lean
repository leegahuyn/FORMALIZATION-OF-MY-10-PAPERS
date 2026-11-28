import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import PrimalitySheafVerification.ManuscriptAudit.IntCyclicProjectiveResolution

/-! The true derived Tor group over the integers, when the second
module is a cyclic quotient, is the actual kernel of multiplication. -/

namespace ManuscriptAudit.IntCyclicDerivedTor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open IntCyclicProjectiveResolution (residues multiplication resolution resolution_d_one resolution_d_two)
open scoped MonoidalCategory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := ModuleCat.{0} ℤ
private abbrev tensor (A : C) := (tensoringLeft C).obj A

private abbrev imageComplex (A : C) (n : ℕ) (hn : n ≠ 0) :=
  ((tensor A).mapHomologicalComplex (ComplexShape.down ℕ)).obj (resolution n hn).complex

set_option maxHeartbeats 3500000 in
/-- Degree-one native Tor agrees with the kernel in the actual input module. -/
def torOneEquivKernel (A : C) (n : ℕ) (hn : n ≠ 0) :
    ((Tor C 1).obj A).obj (residues n) ≅
      ModuleCat.of ℤ (LinearMap.ker ((n : ℤ) • (LinearMap.id : A →ₗ[ℤ] A))) := by
  let T := tensor A
  let K := imageComplex A n hn
  let S := K.sc' 2 1 0
  have hf : S.f = 0 := by
    change T.map ((resolution n hn).complex.d 2 1) = 0
    rw [resolution_d_two, T.map_zero]
  have hg : S.g = (n : ℤ) • 𝟙 S.X₂ := by
    let I := IntCyclicProjectiveResolution.integers
    change T.map ((resolution n hn).complex.d 1 0) = (n : ℤ) • 𝟙 (T.obj I)
    rw [resolution_d_one, multiplication, T.map_zsmul]
    exact congrArg (fun a : T.obj I ⟶ T.obj I ↦ (n : ℤ) • a) (T.map_id I)
  let eCat : S.X₂ ≅ A := ρ_ A
  let e : S.X₂ ≃ₗ[ℤ] A := eCat.toLinearEquiv
  let D : A →ₗ[ℤ] A := (n : ℤ) • LinearMap.id
  let d : A ⟶ A := ModuleCat.ofHom D
  have hd : d = (n : ℤ) • 𝟙 A := by
    apply ModuleCat.hom_ext
    simp only [d, ModuleCat.hom_ofHom, ModuleCat.hom_zsmul, ModuleCat.hom_id, D]
  have hComm : S.g ≫ eCat.hom = eCat.hom ≫ d := by
    rw [hg, hd, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Category.id_comp, Category.comp_id]
  have hAct (x : S.X₂) : e (S.g x) = D (e x) := by
    exact congrArg (fun h : S.X₂ ⟶ A ↦ h x) hComm
  have hKer : (LinearMap.ker S.g.hom).map e.toLinearMap = LinearMap.ker D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change D (e x) = 0
      rw [← hAct, show S.g x = 0 from hx, map_zero]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change S.g (e.symm y) = 0
      apply e.injective
      rw [hAct, e.apply_symm_apply, map_zero]
      exact hy
  let iKer := e.ofSubmodules (LinearMap.ker S.g.hom) (LinearMap.ker D) hKer
  let iCycles := S.moduleCatCyclesIso
  let B : C := ModuleCat.of ℤ (LinearMap.ker D)
  let iKernel : S.moduleCatLeftHomologyData.K ≃ₗ[ℤ] B :=
    AddEquiv.toIntLinearEquiv
      (modM := S.moduleCatLeftHomologyData.K.isModule) (modM₂ := B.isModule)
      (show (S.moduleCatLeftHomologyData.K : Type) ≃+ (B : Type) from iKer.toAddEquiv)
  let iDerived : (T.leftDerived 1).obj (residues n) ≅ K.homology 1 :=
    (resolution n hn).isoLeftDerivedObj T 1
  let iShort : K.homology 1 ≅ S.homology :=
    K.homologyIsoSc' 2 1 0 (by simp) (by simp)
  letI : IsIso S.homologyπ := S.isIso_homologyπ hf
  change (T.leftDerived 1).obj (residues n) ≅ ModuleCat.of ℤ (LinearMap.ker D)
  exact iDerived ≪≫ iShort ≪≫ (asIso S.homologyπ).symm ≪≫ iCycles ≪≫ iKernel.toModuleIso

end
end ManuscriptAudit.IntCyclicDerivedTor

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntCyclicDerivedTor.torOneEquivKernel
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
