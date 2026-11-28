import Lean.Util.CollectAxioms
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
  let e : S.X₂ ≃ₗ[ℤ] A := (ρ_ A).toLinearEquiv
  let D : A →ₗ[ℤ] A := (n : ℤ) • LinearMap.id
  have hAct (x : S.X₂) : e (S.g x) = D (e x) := by
    rw [hg]
    change e ((n : ℤ) • x) = (n : ℤ) • e x
    exact e.map_smul (n : ℤ) x
  have hIso : LinearMap.ker S.g.hom ≃ₗ[ℤ] LinearMap.ker D := {
    toFun := fun x ↦ ⟨e x.val, by
      change D (e x.val) = 0
      rw [← hAct, show S.g x.val = 0 from x.property, map_zero]⟩
    invFun := fun y ↦ ⟨e.symm y.val, by
      change S.g (e.symm y.val) = 0
      apply e.injective
      rw [hAct, e.apply_symm_apply, show D y.val = 0 from y.property, map_zero]⟩
    left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
    right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y.val)
    map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
    map_smul' := fun a x ↦ Subtype.ext (e.map_smul a x.val) }
  have hD : ((Tor C 1).obj A).obj (residues n) ≅ S.homology :=
    (resolution n hn).isoLeftDerivedObj T 1
  letI : IsIso S.homologyπ := S.isIso_homologyπ hf
  exact hD ≪≫ (asIso S.homologyπ).symm ≪≫ S.moduleCatCyclesIso ≪≫ hIso.toModuleIso

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
