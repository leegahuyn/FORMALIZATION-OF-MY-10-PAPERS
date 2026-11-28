import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-! If all degree-zero sections on the second open are ambient restrictions,
the Mayer–Vietoris difference has the range of the first open's restriction. -/

namespace ManuscriptAudit.MayerVietorisZeroRange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- A surjective ambient restriction to the second open removes its contribution
to the overlap restriction range. -/
theorem range_fromBiprod_eq_left
    (hRight : Function.Surjective ((F.cohomologyPresheaf 0).map S.f₃₄.op)) :
    ((S.fromBiprod F 0).hom).range = ((F.cohomologyPresheaf 0).map S.f₁₂.op).hom.range := by
  let E := AddCommGrpCat.biprodIsoProd (F.H' 0 S.X₂) (F.H' 0 S.X₃)
  let Z := F.cohomologyPresheaf 0
  have hSquare : Z.map S.f₃₄.op ≫ Z.map S.f₁₃.op = Z.map S.f₂₄.op ≫ Z.map S.f₁₂.op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, S.toSquare.fac]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    let a := E.hom x
    obtain ⟨z, hz⟩ := hRight a.2
    have he : Z.map S.f₁₂.op (Z.map S.f₂₄.op z) = Z.map S.f₁₃.op a.2 := by
      rw [← hz]
      exact congrArg (fun h : F.H' 0 S.X₄ ⟶ F.H' 0 S.X₁ => h z) hSquare.symm
    refine ⟨a.1 - Z.map S.f₂₄.op z, ?_⟩
    calc
      Z.map S.f₁₂.op (a.1 - Z.map S.f₂₄.op z) =
          Z.map S.f₁₂.op a.1 - Z.map S.f₁₃.op a.2 := by rw [map_sub, he]
      _ = S.fromBiprod F 0 (E.inv a) :=
        (S.fromBiprod_biprodIsoProd_inv_apply F a.1 a.2).symm
      _ = S.fromBiprod F 0 x := by
        dsimp only [a]
        rw [E.hom_inv_id_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨E.inv ⟨x, 0⟩, ?_⟩
    change S.fromBiprod F 0 (E.inv ⟨x, 0⟩) = Z.map S.f₁₂.op x
    rw [S.fromBiprod_biprodIsoProd_inv_apply, map_zero, sub_zero]

end

end ManuscriptAudit.MayerVietorisZeroRange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.MayerVietorisZeroRange.range_fromBiprod_eq_left
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
