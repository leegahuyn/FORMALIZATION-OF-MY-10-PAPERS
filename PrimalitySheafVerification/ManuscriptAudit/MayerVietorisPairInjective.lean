import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Algebra.Category.Grp.Abelian

/-! Actual chart restrictions jointly detect a class if the preceding
restriction to the overlap is surjective. -/

namespace ManuscriptAudit.MayerVietorisPairInjective

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite ComposableArrows

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- If restriction of one chart is onto the overlap in degree n, then
both chart restrictions jointly detect degree n+1 classes. -/
theorem pair_injective (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (hLower : Function.Surjective ((F.cohomologyPresheaf n).map S.f₁₂.op)) :
    Function.Injective (fun x : F.H' (n + 1) S.X₄ ↦
      ((F.cohomologyPresheaf (n + 1)).map S.f₂₄.op x,
       (F.cohomologyPresheaf (n + 1)).map S.f₃₄.op x)) := by
  have connecting_zero (x : F.H' n S.X₁) : S.δ F n (n + 1) rfl x = 0 := by
    obtain ⟨y, hy⟩ := hLower x
    let z : ↑(F.H' n S.X₂ ⊞ F.H' n S.X₃) :=
      (AddCommGrpCat.biprodIsoProd _ _).inv ⟨y, 0⟩
    have hz : S.fromBiprod F n z = x := by
      dsimp [z]
      rw [S.fromBiprod_biprodIsoProd_inv_apply, map_zero, sub_zero, hy]
    have h := ConcreteCategory.congr_hom (S.fromBiprod_δ F n (n + 1) rfl) z
    change S.δ F n (n + 1) rfl (S.fromBiprod F n z) = 0 at h
    rwa [hz] at h
  have zero_of_restrict (x : F.H' (n + 1) S.X₄) (hx : S.toBiprod F (n + 1) x = 0) :
      x = 0 := by
    have he : (S.δ F n (n + 1) rfl).hom.range = (S.toBiprod F (n + 1)).hom.ker :=
      ((S.sequence_exact F n (n + 1) rfl).exact' 2 3 4).ab_range_eq_ker
    have hxk : x ∈ (S.toBiprod F (n + 1)).hom.ker := hx
    rw [← he] at hxk
    obtain ⟨y, hy⟩ := hxk
    change S.δ F n (n + 1) rfl y = x at hy
    exact hy.symm.trans (connecting_zero y)
  intro a b h
  apply sub_eq_zero.mp
  apply zero_of_restrict
  have hab : S.toBiprod F (n + 1) a = S.toBiprod F (n + 1) b := by
    rw [S.toBiprod_apply, S.toBiprod_apply]
    exact congrArg (fun x ↦ (AddCommGrpCat.biprodIsoProd _ _).inv x) h
  rw [map_sub, hab, sub_self]

end ManuscriptAudit.MayerVietorisPairInjective

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MayerVietorisPairInjective.pair_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
