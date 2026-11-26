import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Algebra.Category.Grp.Abelian

/-! In a Mayer–Vietoris square, a class is detected by its first chart
when lower restrictions onto the overlap are surjective and higher
restriction from the second chart to the overlap is injective. -/

namespace ManuscriptAudit.MayerVietorisRestriction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Opposite ComposableArrows

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Actual higher cohomology restriction to the first open is injective
under the stated lower- and higher-degree overlap conditions. -/
theorem first_restriction_injective
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (hLower : Function.Surjective ((F.cohomologyPresheaf n).map S.f₁₂.op))
    (hHigher : Function.Injective ((F.cohomologyPresheaf (n + 1)).map S.f₁₃.op)) :
    Function.Injective ((F.cohomologyPresheaf (n + 1)).map S.f₂₄.op) := by
  let r := (F.cohomologyPresheaf (n + 1)).map S.f₂₄.op
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
  have zero_of_restrict (x : F.H' (n + 1) S.X₄) (hx : r x = 0) : x = 0 := by
    let r' := (F.cohomologyPresheaf (n + 1)).map S.f₃₄.op
    have h := ConcreteCategory.congr_hom (S.toBiprod_fromBiprod F (n + 1)) x
    change S.fromBiprod F (n + 1) (S.toBiprod F (n + 1) x) = 0 at h
    rw [S.toBiprod_apply, S.fromBiprod_biprodIsoProd_inv_apply] at h
    change r x - (F.cohomologyPresheaf (n + 1)).map S.f₁₃.op (r' x) = 0 at h
    rw [hx, zero_sub, neg_eq_zero] at h
    have hx' : r' x = 0 := hHigher (h.trans (map_zero _).symm)
    have hb : S.toBiprod F (n + 1) x = 0 := by
      rw [S.toBiprod_apply]
      change (AddCommGrpCat.biprodIsoProd _ _).inv ⟨r x, r' x⟩ = 0
      rw [hx, hx']
      exact map_zero _
    have he : (S.δ F n (n + 1) rfl).hom.range = (S.toBiprod F (n + 1)).hom.ker :=
      ((S.sequence_exact F n (n + 1) rfl).exact' 2 3 4).ab_range_eq_ker
    have hxk : x ∈ (S.toBiprod F (n + 1)).hom.ker := hb
    rw [← he] at hxk
    obtain ⟨y, hy⟩ := hxk
    change S.δ F n (n + 1) rfl y = x at hy
    exact hy.symm.trans (connecting_zero y)
  intro x y h
  apply sub_eq_zero.mp
  apply zero_of_restrict
  rw [map_sub, h, sub_self]

end ManuscriptAudit.MayerVietorisRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MayerVietorisRestriction.first_restriction_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
