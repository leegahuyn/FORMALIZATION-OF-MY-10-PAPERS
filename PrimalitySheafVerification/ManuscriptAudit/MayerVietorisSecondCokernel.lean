import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-! When the first overlap restriction vanishes, the actual Mayer–Vietoris boundary realizes the second restriction's cokernel. -/

namespace ManuscriptAudit.MayerVietorisSecondCokernel

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits ComposableArrows Opposite

noncomputable section
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)

private abbrev first := ((F.cohomologyPresheaf n).map S.f₁₂.op).hom
private abbrev second := ((F.cohomologyPresheaf n).map S.f₁₃.op).hom
private abbrev connecting := (S.δ F n (n + 1) rfl).hom

private theorem range_difference (h₀ : first S F n = 0) :
    (S.fromBiprod F n).hom.range = (second S F n).range := by
  let e := (AddCommGrpCat.biprodIsoProd (F.H' n S.X₂) (F.H' n S.X₃)).addCommGroupIsoToAddEquiv
  have hEval (x : F.H' n S.X₂) (y : F.H' n S.X₃) :
      S.fromBiprod F n (e.symm (x, y)) = -(second S F n) y := by
    change S.fromBiprod F n ((AddCommGrpCat.biprodIsoProd _ _).inv (x, y)) = _
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    change (first S F n) x - (second S F n) y = _
    rw [h₀, AddMonoidHom.zero_apply, zero_sub]
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := e.symm.surjective s
    exact ⟨-y, (map_neg (second S F n) y).trans (hEval x y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.symm (0, -y), ?_⟩
    change S.fromBiprod F n (e.symm (0, -y)) = (second S F n) y
    rw [hEval, map_neg, neg_neg]

/-- The native connecting map is the quotient by the second overlap restriction when the first
restriction is zero and the two chart groups in the next degree vanish. -/
def cokernelEquiv (h₀ : first S F n = 0)
    (hU : Subsingleton (F.H' (n + 1) S.X₂)) (hV : Subsingleton (F.H' (n + 1) S.X₃)) :
    ((F.H' n S.X₁ : Type v) ⧸ (second S F n).range) ≃+ F.H' (n + 1) S.X₄ := by
  let hExact := S.sequence_exact F n (n + 1) rfl
  have hKer : (connecting S F n).ker = (second S F n).range :=
    (hExact.exact' 1 2 3).ab_range_eq_ker.symm.trans (range_difference S F n h₀)
  have hSurj : Function.Surjective (connecting S F n) := by
    intro x
    let e := (AddCommGrpCat.biprodIsoProd (F.H' (n + 1) S.X₂)
      (F.H' (n + 1) S.X₃)).addCommGroupIsoToAddEquiv
    have hz : S.toBiprod F (n + 1) x = 0 :=
      e.injective (Prod.ext (hU.elim _ _) (hV.elim _ _))
    have h := hExact.exact' 2 3 4
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact (h x).mp hz
  rw [← hKer]
  exact QuotientAddGroup.quotientKerEquivOfSurjective (connecting S F n) hSurj

end
end ManuscriptAudit.MayerVietorisSecondCokernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MayerVietorisSecondCokernel.cokernelEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
