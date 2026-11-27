import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientDerived

/-!
# Stalk support of the point-coefficient sheaf

Independent coefficient sections have support equal to the closure of
the chosen set when each coefficient is nontrivial. Accumulation points
can therefore support genuine new germs.
-/

namespace ManuscriptAudit.PointCoefficientClosureSupport

open CategoryTheory Opposite Set TopologicalSpace
open PointCoefficientSheaf ClosedSupportDetection

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]

private abbrev G := AddCommGrpCat.{0}

theorem stalk_subsingleton_outside_closure {x : X} (hx : x ∉ closure P) :
    Subsingleton (TopCat.Presheaf.stalk (C := G) (presheaf P A) x) := by
  let F := presheaf P A
  let V : Opens X := ⟨(closure P)ᶜ, isClosed_closure.isOpen_compl⟩
  apply subsingleton_of_forall_eq 0
  intro s
  obtain ⟨U, hUV, hxU, t, ht⟩ := F.exists_le_germ_eq (x := x) s (V := V) hx
  have h0 : t = 0 := by
    change t = (0 : Sections P A U)
    funext q
    have hV : q.val.val ∉ closure P := hUV q.property
    exact (hV (subset_closure q.val.property)).elim
  rw [← ht, h0, map_zero]

private def nonzeroCoefficients [∀ p : P, Nontrivial (A p)] (U : Opens X) :
    Sections P A U :=
  fun q => (exists_ne (0 : A q.val)).choose

theorem stalk_nontrivial_in_closure [∀ p : P, Nontrivial (A p)] {x : X} (hx : x ∈ closure P) :
    Nontrivial (TopCat.Presheaf.stalk (C := G) (presheaf P A) x) := by
  let F := presheaf P A
  let U : Opens X := ⊤
  let hxU : x ∈ U := Opens.mem_top x
  let t : Sections P A U := nonzeroCoefficients P A U
  refine ⟨F.germ U x hxU t, 0, ?_⟩
  intro h
  have hr : F.germ U x hxU (0 : Sections P A U) = 0 := map_zero _
  obtain ⟨W, hxW, i, j, he⟩ := F.germ_eq x hxU hxU t (0 : Sections P A U) (h.trans hr.symm)
  obtain ⟨y, hyW, hyP⟩ := (mem_closure_iff.mp hx) W W.isOpen hxW
  let p : P := ⟨y, hyP⟩
  change restrict P A i.le t = restrict P A j.le (0 : Sections P A U) at he
  have hp := congrFun he (⟨p, hyW⟩ : PointsIn P W)
  change (exists_ne (0 : A p)).choose = 0 at hp
  exact (exists_ne (0 : A p)).choose_spec hp

theorem support_eq_closure [∀ p : P, Nontrivial (A p)] :
    stalkSupport (sheaf P A) = closure P := by
  ext x
  constructor
  · intro hx
    by_contra hn
    have h := stalk_subsingleton_outside_closure P A hn
    change Nontrivial (TopCat.Presheaf.stalk (C := G) (presheaf P A) x) at hx
    exact (not_nontrivial_iff_subsingleton.mpr h) hx
  · intro hx
    change Nontrivial (TopCat.Presheaf.stalk (C := G) (presheaf P A) x)
    exact stalk_nontrivial_in_closure P A hx

end
end ManuscriptAudit.PointCoefficientClosureSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientClosureSupport.stalk_subsingleton_outside_closure,
      ``ManuscriptAudit.PointCoefficientClosureSupport.stalk_nontrivial_in_closure,
      ``ManuscriptAudit.PointCoefficientClosureSupport.support_eq_closure] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
