import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeCohomologyPullback

/-! The actual constant-coefficient pullback is natural in the coefficient group. -/

namespace ManuscriptAudit.ProetaleSchemeConstantNaturality

open AlgebraicGeometry CategoryTheory
open ProetaleInverseImage (inverseImage constantInverseImageIso)
open ProetaleSchemeCohomologyPullback (constant pullback pullback_naturality)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := constantSheaf (Scheme.ProEt.topology X) A

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {M N : A} (b : M ⟶ N)

theorem constant_natural (n : ℕ) (x : Sheaf.H ((C Y).obj M) n) :
    constant f N n (Sheaf.H.map ((C Y).map b) n x) =
      Sheaf.H.map ((C X).map b) n (constant f M n x) := by
  let q := pullback f ((C Y).obj M) n x
  let e := constantInverseImageIso f
  change Sheaf.H.map (e.app N).hom n (pullback f ((C Y).obj N) n
      (Sheaf.H.map ((C Y).map b) n x)) =
    Sheaf.H.map ((C X).map b) n (Sheaf.H.map (e.app M).hom n q)
  have hpb := pullback_naturality f ((C Y).map b) n x
  refine (congrArg (fun c ↦ Sheaf.H.map (e.app N).hom n c) hpb).trans ?_
  let g₁ := (inverseImage f).map ((C Y).map b)
  let g₂ := (C X).map b
  let e₁ := (e.app M).hom
  let e₂ := (e.app N).hom
  have h : g₁ ≫ e₂ = e₁ ≫ g₂ := e.hom.naturality b
  exact (Sheaf.H.map_comp_apply (f := g₁) (n := n) e₂ q).symm.trans
    ((congrArg (fun t ↦ Sheaf.H.map t n q) h).trans
      (Sheaf.H.map_comp_apply (f := e₁) (n := n) g₂ q))

end
end ManuscriptAudit.ProetaleSchemeConstantNaturality

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleSchemeConstantNaturality.constant_natural
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
