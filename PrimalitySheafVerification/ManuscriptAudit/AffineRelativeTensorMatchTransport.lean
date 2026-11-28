import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorLegs

/-! Translate matching identities between the actual tensor square and
the categorical coproduct in the affine algebra slice. -/

namespace ManuscriptAudit.AffineRelativeTensorMatchTransport

open CategoryTheory CategoryTheory.Limits
open AffineStageTensorCoproduct (tensorIso)
open AffineStageTensorLegs (algebraHom)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {B P Q D : Type u} [CommRing B] [CommRing P] [CommRing Q] [CommRing D]
  [Algebra B P] [Algebra B Q] [Algebra B D]

private abbrev R := CommRingCat.of B
private abbrev U (E : Type u) [CommRing E] [Algebra B E] := CommRingCat.mkUnder (R (B := B)) E

variable [HasBinaryCoproduct (U (B := B) D) (U (B := B) D)]

private abbrev e : U (B := B) (D ⊗[B] D) ≅ U (B := B) D ⨿ U (B := B) D :=
  tensorIso (R := R (B := B)) D D

/-- Send a tensor matching identity to the same categorical coproduct identity. -/
theorem to_coproduct (a : P →ₐ[B] Q) (t : Q →ₐ[B] D ⊗[B] D)
    (m : P →ₐ[B] D) (g : D →ₐ[B] D ⊗[B] D)
    (i : U (B := B) D ⟶ U (B := B) D ⨿ U (B := B) D)
    (hg : g.toUnder ≫ (e (B := B) (D := D)).hom = i)
    (h : t.comp a = g.comp m) :
    a.toUnder ≫ (t.toUnder ≫ (e (B := B) (D := D)).hom) = m.toUnder ≫ i := by
  let x := e (B := B) (D := D)
  calc
    _ = (t.comp a).toUnder ≫ x.hom := by
      rw [AlgHom.toUnder_comp, Category.assoc]
    _ = (g.comp m).toUnder ≫ x.hom :=
      congrArg (fun q : P →ₐ[B] D ⊗[B] D ↦ q.toUnder ≫ x.hom) h
    _ = m.toUnder ≫ (g.toUnder ≫ x.hom) := by
      rw [AlgHom.toUnder_comp, Category.assoc]
    _ = m.toUnder ≫ i := congrArg (fun q ↦ m.toUnder ≫ q) hg

/-- Read the underlying tensor identity from a genuine affine coproduct identity. -/
theorem from_coproduct (a : P →ₐ[B] Q)
    (t : U (B := B) Q ⟶ U (B := B) D ⨿ U (B := B) D)
    (m : P →ₐ[B] D) (g : D →ₐ[B] D ⊗[B] D)
    (i : U (B := B) D ⟶ U (B := B) D ⨿ U (B := B) D)
    (hg : g.toUnder ≫ (e (B := B) (D := D)).hom = i)
    (h : a.toUnder ≫ t = m.toUnder ≫ i) :
    (algebraHom (t ≫ (e (B := B) (D := D)).inv)).comp a = g.comp m := by
  let x := e (B := B) (D := D)
  have hi : i ≫ x.inv = g.toUnder := calc
    _ = (g.toUnder ≫ x.hom) ≫ x.inv := congrArg (fun q ↦ q ≫ x.inv) hg.symm
    _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : a.toUnder ≫ (t ≫ x.inv) = m.toUnder ≫ g.toUnder := calc
    _ = (a.toUnder ≫ t) ≫ x.inv := (Category.assoc _ _ _).symm
    _ = (m.toUnder ≫ i) ≫ x.inv := congrArg (fun q ↦ q ≫ x.inv) h
    _ = _ := by rw [Category.assoc, hi]
  apply AlgHom.ext
  intro z
  exact congrArg (fun q : U (B := B) P ⟶ U (B := B) (D ⊗[B] D) ↦ q.right z) he

end
end ManuscriptAudit.AffineRelativeTensorMatchTransport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.AffineRelativeTensorMatchTransport.to_coproduct,
      ``ManuscriptAudit.AffineRelativeTensorMatchTransport.from_coproduct] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
