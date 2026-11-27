import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineSchemeWeaklyEtaleRefinement
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift

/-! A single native affine pro-étale chart lifts a countable family of sections. -/

namespace ManuscriptAudit.ProetaleCountableAffineRefinement

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} {T : X.ProEt} [IsAffine T.left]

theorem exists_common_refinement (V : ℕ → X.ProEt) (a : ∀ n, V n ⟶ T)
    (hA : ∀ n, IsAffine (V n).left) (hW : ∀ n, WeaklyEtale (a n).left)
    (hS : ∀ n, Surjective (a n).left) :
    ∃ (W : X.ProEt) (f : W ⟶ T) (h : ∀ n, W ⟶ V n),
      IsAffine W.left ∧
      Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology X T ∧
      ∀ n, h n ≫ a n = f := by
  obtain ⟨Y, g, k, hY, hg, hs, hk⟩ := AffineSchemeWeaklyEtaleRefinement.exists_refinement
    (fun n => (V n).left) (fun n => (a n).left) hA hW hS
  letI := hY
  letI := hg
  letI := hs
  let W : X.ProEt := Scheme.ProEt.mk (g ≫ T.hom)
  let f : W ⟶ T := MorphismProperty.Over.homMk g rfl
  let h (n : ℕ) : W ⟶ V n :=
    MorphismProperty.Over.homMk (k n) (by
      change k n ≫ (V n).hom = g ≫ T.hom
      rw [← MorphismProperty.Over.w (a n), ← Category.assoc, hk n])
  refine ⟨W, f, h, hY, ?_, ?_⟩
  · letI : QuasiCompact f.left := inferInstanceAs (QuasiCompact g)
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.singleton f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage T.left
    rw [Presieve.map_singleton]
    change Presieve.singleton g ∈ Scheme.propQCPrecoverage @WeaklyEtale T.left
    exact Scheme.Hom.singleton_mem_propQCPrecoverage hg
  · intro n
    apply (Scheme.ProEt.forget X ⋙ Over.forget X).map_injective
    exact hk n

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

theorem exists_simultaneous_lift (I Q : ℕ → C X) (q : ∀ n, I n ⟶ Q n)
    (hLocal : ∀ n, Sheaf.IsLocallySurjective (q n))
    (x : ∀ n, (Q n).obj.obj (op T)) :
    ∃ (W : X.ProEt) (f : W ⟶ T),
      IsAffine W.left ∧ Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology X T ∧
      ∀ n, ∃ y : (I n).obj.obj (op W),
        (q n).hom.app (op W) y = (Q n).obj.map f.op (x n) := by
  have hEach (n : ℕ) :
      ∃ (V : X.ProEt) (a : V ⟶ T),
        IsAffine V.left ∧ WeaklyEtale a.left ∧ Surjective a.left ∧
        ∃ y : (I n).obj.obj (op V), (q n).hom.app (op V) y = (Q n).obj.map a.op (x n) := by
    letI := hLocal n
    obtain ⟨V, a, hv, hw, hs, _, y, hy⟩ :=
      ProetaleAffineSingletonLift.exists_singleton_cover_lift (q n) (x n)
    exact ⟨V, a, hv, hw, hs, y, hy⟩
  choose V a hV using hEach
  obtain ⟨W, f, h, hW, hCover, hComp⟩ := exists_common_refinement V a
    (fun n => (hV n).1) (fun n => (hV n).2.1) (fun n => (hV n).2.2.1)
  refine ⟨W, f, hW, hCover, ?_⟩
  intro n
  obtain ⟨y, hy⟩ := (hV n).2.2.2
  refine ⟨(I n).obj.map (h n).op y, ?_⟩
  rw [NatTrans.naturality_apply, hy, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, hComp n]

end
end ManuscriptAudit.ProetaleCountableAffineRefinement

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleCountableAffineRefinement.exists_common_refinement,
      ``ManuscriptAudit.ProetaleCountableAffineRefinement.exists_simultaneous_lift] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
