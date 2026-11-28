import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv

/-! Vanishing of the closed coefficient's neighboring groups yields the native
cohomology comparison in each positive successor degree. -/

namespace ManuscriptAudit.ProetaleHigherShortExactEquiv

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A
private abbrev integers (X : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

/-- The equivalence is induced by the original map of the short exact sequence. -/
def equivalence {X : Scheme.{0}} (S : ShortComplex (C X)) (h : S.ShortExact) (n : ℕ)
    (h₀ : Subsingleton (Sheaf.H S.X₃ n)) (h₁ : Subsingleton (Sheaf.H S.X₃ (n + 1))) :
    Sheaf.H S.X₁ (n + 1) ≃+ Sheaf.H S.X₂ (n + 1) := by
  refine AddEquiv.ofBijective (Sheaf.H.map S.f (n + 1)) ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    have hz : Sheaf.H.map S.f (n + 1) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz'⟩ := Ext.covariant_sequence_exact₁ (integers X) h (x - y) hz
      (show n + 1 = n + 1 by rfl)
    rw [h₀.elim z 0, Ext.zero_comp] at hz'
    exact hz'.symm
  · intro x
    exact Ext.covariant_sequence_exact₂ (integers X) h x (h₁.elim _ _)

/-- The additive equivalence has the literal induced map as its underlying function. -/
theorem equivalence_apply {X : Scheme.{0}} (S : ShortComplex (C X)) (h : S.ShortExact)
    (n : ℕ) (h₀ : Subsingleton (Sheaf.H S.X₃ n))
    (h₁ : Subsingleton (Sheaf.H S.X₃ (n + 1))) (x : Sheaf.H S.X₁ (n + 1)) :
    equivalence S h n h₀ h₁ x = Sheaf.H.map S.f (n + 1) x := rfl

end
end ManuscriptAudit.ProetaleHigherShortExactEquiv

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.ProetaleHigherShortExactEquiv.equivalence,
      ``ManuscriptAudit.ProetaleHigherShortExactEquiv.equivalence_apply] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
